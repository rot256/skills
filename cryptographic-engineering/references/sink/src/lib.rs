//! Streaming, domain-separated serialization for cryptographic operations.
//!
//! `Tagged` values serialize through an infallible [`Sink`], so hashes, MACs,
//! KDFs, and Fiat-Shamir transcripts consume the encoding without it ever
//! existing as an intermediate buffer. [`Tagged::encode`] materializes the
//! encoding only for APIs that demand a byte slice, as an exact-size boxed
//! slice that is zeroized on drop.
//!
//! postcard is illustrative: any canonical, self-delimiting serialization
//! serves. The pattern is building every cryptographic operation around
//! domain-separated types, not the particular serializer.

pub mod aead;
pub mod kdf;
pub mod kem;
pub mod mac;
pub mod secret;
pub mod sig;

pub use secret::Secret;

use serde::Serialize;
use zeroize::Zeroizing;

/// One uniform external failure per operation class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CryptoError {
    SignatureVerificationFailed,
    AuthenticationFailed,
    DecryptionFailed,
}

impl core::fmt::Display for CryptoError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            CryptoError::SignatureVerificationFailed => "signature verification failed",
            CryptoError::AuthenticationFailed => "authentication failed",
            CryptoError::DecryptionFailed => "decryption failed",
        })
    }
}

impl std::error::Error for CryptoError {}

/// Infallible byte sink; absorbing cannot fail.
///
/// Absorbing bytes into a hash, MAC, sponge, or buffer cannot fail, so the
/// trait is infallible; `std::io::Write` would force a `Result` that is a
/// lie for these consumers. Keep `std::io::Write` as a separate, genuinely
/// fallible interface for real I/O. This trait is core-compatible.
pub trait Sink {
    fn write(&mut self, bytes: &[u8]);
}

impl Sink for Vec<u8> {
    fn write(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

/// Counts bytes without storing them.
pub struct ByteCounter(pub usize);

impl Sink for ByteCounter {
    fn write(&mut self, bytes: &[u8]) {
        self.0 += bytes.len();
    }
}

/// Writes into the front of a fixed slice; panics if it runs out of space.
impl Sink for &mut [u8] {
    fn write(&mut self, bytes: &[u8]) {
        assert!(bytes.len() <= self.len(), "slice sink out of space");
        let (head, tail) = core::mem::take(self).split_at_mut(bytes.len());
        head.copy_from_slice(bytes);
        *self = tail;
    }
}

/// Sink adapter for any hash or MAC state.
pub struct Absorbing<D: digest::Update>(pub D);

impl<D: digest::Update> Sink for Absorbing<D> {
    fn write(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }
}

/// Domain-separated hash of a tagged value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Digest([u8; 32]);

impl AsRef<[u8; 32]> for Digest {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

pub fn hash<T: Tagged>(input: &T) -> Digest {
    use sha3::Digest as _;

    let mut h = Absorbing(sha3::Sha3_256::new());
    input.absorb(&mut h);
    Digest(h.0.finalize().into())
}

/// Bridge: lets postcard serialize straight into any [`Sink`].
struct IntoSink<'a, S: Sink>(&'a mut S);

impl<S: Sink> postcard::ser_flavors::Flavor for IntoSink<'_, S> {
    type Output = ();

    fn try_push(&mut self, byte: u8) -> postcard::Result<()> {
        self.0.write(&[byte]);
        Ok(())
    }

    fn try_extend(&mut self, bytes: &[u8]) -> postcard::Result<()> {
        self.0.write(bytes);
        Ok(())
    }

    fn finalize(self) -> postcard::Result<()> {
        Ok(())
    }
}

/// Serialize a plain (untagged) value to an exact-size zeroized buffer:
/// count, allocate, write.
pub(crate) fn to_boxed<T: Serialize + ?Sized>(value: &T) -> Zeroizing<Box<[u8]>> {
    let mut counter = ByteCounter(0);
    postcard::serialize_with_flavor(value, IntoSink(&mut counter))
        .expect("in-memory serialization must succeed");

    let mut out = Zeroizing::new(vec![0u8; counter.0].into_boxed_slice());
    let mut slot: &mut [u8] = &mut out;
    postcard::serialize_with_flavor(value, IntoSink(&mut slot))
        .expect("in-memory serialization must succeed");
    assert!(slot.is_empty(), "encoded length must match counted length");
    out
}

/// Canonical serialization combined with a stable purpose tag.
///
/// The encoding is the injective `(separator, value)` pair: postcard writes
/// the separator as a length-prefixed string, so distinct tagged values can
/// never collide. `Serialize` impls must be deterministic and side-effect
/// free; `encode` traverses the value twice.
pub trait Tagged: Serialize {
    const SEPARATOR: &'static str;

    /// Stream the domain-separated encoding into a sink.
    fn absorb<S: Sink>(&self, sink: &mut S)
    where
        Self: Sized,
    {
        #[derive(Serialize)]
        struct DomainTuple<'a, T: Tagged + ?Sized> {
            sep: &'a str,
            val: &'a T,
        }

        postcard::serialize_with_flavor(
            &DomainTuple {
                sep: Self::SEPARATOR,
                val: self,
            },
            IntoSink(sink),
        )
        .expect("in-memory serialization must succeed");
    }

    /// Materialize the encoding; only for APIs that demand a byte slice.
    /// Zeroized on drop.
    fn encode(&self) -> Zeroizing<Box<[u8]>>
    where
        Self: Sized,
    {
        let mut counter = ByteCounter(0);
        self.absorb(&mut counter);

        let mut out = Zeroizing::new(vec![0u8; counter.0].into_boxed_slice());
        let mut slot: &mut [u8] = &mut out;
        self.absorb(&mut slot);
        assert!(slot.is_empty(), "encoded length must match counted length");
        out
    }
}

/// Wrap a value so its serialized byte array is a multiple of `BLOCK`.
///
/// Serializes as `postcard(inner) || zero padding`, padded to the next
/// multiple of `BLOCK` (at least one block). The inner encoding is
/// self-delimiting, so deserialization stops at the logical end and accepts
/// any padding amount. The padded form is non-canonical: confine it to
/// positions covered by an authenticated envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Padded<T, const BLOCK: usize>(pub T);

impl<T: Serialize, const BLOCK: usize> Serialize for Padded<T, BLOCK> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        const { assert!(BLOCK > 0, "BLOCK must be nonzero") };

        let mut counter = ByteCounter(0);
        postcard::serialize_with_flavor(&self.0, IntoSink(&mut counter))
            .map_err(serde::ser::Error::custom)?;

        let target = counter
            .0
            .checked_next_multiple_of(BLOCK)
            .unwrap_or(counter.0)
            .max(BLOCK);

        let mut padded = Zeroizing::new(vec![0u8; target].into_boxed_slice());
        let mut slot: &mut [u8] = &mut padded;
        postcard::serialize_with_flavor(&self.0, IntoSink(&mut slot))
            .map_err(serde::ser::Error::custom)?;

        (*padded).serialize(serializer)
    }
}

impl<'de, T: serde::de::DeserializeOwned, const BLOCK: usize> serde::Deserialize<'de>
    for Padded<T, BLOCK>
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let bytes: Zeroizing<Vec<u8>> =
            Zeroizing::new(serde::Deserialize::deserialize(deserializer)?);
        postcard::from_bytes(&bytes)
            .map(Padded)
            .map_err(serde::de::Error::custom)
    }
}

impl<T: Tagged, const BLOCK: usize> Tagged for Padded<T, BLOCK> {
    const SEPARATOR: &'static str = T::SEPARATOR;
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use serde::Deserialize;

    /// Infallible CSPRNG for tests.
    pub(crate) fn rng() -> impl rand_core::CryptoRng {
        rand::rng()
    }

    #[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
    pub(crate) struct Msg {
        pub(crate) id: u32,
        pub(crate) body: Vec<u8>,
    }

    impl Tagged for Msg {
        const SEPARATOR: &'static str = "v0:test-msg";
    }

    #[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
    pub(crate) struct OtherRole {
        pub(crate) id: u32,
        pub(crate) body: Vec<u8>,
    }

    impl Tagged for OtherRole {
        const SEPARATOR: &'static str = "v0:test-other";
    }

    pub(crate) fn msg() -> Msg {
        Msg {
            id: 7,
            body: b"attack at dawn".to_vec(),
        }
    }

    #[test]
    fn encode_matches_streamed_bytes() {
        let m = msg();
        let mut streamed = Vec::new();
        m.absorb(&mut streamed);
        assert_eq!(&m.encode()[..], &streamed[..]);
    }

    #[test]
    fn encode_len_matches_counter() {
        let m = msg();
        let mut counter = ByteCounter(0);
        m.absorb(&mut counter);
        assert_eq!(m.encode().len(), counter.0);
    }

    #[test]
    fn hash_is_deterministic() {
        assert_eq!(hash(&msg()), hash(&msg()));
    }

    #[test]
    fn same_bytes_different_separator_hash_differently() {
        let a = msg();
        let b = OtherRole {
            id: 7,
            body: b"attack at dawn".to_vec(),
        };
        assert_ne!(hash(&a), hash(&b));
    }

    #[test]
    fn hash_matches_encode_of_domain_tuple() {
        use sha3::Digest as _;

        let m = msg();
        let streamed = hash(&m);
        let buffered: [u8; 32] = sha3::Sha3_256::digest(&m.encode()[..]).into();
        assert_eq!(*streamed.as_ref(), buffered);
    }

    #[test]
    #[should_panic(expected = "slice sink out of space")]
    fn slice_sink_panics_on_overflow() {
        let mut buf = [0u8; 2];
        let mut slot: &mut [u8] = &mut buf;
        slot.write(&[1, 2, 3]);
    }

    #[test]
    fn padded_roundtrip() {
        let p: Padded<Msg, 32> = Padded(msg());
        let bytes = postcard::to_allocvec(&p).unwrap();
        let back: Padded<Msg, 32> = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(p, back);
    }

    #[test]
    fn padded_len_is_block_multiple() {
        for len in [0usize, 1, 31, 32, 33, 100] {
            let p: Padded<Vec<u8>, 32> = Padded(vec![0xab; len]);
            let outer = postcard::to_allocvec(&p).unwrap();
            let inner: Vec<u8> = postcard::from_bytes(&outer).unwrap();
            assert!(inner.len() % 32 == 0 && !inner.is_empty(), "len {len}");
        }
    }

    #[test]
    fn padded_accepts_different_block_on_deserialize() {
        let p: Padded<Msg, 32> = Padded(msg());
        let bytes = postcard::to_allocvec(&p).unwrap();
        let back: Padded<Msg, 64> = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(back.0, msg());
    }
}
