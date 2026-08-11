---
name: cryptographic-engineering
description: Design, implement, modify, and review robust cryptographic software, especially Rust code. Use for cryptographic APIs and protocols involving domain separation, transcript encoding, hashes, KDFs, AEAD, public-key encryption, signatures, commitments, proofs, secret sharing, randomness, secret-memory handling, serialization, or verification logic.
---

# Cryptographic Engineering

Treat protocol meaning as part of the type system.
Operate on semantic values rather than untyped byte strings,
bind every cryptographic operation to its purpose and context,
and make invalid states impossible to represent.

## Start from the protocol

Before editing code:

1. Identify every secret, public value, message, context, transcript, state transition, and trust boundary.
2. Record what each hash, KDF, signature, encryption, commitment, or proof must bind.
3. Separate protocol versions and algorithm versions explicitly.
4. Decide which malformed inputs must be rejected before expensive cryptography.
5. Prefer established, reviewed constructions and libraries.
   Implement a new construction only when the protocol requires it and its security argument is understood.

Do not let serialization layout, call-site convention,
or comments carry an invariant that a type or API can enforce.

## Make invalid states unrepresentable

Separate untrusted wire representations from validated cryptographic types.
Give validated types private fields and expose only fallible constructors.
Make the validated types implement `Deserialize` themselves — route the derive
through the fallible conversion with `#[serde(try_from = "...")]` or write a
manual deserializer — so every invariant is enforced during deserialization
and protocol messages declare the refined types directly in their fields.
The raw wire type stays a private implementation detail of decoding.

```rust
#[derive(serde::Deserialize)]
struct WirePoint([u8; 48]);

/// Canonically decoded, on-curve point in the required prime-order subgroup.
/// The identity point is allowed.
#[derive(serde::Deserialize)]
#[serde(try_from = "WirePoint")]
pub struct Point(ark_bls12_381::G1Affine);

/// A [`Point`] guaranteed not to be the identity.
#[derive(serde::Deserialize)]
#[serde(try_from = "Point")]
pub struct NonZeroPoint(Point);

impl TryFrom<WirePoint> for Point {
    type Error = DecodeError;
    fn try_from(wire: WirePoint) -> Result<Self, Self::Error> {
        let point = ark_bls12_381::G1Affine::deserialize_compressed(&wire.0[..])
            .map_err(|_| DecodeError::InvalidPoint)?;
        Ok(Self(point))
    }
}

impl TryFrom<Point> for NonZeroPoint {
    type Error = DecodeError;
    fn try_from(point: Point) -> Result<Self, Self::Error> {
        if point.0.is_zero() {
            Err(DecodeError::IdentityNotAllowed)
        } else {
            Ok(Self(point))
        }
    }
}

impl AsRef<Point> for NonZeroPoint {
    fn as_ref(&self) -> &Point {
        &self.0
    }
}

impl std::ops::Deref for NonZeroPoint {
    type Target = Point;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
```

Verify the exact guarantees of the library decoder.
For untrusted elliptic-curve input, require canonical field encodings, an on-curve point, and membership in the correct prime-order subgroup before constructing `Point`. When a protocol position also forbids the identity, require `NonZeroPoint`; do not make all valid points globally nonzero. Never use unchecked point deserialization merely because a later equation is expected to fail.

Build the same refinement hierarchy for scalars:

```rust
#[derive(serde::Deserialize)]
struct WireScalar([u8; 32]);

/// Canonically decoded scalar; zero is allowed.
#[derive(serde::Deserialize)]
#[serde(try_from = "WireScalar")]
pub struct Scalar(FieldElement);

/// A [`Scalar`] guaranteed not to be zero.
#[derive(serde::Deserialize)]
#[serde(try_from = "Scalar")]
pub struct NonZeroScalar(Scalar);
```

Construct `Scalar` only from a canonical field encoding, then construct `NonZeroScalar` through `TryFrom<Scalar>`. Implement immutable `AsRef<Scalar>` and `Deref<Target = Scalar>` for ergonomic use where the less-restricted type is accepted.

Use refinement to make partial operations total, for example requiring the denominator of a division to be `NonZeroScalar` so the operation can only be invoked where it is defined:

```rust
impl NonZeroScalar {
    /// Total: a nonzero scalar in a prime field is always invertible,
    /// and the inverse is itself nonzero.
    pub fn invert(&self) -> NonZeroScalar {
        NonZeroScalar(Scalar(self.0.0.inverse().expect("nonzero scalar is invertible")))
    }
}

impl std::ops::Div<&NonZeroScalar> for &Scalar {
    type Output = Scalar;

    fn div(self, denom: &NonZeroScalar) -> Scalar {
        Scalar(self.0 * denom.invert().0.0)
    }
}
```

Lagrange interpolation is the canonical instance: distinct validated share indices make every pairwise difference of evaluation points a `NonZeroScalar`, so coefficient computation cannot divide by zero.

Do not implement `AsMut`, `DerefMut`, or expose a mutable inner value: mutation could turn a refined value into an invalid one. When ownership must be relaxed, implement the infallible `From<NonZeroScalar> for Scalar` or `From<NonZeroPoint> for Point` conversion.

Apply the same pattern to:

- Nonzero scalars, secret keys, nonces, and evaluation points.
- Fixed-size keys, hashes, signatures, and identifiers.
- Thresholds, participant counts, unique participant IDs, and share indices.
- Monotonic counters, timestamps, validity intervals, and bounded collection sizes.
- Supported message and algorithm versions.
- Ordered or duplicate-free transcript collections.

Use layered refinement types such as `Point`/`NonZeroPoint` and `Scalar`/`NonZeroScalar`, as well as arrays, enums, and other validated newtypes, instead of raw vectors, integers, strings, or booleans when they encode protocol invariants. Accept the weakest type that satisfies each API's actual precondition. Validate cross-field invariants by converting an entire wire struct into one validated aggregate, not by validating fields independently and hoping the caller completes the checks.

If parsing must temporarily hold invalid data, keep it in an explicitly named private wire type. Do not expose it to cryptographic operations, application state, logs, callbacks, or persistence before successful conversion.

## Domain-separate with semantic types

Require cryptographic inputs to implement a trait that combines canonical serialization with a stable purpose tag:

```rust
pub trait Tagged: serde::Serialize {
    const SEPARATOR: &'static str;

    fn encode(&self) -> Vec<u8>
    where
        Self: Sized,
    {
        #[derive(serde::Serialize)]
        struct DomainTuple<'a, T: Tagged + ?Sized> {
            sep: &'a str,
            val: &'a T,
        }

        bincode::serde::encode_to_vec(
            &DomainTuple {
                sep: Self::SEPARATOR,
                val: self,
            },
            bincode::config::standard(),
        )
        .expect("in-memory transcript encoding must succeed")
    }
}
```

Use length-delimited structured encoding such as `(separator, value)`. Never create transcripts by concatenating variable-length fields without lengths or an equally unambiguous grammar.

Name separators by version and purpose:

```rust
impl Tagged for EmailCertificateMessage {
    const SEPARATOR: &'static str = "v0:email-cert";
}

impl Tagged for RecoveryRequestMessage {
    const SEPARATOR: &'static str = "v0:recovery-request";
}
```

Apply these rules:

- Assign a distinct separator to every semantic role, even when two types currently serialize identically.
- Include a version in every protocol-facing separator, such as `v0:<component>-<purpose>`.
- Treat a separator as immutable once data using it can persist or cross a trust boundary.
- Search the whole project for duplicates when adding a separator. The trait cannot enforce global uniqueness.
- Use zero-field marker types for KDF purposes that have no runtime context.
- Give separate stages separate tags: input hashing, proof challenges, output derivation, encryption pads, MACs, and nonces must not share a domain.

For hash-to-curve, use both a standards-compliant suite/DST and a typed encoded message. Include the application, curve/group, protocol version, and semantic purpose in the DST.

## Construct explicit transcripts

Represent every cryptographic transcript as a serializable struct with named fields. Include all values that affect authorization or interpretation.

This Schnorr signature-of-knowledge transcript binds the application message, proof commitment, and ordered commitment set:

```rust
#[derive(serde::Serialize)]
struct SokMessage<'a> {
    msg: [u8; 32],
    delta: PedersenCommitment,
    commitments: &'a [PedersenCommitment],
}

impl Tagged for SokMessage<'_> {
    const SEPARATOR: &'static str = "v0:schnorr-sok";
}
```

Do not sign or hash only the payload when its meaning also depends on an account ID, recipient, public key, counter, session ID, algorithm, or external context. Put those values in the transcript.

When a generic inner type would otherwise disappear during serialization, include its separator explicitly:

```rust
#[derive(serde::Serialize)]
struct MacTranscript<'a, 'b, A: Tagged> {
    roles: (&'static str, &'static str),
    nonce: &'a Nonce,
    ciphertext: &'a [u8],
    associated_data: &'b A,
}

let transcript = MacTranscript {
    roles: (M::SEPARATOR, A::SEPARATOR),
    nonce: &nonce,
    ciphertext: &ciphertext,
    associated_data,
};
```

Preserve ordering when ordering is semantically meaningful. Sort or canonicalize sets before encoding when it is not.

## Make encryption type-aware

Accept plaintext and associated data as distinct tagged types. Accept randomness through a cryptographically secure RNG bound rather than selecting a hidden global RNG.

```rust
fn seal<M, A, R, K>(
    rng: &mut R,
    key: &K,
    plaintext: &M,
    associated_data: &A,
) -> Ciphertext
where
    M: Tagged,
    A: Tagged,
    R: rand_core::RngCore + rand_core::CryptoRng,
    K: AsRef<Key>;

fn open<M, A, K>(
    key: &K,
    ciphertext: &Ciphertext,
    associated_data: &A,
) -> Result<M, CryptoError>
where
    M: Tagged + serde::de::DeserializeOwned,
    A: Tagged,
    K: AsRef<Key>;
```

Bind both `M::SEPARATOR` and `A::SEPARATOR` into authentication. Make decryption under the wrong plaintext type, associated-data type, or associated-data value fail with the same external error.

For hybrid public-key encryption:

1. Encapsulate with a reviewed KEM.
2. Derive the DEM key under a dedicated KEM-to-DEM KDF tag.
3. Encrypt through the same typed AEAD interface.
4. Bind recipient-independent context and algorithm/version identifiers.
5. Collapse decapsulation, authentication, and plaintext-decoding failures into one decryption failure unless the protocol explicitly requires otherwise.

Parameterize the ciphertext type with the message and context when practical. If wire compatibility requires an untyped ciphertext, require the caller to state the expected output type at decryption and authenticate that type's separator.

## Use KDFs by purpose

Give every derived key a dedicated info type. Place the derivation purpose in the KDF customization string or equivalent domain-separation input and encode the context structurally.

```rust
#[derive(serde::Serialize)]
struct BackupMetadataKeyInfo<'a> {
    commitments: &'a [ShareCommitment],
}

impl Tagged for BackupMetadataKeyInfo<'_> {
    const SEPARATOR: &'static str = "v0:backup-kdf-meta";
}
```

Do not reuse a derived key for encryption, authentication, commitments, exports, or unrelated protocol stages. Prefer independent subkeys even if their current source key and context are identical.

Treat KDF input key material as secret. Zeroize serialized IKM and intermediate buffers; a tagged info value does not automatically protect an untagged or copied IKM buffer.

## Contain and clear secrets

Centralize fixed-size secret bytes in a wrapper that zeroizes on drop, compares in constant time, and redacts debug output:

```rust
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, ZeroizeOnDrop};

#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Secret<const N: usize>([u8; N]);

impl<const N: usize> ConstantTimeEq for Secret<N> {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.0.ct_eq(&other.0)
    }
}

impl<const N: usize> PartialEq for Secret<N> {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl<const N: usize> std::fmt::Debug for Secret<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[REDACTED; {N}]")
    }
}
```

Also zeroize field elements, secret shares, polynomial coefficients, signing keys, KEM decapsulation keys, derived keys, and random masks. Enable dependency features such as `zeroize` when the underlying library provides them.

Audit the complete lifetime of secret material:

- Minimize cloning and ownership transfers.
- Wrap temporary plaintext, serialized IKM, seeds, and decrypted byte buffers in `Zeroizing` or zeroize them explicitly.
- Ensure temporary Serde wire structs holding raw key bytes also zeroize on drop.
- Avoid conversions that move a secret into an ordinary array or `Vec<u8>` without transferring the zeroization obligation.
- Do not derive `Debug`, `Display`, `Hash`, or `Serialize` for secret types unless required and reviewed. Make secret serialization an explicit capability.
- Remember that zeroization does not prevent swapping, compiler-created copies, allocator copies, or side channels. Minimize exposure even when using `ZeroizeOnDrop`.

Use constant-time equality and selection only for secret-dependent comparisons. Do not claim an entire routine is constant-time merely because its final comparison is.

## Compare cryptographic values in constant time

Use `subtle` instead of handwritten comparison loops. Give each fixed-size cryptographic value its own newtype so its equality and role are enforced by the type:

```rust
use subtle::ConstantTimeEq;

#[derive(Clone, serde::Serialize, serde::Deserialize)]
struct Mac(Secret<32>);

impl ConstantTimeEq for Mac {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.0.ct_eq(&other.0)
    }
}

impl PartialEq for Mac {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for Mac {}
```

Do not use `type Mac = Secret<32>` or derive `PartialEq`: an alias permits accidental interchange with keys and nonces, while derived byte-array equality may exit early. Construct the expected tag as a `Mac` and compare the two `Mac` values; return one uniform authentication/decryption failure on mismatch.

Keep compared encodings fixed-size so length does not become part of a secret-dependent comparison. Preserve `subtle::Choice` through secret-dependent selection with `ConditionallySelectable` or `CtOption` where practical; convert to `bool` only at a deliberate public control-flow boundary. Review the whole operation for secret-dependent branches, indexing, table lookup, allocation, and early returns—constant-time equality alone does not make surrounding code constant-time.

Use dedicated newtypes for keys, nonces, tags, commitments, and identifiers even when their byte lengths match. Test semantic equality and mismatches at the first, middle, and last byte, but do not claim unit tests prove timing behavior; rely on reviewed primitives and code inspection.

## Sign and verify typed messages

Expose signature operations only over tagged messages:

```rust
impl VerificationKey {
    pub fn verify<T: Tagged>(
        &self,
        signature: &Signature,
        message: &T,
    ) -> Result<(), CryptoError> {
        self.0
            .verify_strict(&message.encode(), &signature.0)
            .map_err(|_| CryptoError::SignatureVerificationFailed)
    }
}
```

Use strict verification offered by the library. Match signature and verification-key algorithm versions explicitly. Return a uniform external failure instead of leaking parser or equation details.

Reconstruct the expected signed object from trusted context and parsed fields. This envelope prevents replaying a guardian share in another position or session:

```rust
#[derive(serde::Serialize)]
struct SignedEncryptedShare<'a> {
    ciphertext: &'a Ciphertext,
    index: u32,
    session_id: SessionId,
}

impl Tagged for SignedEncryptedShare<'_> {
    const SEPARATOR: &'static str = "v0:signed-encrypted-share";
}

verification_key.verify(
    &share.signature,
    &SignedEncryptedShare {
        ciphertext: &share.ciphertext,
        index: share.index,
        session_id: expected_session_id,
    },
)?;
```

Before accepting signed state:

1. Parse with bounded, canonical decoding.
2. Enforce structural bounds and supported versions.
3. Reconstruct the complete expected transcript.
4. Verify the signature or proof.
5. Enforce identity bindings, monotonic counters, freshness, authorization, and state-transition rules.
6. Return or persist the authenticated value only after all checks succeed.

For signed batches, sign the complete inner envelope and verify it before releasing any decrypted item. If ciphertext position or recipient membership is sensitive, avoid early-exit searches; process the full fixed/bounded collection and select results without secret-dependent control flow where feasible.

## Version messages explicitly

Represent every long-lived or cross-boundary message as one closed, data-carrying enum. The variant is the version and carries exactly that version's payload:

```rust
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum AccountState {
    V0(AccountStateV0),
    V1(AccountStateV1),
}
```

Serialize and deserialize `AccountState` itself. The canonical enum encoding includes the variant discriminant followed by the selected payload, so deserialization produces `AccountState::V0(value)` or `AccountState::V1(value)` directly. Do not expose a separate version field, a parallel fieldless version enum, or a raw integer/string tag for callers to dispatch themselves.

If the serializer's derived enum representation is part of the stable protocol, freeze its exact encoding and variant order. If explicit numeric assignments or gaps are required, generate the enum's serialization from one declaration rather than maintaining a second version type, for example with a macro of this form:

```rust
versioned_enum!(
    #[derive(Clone, Debug)]
    AccountState,
    V0(AccountStateV0) = 0,
    V1(AccountStateV1) = 1,
);
```

The generated public type is still the single `AccountState` enum. Its wire encoding contains the assigned variant number and payload, and its deserializer returns the corresponding data-carrying variant or rejects an unknown variant.

Apply these evolution rules:

- Freeze a released version's field order, field types, defaults, canonical encoding, and cryptographic tags.
- Add a new payload type and a fresh numeric tag for an incompatible change. Never silently reinterpret `V0` bytes as `V1`.
- Never renumber or reuse a released tag. Keep removed versions as tombstones unless permanently losing read compatibility is intentional.
- Append derived enum variants; never reorder them. With explicit assignments, keep the assigned values immutable.
- Match the data-carrying enum exhaustively. Reject unknown versions unless the protocol deliberately specifies opaque forwarding.
- Keep the numeric wire tag and semantic separator version aligned but distinct: the wire tag selects a schema; the separator binds the cryptographic purpose.
- Authenticate the version. Either sign/MAC the outer versioned encoding or sign a concrete payload under a version-specific separator that cannot be confused with another version.
- Prevent downgrade attacks by checking allowed versions as part of authenticated protocol policy, not by accepting the first version that parses.
- Convert old messages to a current internal model only through explicit, fallible upgrade functions. Preserve the original authenticated bytes or version until verification is complete.
- Version algorithms separately from application messages when they can evolve independently.

Test exact serialized bytes, not only round trips. Confirm that a new reader accepts every supported old variant, an old reader rejects new variants cleanly, unknown/reserved tags fail, removed tags behave intentionally, and changing the tag changes every signature, MAC, hash, or ciphertext transcript that must bind it.

## Separate cryptographic encoding from transport encoding

Use one stable canonical encoding for cryptographic transcripts and a separately reviewed transport layer. Do not assume JSON object ordering or a language-specific debug representation is canonical.

For all untrusted serialized input—binary or text:

- Limit raw bytes or characters before parsing, and bound strings, collections, nesting, and recursion during decoding.
- Bound decompressed output before parsing compressed input.
- Consume exactly one complete value. Reject trailing binary bytes and extra text documents or tokens.
- Define and enforce duplicate-field, unknown-field, missing-field, and default-value policies.
- Validate numeric ranges, lengths, counts, identifiers, and cross-field invariants before allocation or cryptographic work.
- Reject unknown versions unless forward compatibility is explicitly designed.
- Use fixed-size encodings for fixed-size secrets, keys, signatures, scalars, and group elements.
- Use canonical, checked deserialization for curve points and field elements.
- Test exact encoded sizes for persisted formats.
- Keep version tags in long-lived wire types.

Decode textual formats into typed structs. Do not navigate security-sensitive input through generic JSON values or maps unless the schema is genuinely dynamic. If JSON, Base64, hexadecimal, or another text wrapper can represent the same value multiple ways, canonicalize to the protocol's binary form before hashing or signing; never sign a convenient textual rendering.

Use a transport wrapper such as URL-safe unpadded Base64 only after canonical binary serialization. Do not confuse text encoding with cryptographic domain separation.

## Padding

When ciphertext length leaks sensitive structure, pad the serialized plaintext into documented buckets before encryption. Make bucketing a reusable wrapper type instead of ad hoc call-site logic:

```rust
/// Serializes as `bincode(inner) || zero padding`, padded to the next
/// multiple of `BLOCK` (at least one block). The inner encoding is
/// self-delimiting, so deserialization stops at the logical end and
/// accepts any padding amount, letting `BLOCK` evolve without breaking
/// persisted data.
#[derive(Clone)]
pub struct Padded<T, const BLOCK: usize>(T);

// BINCODE_CONFIG: bincode::config::standard().with_limit::<MAX_BYTES>()
impl<T: serde::Serialize, const BLOCK: usize> serde::Serialize for Padded<T, BLOCK> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut bytes = bincode::serde::encode_to_vec(&self.0, BINCODE_CONFIG)
            .map_err(serde::ser::Error::custom)?;
        let target = bytes
            .len()
            .checked_next_multiple_of(BLOCK)
            .unwrap_or(bytes.len())
            .max(BLOCK);
        bytes.resize(target, 0);
        bytes.serialize(serializer)
    }
}

impl<'de, T: serde::de::DeserializeOwned, const BLOCK: usize> serde::Deserialize<'de>
    for Padded<T, BLOCK>
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = serde::Deserialize::deserialize(deserializer)?;
        let (inner, _consumed) = bincode::serde::decode_from_slice(&bytes, BINCODE_CONFIG)
            .map_err(serde::de::Error::custom)?;
        Ok(Padded(inner))
    }
}

impl<T: Tagged, const BLOCK: usize> Tagged for Padded<T, BLOCK> {
    const SEPARATOR: &'static str = T::SEPARATOR;
}
```

Padding is representation, not meaning: `Padded<T, BLOCK>` keeps `T`'s separator, and the padding-tolerant deserializer is what allows the bucket size to change over time.

## Validate adversarially

Write positive tests, but prioritize failures that demonstrate binding and non-confusion:

- Decrypting identical serialized data as a different tagged type fails.
- Changing the associated-data type or value fails.
- Changing every signed transcript field individually fails.
- Wrong key, recipient, session, counter, version, ordering, or algorithm fails.
- Missing, duplicated, reordered, or extra proof/commitment elements fail as specified.
- Empty inputs and threshold boundaries behave intentionally.
- Truncated, oversized, trailing, non-canonical, and invalid-group encodings fail.
- Serialization round-trips and exact wire sizes remain stable.
- Secret-sharing and interpolation properties hold over randomized valid and invalid cases.
- Batch processing does not reveal the successful position through an early exit when that position is sensitive.

Use known-answer and cross-implementation vectors for standardized primitives. Use property tests for algebraic relations and state-machine transitions. Do not use round-trip tests alone as evidence of cryptographic correctness.

## Final review checklist

Before finishing a cryptographic change, confirm:

- Invalid encodings and unchecked primitives cannot inhabit validated protocol types.
- Every operation has a unique, versioned purpose tag.
- Every transcript is structured, canonical, and binds all interpretation-relevant context.
- Encryption authenticates both plaintext and associated-data types.
- Every derived key has a single purpose.
- Secrets, copies, and temporary buffers have explicit destruction behavior.
- Secret values and authentication tags use dedicated newtypes with `subtle`-based constant-time comparison.
- Signature and proof verification use reconstructed typed messages and strict library APIs.
- Messages deserialize directly into one closed, data-carrying version enum with stable encoding and exhaustive dispatch.
- Untrusted decoding is bounded, canonical, and rejects trailing data.
- Verification failures do not become distinguishable oracles.
- Secret-dependent branches, indexing, lookup, and early exits have been reviewed.
- Negative tests cover type confusion, context confusion, replay, mutation, and malformed encodings.
