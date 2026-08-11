//! Public-key encryption: a typed wrapper around HPKE (RFC 9180),
//! a reviewed construction rather than a hand-rolled hybrid.
//!
//! The wrapper adds the tagged context HPKE's byte-oriented API lacks:
//! the plaintext type, associated-data type, and associated-data value are
//! bound into HPKE's AAD input, the application/version tag into its info
//! input, and every failure collapses into one uniform decryption error.

use hpke::{
    Kem as KemTrait, OpModeR, OpModeS, aead::ChaCha20Poly1305, kdf::HkdfSha256, kem::MlKem768,
};
use rand_core::CryptoRng;
use serde::{Serialize, de::DeserializeOwned};
use zeroize::Zeroizing;

use crate::{CryptoError, Tagged, to_boxed};

/// Recipient-independent application and version identifier, bound into
/// the HPKE key schedule.
const INFO: &[u8] = b"v0:pke-hpke";

pub struct EncryptionKey(<MlKem768 as KemTrait>::PublicKey);

pub struct DecryptionKey(<MlKem768 as KemTrait>::PrivateKey);

pub struct Ciphertext {
    encapped: <MlKem768 as KemTrait>::EncappedKey,
    ct: Vec<u8>,
}

/// Binds the plaintext type, associated-data type, and associated-data
/// value into authentication.
#[derive(Serialize)]
struct PkeContext<'a, A: Tagged> {
    seps: (&'static str, &'static str),
    ad: &'a A,
}

impl<A: Tagged> Tagged for PkeContext<'_, A> {
    const SEPARATOR: &'static str = "v0:pke-context";
}

impl EncryptionKey {
    pub fn encrypt<M: Tagged, A: Tagged, R: CryptoRng>(
        &self,
        rng: &mut R,
        pt: &M,
        ad: &A,
    ) -> Ciphertext {
        let aad = PkeContext {
            seps: (M::SEPARATOR, A::SEPARATOR),
            ad,
        }
        .encode();
        let pt = to_boxed(pt);

        let (encapped, ct) = hpke::single_shot_seal_with_rng::<
            ChaCha20Poly1305,
            HkdfSha256,
            MlKem768,
        >(&OpModeS::Base, &self.0, INFO, &pt, &aad, rng)
        .expect("in-memory encryption must succeed");
        Ciphertext { encapped, ct }
    }
}

impl DecryptionKey {
    pub fn generate<R: CryptoRng>(rng: &mut R) -> Self {
        let (sk, _pk) = MlKem768::gen_keypair_with_rng(rng);
        Self(sk)
    }

    #[must_use]
    pub fn encryption_key(&self) -> EncryptionKey {
        EncryptionKey(MlKem768::sk_to_pk(&self.0))
    }

    pub fn decrypt<M: Tagged + DeserializeOwned, A: Tagged>(
        &self,
        ct: &Ciphertext,
        ad: &A,
    ) -> Result<M, CryptoError> {
        let aad = PkeContext {
            seps: (M::SEPARATOR, A::SEPARATOR),
            ad,
        }
        .encode();

        let pt = hpke::single_shot_open::<ChaCha20Poly1305, HkdfSha256, MlKem768>(
            &OpModeR::Base,
            &self.0,
            &ct.encapped,
            INFO,
            &ct.ct,
            &aad,
        )
        .map_err(|_| CryptoError::DecryptionFailed)?;
        let pt = Zeroizing::new(pt);

        let (msg, rest) =
            postcard::take_from_bytes(&pt).map_err(|_| CryptoError::DecryptionFailed)?;
        if rest.is_empty() {
            Ok(msg)
        } else {
            Err(CryptoError::DecryptionFailed)
        }
    }
}

#[cfg(test)]
#[allow(clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::tests::{Msg, OtherRole, msg, rng};
    use serde::Deserialize;

    #[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
    struct Ad {
        recipient: u64,
    }

    impl Tagged for Ad {
        const SEPARATOR: &'static str = "v0:test-pke-ad";
    }

    #[test]
    fn encrypt_decrypt_roundtrip() {
        let mut rng = rng();
        let dk = DecryptionKey::generate(&mut rng);
        let ek = dk.encryption_key();
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        let back: Msg = dk.decrypt(&ct, &Ad { recipient: 1 }).unwrap();
        assert_eq!(back, msg());
    }

    #[test]
    fn wrong_recipient_fails() {
        let mut rng = rng();
        let ek = DecryptionKey::generate(&mut rng).encryption_key();
        let other_dk = DecryptionKey::generate(&mut rng);
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        assert_eq!(
            other_dk.decrypt::<Msg, _>(&ct, &Ad { recipient: 1 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_ad_value_fails() {
        let mut rng = rng();
        let dk = DecryptionKey::generate(&mut rng);
        let ek = dk.encryption_key();
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        assert_eq!(
            dk.decrypt::<Msg, _>(&ct, &Ad { recipient: 2 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_ad_type_fails() {
        #[derive(Serialize)]
        struct AdOther {
            recipient: u64,
        }

        impl Tagged for AdOther {
            const SEPARATOR: &'static str = "v0:test-pke-ad-other";
        }

        let mut rng = rng();
        let dk = DecryptionKey::generate(&mut rng);
        let ek = dk.encryption_key();
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        assert_eq!(
            dk.decrypt::<Msg, _>(&ct, &AdOther { recipient: 1 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_plaintext_type_fails() {
        let mut rng = rng();
        let dk = DecryptionKey::generate(&mut rng);
        let ek = dk.encryption_key();
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        assert_eq!(
            dk.decrypt::<OtherRole, _>(&ct, &Ad { recipient: 1 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn any_single_byte_tamper_fails() {
        use hpke::{Deserializable, Serializable};

        let mut rng = rng();
        let dk = DecryptionKey::generate(&mut rng);
        let ek = dk.encryption_key();
        let ct = ek.encrypt(&mut rng, &msg(), &Ad { recipient: 1 });
        let encapped_bytes = ct.encapped.to_bytes();

        for i in 0..ct.ct.len() {
            let mut dem = ct.ct.clone();
            dem[i] ^= 1;
            let tampered = Ciphertext {
                encapped: <MlKem768 as KemTrait>::EncappedKey::from_bytes(&encapped_bytes).unwrap(),
                ct: dem,
            };
            assert!(
                dk.decrypt::<Msg, _>(&tampered, &Ad { recipient: 1 })
                    .is_err(),
                "dem byte {i}"
            );
        }

        for i in 0..encapped_bytes.len() {
            let mut bytes = encapped_bytes;
            bytes[i] ^= 1;
            // A mutated encapped key must either fail to decode or fail
            // to decrypt; both count as rejection.
            if let Ok(encapped) = <MlKem768 as KemTrait>::EncappedKey::from_bytes(&bytes) {
                let tampered = Ciphertext {
                    encapped,
                    ct: ct.ct.clone(),
                };
                assert!(
                    dk.decrypt::<Msg, _>(&tampered, &Ad { recipient: 1 })
                        .is_err(),
                    "encapped byte {i}"
                );
            }
        }
    }
}
