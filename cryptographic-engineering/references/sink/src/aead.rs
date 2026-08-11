//! Typed authenticated encryption: plaintext and associated data are
//! distinct tagged types, both separators are bound into authentication,
//! and every failure collapses into one uniform decryption error.

use chacha20poly1305::aead::{Aead, Payload};
use chacha20poly1305::{KeyInit, XChaCha20Poly1305, XNonce};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use zeroize::Zeroizing;

use crate::{to_boxed, CryptoError, Secret, Tagged};

pub struct Key(Secret<32>);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Ciphertext {
    nonce: [u8; 24],
    ct: Vec<u8>,
}

/// Binds the plaintext type, associated-data type, and associated-data
/// value into authentication.
#[derive(Serialize)]
struct AeadContext<'a, A: Tagged> {
    seps: (&'static str, &'static str),
    ad: &'a A,
}

impl<A: Tagged> Tagged for AeadContext<'_, A> {
    const SEPARATOR: &'static str = "v0:aead-context";
}

impl Key {
    pub fn gen<R: rand_core::CryptoRng>(rng: &mut R) -> Self {
        Self(Secret::gen(rng))
    }

    pub fn seal<M: Tagged, A: Tagged, R: rand_core::CryptoRng>(
        &self,
        rng: &mut R,
        plaintext: &M,
        associated_data: &A,
    ) -> Ciphertext {
        let mut nonce = [0u8; 24];
        rng.fill_bytes(&mut nonce);

        let aad = AeadContext {
            seps: (M::SEPARATOR, A::SEPARATOR),
            ad: associated_data,
        }
        .encode();
        let pt = to_boxed(plaintext);

        let cipher = XChaCha20Poly1305::new(self.0.as_bytes().into());
        let ct = cipher
            .encrypt(
                &XNonce::from(nonce),
                Payload {
                    msg: &pt,
                    aad: &aad,
                },
            )
            .expect("in-memory encryption must succeed");
        Ciphertext { nonce, ct }
    }

    pub fn open<M: Tagged + DeserializeOwned, A: Tagged>(
        &self,
        ciphertext: &Ciphertext,
        associated_data: &A,
    ) -> Result<M, CryptoError> {
        let aad = AeadContext {
            seps: (M::SEPARATOR, A::SEPARATOR),
            ad: associated_data,
        }
        .encode();

        let cipher = XChaCha20Poly1305::new(self.0.as_bytes().into());
        let pt = cipher
            .decrypt(
                &XNonce::from(ciphertext.nonce),
                Payload {
                    msg: &ciphertext.ct,
                    aad: &aad,
                },
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
mod tests {
    use super::*;
    use crate::tests::{msg, rng, Msg, OtherRole};

    #[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
    struct Ad {
        session: u64,
    }

    impl Tagged for Ad {
        const SEPARATOR: &'static str = "v0:test-ad";
    }

    #[derive(Serialize)]
    struct AdOther {
        session: u64,
    }

    impl Tagged for AdOther {
        const SEPARATOR: &'static str = "v0:test-ad-other";
    }

    #[test]
    fn seal_open_roundtrip() {
        let mut rng = rng();
        let key = Key::gen(&mut rng);
        let ct = key.seal(&mut rng, &msg(), &Ad { session: 1 });
        let back: Msg = key.open(&ct, &Ad { session: 1 }).unwrap();
        assert_eq!(back, msg());
    }

    #[test]
    fn wrong_ad_value_fails() {
        let mut rng = rng();
        let key = Key::gen(&mut rng);
        let ct = key.seal(&mut rng, &msg(), &Ad { session: 1 });
        assert_eq!(
            key.open::<Msg, _>(&ct, &Ad { session: 2 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_ad_type_fails() {
        let mut rng = rng();
        let key = Key::gen(&mut rng);
        let ct = key.seal(&mut rng, &msg(), &Ad { session: 1 });
        assert_eq!(
            key.open::<Msg, _>(&ct, &AdOther { session: 1 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_plaintext_type_fails() {
        let mut rng = rng();
        let key = Key::gen(&mut rng);
        let ct = key.seal(&mut rng, &msg(), &Ad { session: 1 });
        assert_eq!(
            key.open::<OtherRole, _>(&ct, &Ad { session: 1 }),
            Err(CryptoError::DecryptionFailed)
        );
    }

    #[test]
    fn wrong_key_fails() {
        let mut rng = rng();
        let key = Key::gen(&mut rng);
        let ct = key.seal(&mut rng, &msg(), &Ad { session: 1 });
        let other = Key::gen(&mut rng);
        assert!(other.open::<Msg, _>(&ct, &Ad { session: 1 }).is_err());
    }
}
