//! Signing over tagged messages: ed25519 with strict verification and a
//! uniform external failure.

use ed25519_dalek::Signer as _;
use rand_core::CryptoRng;
use zeroize::Zeroizing;

use crate::{CryptoError, Tagged};

pub struct SigningKey(ed25519_dalek::SigningKey);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationKey(ed25519_dalek::VerifyingKey);

#[derive(Clone, Debug)]
pub struct Signature(ed25519_dalek::Signature);

impl SigningKey {
    pub fn generate<R: CryptoRng>(rng: &mut R) -> Self {
        let mut seed = Zeroizing::new([0u8; 32]);
        rng.fill_bytes(&mut *seed);
        Self(ed25519_dalek::SigningKey::from_bytes(&seed))
    }

    pub fn sign<T: Tagged>(&self, msg: &T) -> Signature {
        Signature(self.0.sign(&msg.encode()))
    }

    #[must_use]
    pub fn verification_key(&self) -> VerificationKey {
        VerificationKey(self.0.verifying_key())
    }
}

impl VerificationKey {
    pub fn verify<T: Tagged>(&self, sig: &Signature, msg: &T) -> Result<(), CryptoError> {
        self.0
            .verify_strict(&msg.encode(), &sig.0)
            .map_err(|_| CryptoError::SignatureVerificationFailed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{Msg, OtherRole, msg, rng};

    #[test]
    fn sign_verify_roundtrip() {
        let sk = SigningKey::generate(&mut rng());
        let sig = sk.sign(&msg());
        assert!(sk.verification_key().verify(&sig, &msg()).is_ok());
    }

    #[test]
    fn wrong_message_fails() {
        let sk = SigningKey::generate(&mut rng());
        let sig = sk.sign(&msg());
        let other = Msg {
            id: 8,
            body: b"attack at dusk".to_vec(),
        };
        assert_eq!(
            sk.verification_key().verify(&sig, &other),
            Err(CryptoError::SignatureVerificationFailed)
        );
    }

    #[test]
    fn wrong_key_fails() {
        let sk = SigningKey::generate(&mut rng());
        let sig = sk.sign(&msg());
        let other = SigningKey::generate(&mut rng());
        assert!(other.verification_key().verify(&sig, &msg()).is_err());
    }

    #[test]
    fn same_bytes_different_type_fails() {
        let sk = SigningKey::generate(&mut rng());
        let sig = sk.sign(&msg());
        let confused = OtherRole {
            id: 7,
            body: b"attack at dawn".to_vec(),
        };
        assert!(sk.verification_key().verify(&sig, &confused).is_err());
    }
}
