//! Purpose-bound key derivation: every derived key has a dedicated tagged
//! info type, and the output is filled in place inside its zeroizing
//! container.

use crate::{Secret, Tagged};

/// Derive a purpose-bound subkey from input key material.
pub fn kdf<T: Tagged, const N: usize>(ikm: &Secret<32>, info: &T) -> Secret<N> {
    let hk = hkdf::Hkdf::<sha3::Sha3_256>::new(None, ikm.as_bytes());
    Secret::init(|buf| {
        hk.expand(&info.encode(), buf)
            .expect("output length is valid for HKDF")
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{msg, rng, OtherRole};

    #[test]
    fn deterministic() {
        let ikm = Secret::gen(&mut rng());
        let a: Secret<32> = kdf(&ikm, &msg());
        let b: Secret<32> = kdf(&ikm, &msg());
        assert_eq!(a, b);
    }

    #[test]
    fn same_bytes_different_info_type_differ() {
        let ikm = Secret::gen(&mut rng());
        let a: Secret<32> = kdf(&ikm, &msg());
        let b: Secret<32> = kdf(
            &ikm,
            &OtherRole {
                id: 7,
                body: b"attack at dawn".to_vec(),
            },
        );
        assert_ne!(a, b);
    }

    #[test]
    fn different_ikm_differ() {
        let a: Secret<32> = kdf(&Secret::gen(&mut rng()), &msg());
        let b: Secret<32> = kdf(&Secret::gen(&mut rng()), &msg());
        assert_ne!(a, b);
    }
}
