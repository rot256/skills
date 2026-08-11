//! Context-bound key encapsulation over ML-KEM.
//!
//! Standardized KEMs take no associated data: encapsulation consumes only
//! the encapsulation key and decapsulation only the ciphertext. The wrapper
//! adds the missing context binding by deriving the output secret from the
//! raw shared secret under a tagged context that also binds the
//! encapsulation key and ciphertext, compensating for the varying binding
//! guarantees of the underlying KEM.

use ml_kem::{Decapsulate as _, Encapsulate as _, Kem as _, KeyExport as _, MlKem768};
use serde::Serialize;

use crate::{kdf::kdf, Secret, Tagged};

pub struct EncapsulationKey(ml_kem::EncapsulationKey<MlKem768>);

pub struct DecapsulationKey(ml_kem::DecapsulationKey<MlKem768>);

pub struct KemCiphertext(ml_kem::kem::Ciphertext<MlKem768>);

#[derive(Debug, PartialEq, Eq)]
pub struct SharedSecret(Secret<32>);

/// Binds the encapsulation key, ciphertext, and caller context into the
/// derived secret; the context's own separator travels with its value.
#[derive(Serialize)]
struct KemContext<'a, C: Tagged> {
    ek: &'a [u8],
    ct: &'a [u8],
    ctx: (&'static str, &'a C),
}

impl<C: Tagged> Tagged for KemContext<'_, C> {
    const SEPARATOR: &'static str = "v0:kem-context";
}

fn derive<C: Tagged>(
    raw: &[u8],
    ek: &ml_kem::EncapsulationKey<MlKem768>,
    ct: &ml_kem::kem::Ciphertext<MlKem768>,
    context: &C,
) -> SharedSecret {
    let ikm = Secret::init(|buf| buf.copy_from_slice(raw));
    let ek_bytes = ek.to_bytes();
    SharedSecret(kdf(
        &ikm,
        &KemContext {
            ek: ek_bytes.as_slice(),
            ct: ct.as_slice(),
            ctx: (C::SEPARATOR, context),
        },
    ))
}

pub fn gen<R: rand_core::CryptoRng>(rng: &mut R) -> (DecapsulationKey, EncapsulationKey) {
    let (dk, ek) = MlKem768::generate_keypair_from_rng(rng);
    (DecapsulationKey(dk), EncapsulationKey(ek))
}

impl EncapsulationKey {
    pub fn encaps<C: Tagged, R: rand_core::CryptoRng>(
        &self,
        rng: &mut R,
        context: &C,
    ) -> (SharedSecret, KemCiphertext) {
        let (ct, raw) = self.0.encapsulate_with_rng(rng);
        let ss = derive(raw.as_slice(), &self.0, &ct, context);
        (ss, KemCiphertext(ct))
    }
}

impl DecapsulationKey {
    /// ML-KEM decapsulation is implicit-rejection: a mismatched ciphertext
    /// yields a pseudorandom secret rather than an error, so a mismatch
    /// surfaces as one uniform failure at first use of the derived secret.
    /// Fallibility lives at the wire decode of [`KemCiphertext`].
    pub fn decaps<C: Tagged>(&self, ciphertext: &KemCiphertext, context: &C) -> SharedSecret {
        let raw = self.0.decapsulate(&ciphertext.0);
        derive(
            raw.as_slice(),
            self.0.encapsulation_key(),
            &ciphertext.0,
            context,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{msg, rng, OtherRole};

    #[test]
    fn encaps_decaps_agree() {
        let mut rng = rng();
        let (dk, ek) = gen(&mut rng);
        let (ss_send, ct) = ek.encaps(&mut rng, &msg());
        assert_eq!(ss_send, dk.decaps(&ct, &msg()));
    }

    #[test]
    fn different_context_value_differs() {
        let mut rng = rng();
        let (dk, ek) = gen(&mut rng);
        let (ss_send, ct) = ek.encaps(&mut rng, &msg());
        let mut other = msg();
        other.id = 8;
        assert_ne!(ss_send, dk.decaps(&ct, &other));
    }

    #[test]
    fn same_bytes_different_context_type_differs() {
        let mut rng = rng();
        let (dk, ek) = gen(&mut rng);
        let (ss_send, ct) = ek.encaps(&mut rng, &msg());
        let confused = OtherRole {
            id: 7,
            body: b"attack at dawn".to_vec(),
        };
        assert_ne!(ss_send, dk.decaps(&ct, &confused));
    }

    #[test]
    fn tampered_ciphertext_yields_different_secret() {
        let mut rng = rng();
        let (dk, ek) = gen(&mut rng);
        let (ss_send, mut ct) = ek.encaps(&mut rng, &msg());
        ct.0[0] ^= 1;
        assert_ne!(ss_send, dk.decaps(&ct, &msg()));
    }
}
