//! Message authentication over tagged messages. The tag is a dedicated
//! newtype compared in constant time; verification returns one uniform
//! failure.

use digest::KeyInit as _;
use hmac::Mac as _;

use crate::{Absorbing, CryptoError, Secret, Tagged};

type HmacSha3 = hmac::Hmac<sha3::Sha3_256>;

pub struct MacKey(Secret<32>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mac(Secret<32>);

impl MacKey {
    pub fn gen<R: rand_core::CryptoRng>(rng: &mut R) -> Self {
        Self(Secret::gen(rng))
    }

    pub fn mac<T: Tagged>(&self, msg: &T) -> Mac {
        let state = HmacSha3::new_from_slice(self.0.as_bytes()).expect("any key length is valid");
        let mut sink = Absorbing(state);
        msg.absorb(&mut sink);
        Mac(Secret::init(|buf| {
            buf.copy_from_slice(&sink.0.finalize().into_bytes())
        }))
    }

    pub fn check<T: Tagged>(&self, tag: &Mac, msg: &T) -> Result<(), CryptoError> {
        if self.mac(msg) == *tag {
            Ok(())
        } else {
            Err(CryptoError::AuthenticationFailed)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{msg, rng, Msg, OtherRole};

    #[test]
    fn mac_check_roundtrip() {
        let key = MacKey::gen(&mut rng());
        let tag = key.mac(&msg());
        assert!(key.check(&tag, &msg()).is_ok());
    }

    #[test]
    fn wrong_message_fails() {
        let key = MacKey::gen(&mut rng());
        let tag = key.mac(&msg());
        let other = Msg {
            id: 8,
            body: b"attack at dusk".to_vec(),
        };
        assert_eq!(
            key.check(&tag, &other),
            Err(CryptoError::AuthenticationFailed)
        );
    }

    #[test]
    fn wrong_key_fails() {
        let key = MacKey::gen(&mut rng());
        let tag = key.mac(&msg());
        let other = MacKey::gen(&mut rng());
        assert!(other.check(&tag, &msg()).is_err());
    }

    #[test]
    fn same_bytes_different_type_fails() {
        let key = MacKey::gen(&mut rng());
        let tag = key.mac(&msg());
        let confused = OtherRole {
            id: 7,
            body: b"attack at dawn".to_vec(),
        };
        assert!(key.check(&tag, &confused).is_err());
    }
}
