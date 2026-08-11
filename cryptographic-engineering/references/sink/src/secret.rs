//! Fixed-size secret bytes: zeroized on drop, constant-time comparison,
//! redacted debug output.

use rand_core::CryptoRng;
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, ZeroizeOnDrop};

#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Secret<const N: usize>([u8; N]);

impl<const N: usize> Secret<N> {
    pub fn generate<R: CryptoRng>(rng: &mut R) -> Self {
        let mut s = Self([0u8; N]);
        rng.fill_bytes(&mut s.0);
        s
    }

    /// Construct by filling the buffer in place, avoiding an
    /// unzeroized temporary holding the secret.
    pub fn init(fill: impl FnOnce(&mut [u8; N])) -> Self {
        let mut s = Self([0u8; N]);
        fill(&mut s.0);
        s
    }

    pub(crate) fn as_bytes(&self) -> &[u8; N] {
        &self.0
    }
}

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

impl<const N: usize> Eq for Secret<N> {}

impl<const N: usize> core::fmt::Debug for Secret<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[REDACTED; {N}]")
    }
}
