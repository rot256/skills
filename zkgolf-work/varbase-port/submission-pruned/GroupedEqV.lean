import Solution.Secp256k1ScalarMul.GroupedEq

namespace Solution.Secp256k1ScalarMul

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace GroupedEqV

open GroupedEq (sum_extend_zero)

structure VParams where
  
  Nf : ℕ → ℕ
  
  OFFf : ℕ → ℕ
  
  Wf : ℕ → ℕ
  
  Nmax : ℕ
  
  OFFmax : ℕ
  
  Wmax : ℕ

end GroupedEqV

end

end Solution.Secp256k1ScalarMul
