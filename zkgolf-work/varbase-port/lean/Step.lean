import Solution.Secp256k1ScalarMul.Lazy.StepValues
import Solution.Secp256k1ScalarMul.Lazy.MuxVec

/-!
# One lazy variable-base chain step: `R' = 2R + T = (R + T) + R`

The accumulator `R` is carried lazily (eight signed radix-`2^32` coefficients
per coordinate, never normalised); the table point `T` is canonical.  Two
slope witnesses with balanced digits (patchgravity's `Sparse32Normalize`,
d59c8bf7), nine sparse products, four zero-row certificates, and boolean
flags for the two cancellation branches.  `T = ∞` is delegated to the global
special-scalar fallback (`sp`); `R = ∞` is handled by an output mux.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost
open Solution.Secp256k1ScalarMul.Lazy
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Specs.ShortWeierstrass Specs.Secp256k1

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-! ### Value-level views and honest witnesses -/

def rx (i : Inputs Field) : Fp := valZ (zwords i.acc.x)
def ry (i : Inputs Field) : Fp := valZ (zwords i.acc.y)
def tX (i : Inputs Field) : Fp := decodeFe i.t.x
def tY (i : Inputs Field) : Fp := decodeFe i.t.y

/-- Honest first slope: chord of `(R, T)`, tangent when `T = R`, and `0` on the
branches where no relation is certified. -/
noncomputable def slope1 (i : Inputs Field) : Fp :=
  if i.acc.isInf = 1 then 0
  else if tX i = rx i then (if tY i = -ry i then 0 else 3 * rx i ^ 2 / (2 * ry i))
  else (tY i - ry i) / (tX i - rx i)

def cflagV (i : Inputs Field) : Field :=
  if i.acc.isInf = 0 ∧ rx i = tX i ∧ ry i = -tY i then 1 else 0

noncomputable def xSV (i : Inputs Field) : Fp := slope1 i * slope1 i - rx i - tX i

noncomputable def zflagV (i : Inputs Field) : Field :=
  if i.acc.isInf = 0 ∧ cflagV i = 0 ∧ xSV i = rx i then 1 else 0

/-- Honest second slope from the two-slope identity. -/
noncomputable def slope2 (i : Inputs Field) : Fp :=
  if xSV i = rx i then 0 else 2 * ry i / (rx i - xSV i) - slope1 i

noncomputable def lam1W (i : Inputs Field) : Emu Field := slopeWitness (slope1 i)
noncomputable def lam2W (i : Inputs Field) : Emu Field := slopeWitness (slope2 i)
noncomputable def flagsW (i : Inputs Field) : fields 2 Field := #v[cflagV i, zflagV i]

def zeroVec : Var (fields 8) Field := Vector.ofFn fun _ => (0 : Expression Field)

/-! ### Circuit -/

noncomputable def main (n : ℕ) (hn : n + 1 ≤ depth) (i : Var Inputs Field) :
    Circuit Field (Var LazyPt Field) := do
  let lam1 ← ProvableType.witness (α := Emu) fun env => lam1W (eval env i)
  let a ← Sparse32Normalize.circuit lam1
  let lam2 ← ProvableType.witness (α := Emu) fun env => lam2W (eval env i)
  let b ← Sparse32Normalize.circuit lam2
  let fl ← ProvableType.witness (α := fields 2) fun env => flagsW (eval env i)
  let c := fl[0]
  let z := fl[1]
  Circuit.assertZero (c * (1 - c))
  Circuit.assertZero (z * (1 - z))
  Circuit.assertZero (c * z)
  Circuit.assertZero (i.acc.isInf * c)
  Circuit.assertZero (i.acc.isInf * z)
  Circuit.assertZero ((1 - i.sp) * i.t.isInf)
  let g ← subcircuit MulCell.circuit ⟨1 - i.sp, 1 - i.acc.isInf⟩
  let p ← subcircuit Products.circuit ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y⟩
  assertion (Certs.circuit n (Nat.le_of_succ_le hn)) ⟨a, b, i.acc.x, i.acc.y, i.t.x, i.t.y, p, g, c, z⟩
  let rt ← subcircuit MulCell.circuit ⟨i.acc.isInf, i.t.isInf⟩
  let zrt ← subcircuit MulCell.circuit ⟨z, rt⟩
  let zOut := z + rt - zrt
  let xP := Products.vaddE (Products.vsubE p.sb p.sa) (embedExpr i.t.x)
  let yP := Products.vsubE p.pb i.acc.y
  let xw ← subcircuit MuxVec.circuit ⟨c, xP, i.acc.x⟩
  let xv ← subcircuit MuxVec.circuit ⟨i.acc.isInf, xw, embedExpr i.t.x⟩
  let xo ← subcircuit MuxVec.circuit ⟨zOut, xv, zeroVec⟩
  let yw ← subcircuit MuxVec.circuit ⟨c, yP, i.acc.y⟩
  let yv ← subcircuit MuxVec.circuit ⟨i.acc.isInf, yw, embedExpr i.t.y⟩
  let yo ← subcircuit MuxVec.circuit ⟨zOut, yv, zeroVec⟩
  return { x := xo, y := yo, isInf := zOut }

noncomputable instance elaborated (n : ℕ) (hn : n + 1 ≤ depth) :
    ElaboratedCircuit Field Inputs LazyPt (main n hn) := by
  elaborate_circuit

attribute [local irreducible] Sparse32Mul.outputExpr Sparse32Square.outputExpr

lemma eval_zeroVec (env : Environment Field) (k : Fin 8) :
    (Vector.map (Expression.eval env) zeroVec)[k.val] = 0 := by
  simp only [zeroVec, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]

theorem soundness (n : ℕ) (hn : n + 1 ≤ depth) :
    Soundness Field (main n hn) (Assumptions n) (Spec n) := by
  circuit_proof_start_core
  subst h_input
  simp +arith only [main, Sparse32Normalize.circuit, Sparse32Normalize.Assumptions,
    Sparse32Normalize.Spec, MulCell.circuit, MulCell.Assumptions, MulCell.Spec,
    Products.circuit, Products.Assumptions, Certs.circuit, MuxVec.circuit, MuxVec.Assumptions,
    MuxVec.Spec, circuit_norm, numLimbs, Nat.reduceAdd] at h_holds h_assumptions ⊢
  obtain ⟨hn1, hn2, z1, z2, z3, z4, z5, z6, hg, hp, hcert, hrt, hzrt, m1, m2, m3, m4, m5, m6⟩ :=
    h_holds
  simp only [Products.map_vaddE, Products.map_vsubE, Products.map_embedExpr] at m1 m2 m4 m5
  exact step_values n hn (hA := h_assumptions) (ha := hn1) (hb := hn2)
    (hc := by linear_combination z1) (hz := by linear_combination z2) (hcz := z3)
    (hic := z4) (hiz := z5) (hspt := by linear_combination z6) (hg := by linear_combination hg)
    (hp := hp) (hcert := hcert) (hrt := hrt) (hzrt := hzrt) (hzo := by ring)
    (hzv := eval_zeroVec env) (hxw := m1) (hxv := m2) (hxo := m3) (hyw := m4) (hyv := m5)
    (hyo := m6)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Step
