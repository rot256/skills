import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ParamsD3
import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.CompleteAddTheorems

/-!
# `L=8` grouped-carry schedule for the doubly×triply-unreduced certificate (`W2` family)

Schedule for the `MulModTargetW2` certificate: the LHS carries `a·b` with `a`
doubly unreduced (limbs `< 2·2^64`, value `< 2p`) and `b` triply unreduced
(limbs `< 3·2^64`, value `< 3p`), coefficient cap `6·(m+1)·2^(2B) = 30·2^128`;
the RHS carries `q·n + target` with a 9-cell quotient (4 limbs + three-bit
top `qh ≤ 5`), keeping the `(m+1)·2^(2B) = 5·2^128` cap. Same paid-group
partition `[2,2,2]` as the `D3` family; the three offset carries widen from
69 to 70 bits.

Also home of `Fe.ValidW2`, the doubly-unreduced field-element predicate
produced by the fused-step `mulA` mux (`λ₁ + w` as a limbwise sum), and the
two-vector limbwise-sum decode lemmas.
-/

namespace Solution.Secp256k1ScalarMul

/-- Doubly-unreduced emulated field element: limbs `< 2^65`, value `< 2p`. -/
def Fe.ValidW2 (x : Emu (F circomPrime)) : Prop :=
  (∀ i : Fin numLimbs, (x[i.val]'i.isLt).val < 2 ^ (limbBits + 1)) ∧
    BigInt.value limbBits x < 2 * P256

/-- Limb-only version of `Fe.ValidW2`: the limbs are `< 2^65`, with no bound on
the represented value.  This is all the doubly-unreduced multiplier needs, and
it is what a sum of two merely *normalized* elements satisfies. -/
def Fe.NormW2 (x : Emu (F circomPrime)) : Prop :=
  ∀ i : Fin numLimbs, (x[i.val]'i.isLt).val < 2 ^ (limbBits + 1)

lemma Fe.normW2_of_validW2 {x : Emu (F circomPrime)} (h : Fe.ValidW2 x) : Fe.NormW2 x := h.1

lemma Fe.normW2_of_normalized {x : Emu (F circomPrime)}
    (h : BigInt.Normalized limbBits x) : Fe.NormW2 x := by
  intro i
  have h1 := h i
  have h2 : (2:ℕ) ^ limbBits ≤ 2 ^ (limbBits + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Fin.getElem_fin] at h1
  omega

/-- A canonical element is in particular doubly unreduced. -/
lemma Fe.validW2_of_valid {x : Emu (F circomPrime)} (h : Fe.Valid x) : Fe.ValidW2 x := by
  refine ⟨fun i => ?_, ?_⟩
  · have := h.1 i
    rw [Fin.getElem_fin] at this
    have hle : (2:ℕ) ^ limbBits ≤ 2 ^ (limbBits + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have := h.2
    have := CompleteAdd.P256_pos
    omega

/-- LHS coefficient cap for the `2×`-by-`3×` unreduced product:
`6·(m+1)·2^(2B) = 30·2^128` dominates the `< 24·2^128` wide product. -/
def nfMulW2 (_ : ℕ) : ℕ := 30 * 2 ^ 128

/-- RHS coefficient cap: unchanged `(m+1)·2^(2B) = 5·2^128` (the three-bit top
quotient contributes `< 6·2^64` per position, absorbed by the `(m+1)` slack). -/
def nfrMulW2 (_ : ℕ) : ℕ := 5 * 2 ^ 128

/-- LHS offset schedule (`30·2^64 + 29`, then `30·2^64 + 30`). -/
def offMulW2 (k : ℕ) : ℕ :=
  if k = 0 then 553402322211286548509 else 553402322211286548510

/-- RHS offset schedule (`5·2^64 + 4`, then `5·2^64 + 5`). -/
def offrMulW2 (k : ℕ) : ℕ :=
  if k = 0 then 92233720368547758084 else 92233720368547758085

def wfMulW2 (_ : ℕ) : ℕ := 70

def vMulW2 : GroupedEqV.VParams where
  Nf := nfMulW2
  OFFf := offMulW2
  Wf := wfMulW2
  Nmax := 0
  OFFmax := 0
  Wmax := 70

def vrMulW2 : GroupedEqV.VParams where
  Nf := nfrMulW2
  OFFf := offrMulW2
  Wf := wfMulW2
  Nmax := 0
  OFFmax := 0
  Wmax := 70

private lemma hgv_pos : ∀ k, posOfMulD3 (k + 1) = posOfMulD3 k + gfMulD3 k := by
  intro k; simp only [posOfMulD3, gfMulD3]; split_ifs <;> omega

private lemma hgv_gf : ∀ k, 0 < gfMulD3 k := by
  intro k; simp only [gfMulD3]; split_ifs <;> omega

private lemma hgv_w : ∀ k, 0 < vMulW2.Wf k ∧ 2 ^ vMulW2.Wf k < circomPrime := by
  intro k
  simp only [vMulW2, wfMulW2]
  exact ⟨by norm_num, by decide⟩

private lemma hgv_nf : ∀ j, 0 < vMulW2.Nf j ∧ 0 < vrMulW2.Nf j := by
  intro j
  simp only [vMulW2, vrMulW2, nfMulW2, nfrMulW2]
  exact ⟨by norm_num, by norm_num⟩

theorem hgvMulW2 :
    GroupedEqXV.GVXHyps circomPrime 8 64 gfMulD3 posOfMulD3 5 vMulW2 vrMulW2 := by
  refine ⟨rfl, hgv_pos, hgv_gf, hgv_w, hgv_nf, ?_, by norm_num,
    by simp only [vMulW2, vrMulW2, wfMulW2, nfMulW2, nfrMulW2, offMulW2, offrMulW2,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
    by simp only [vMulW2, vrMulW2, wfMulW2, nfMulW2, nfrMulW2, offMulW2, offrMulW2,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
    by simp only [vMulW2, vrMulW2, wfMulW2, nfMulW2, nfrMulW2, offMulW2, offrMulW2,
         gfMulD3, posOfMulD3, circomPrime,
         Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
       norm_num [Finset.sum_range_succ, Finset.sum_range_zero]⟩
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    · refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;>
        · simp only [vMulW2, vrMulW2, wfMulW2, nfMulW2, nfrMulW2, offMulW2, offrMulW2,
            gfMulD3, posOfMulD3, circomPrime,
            Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/-- The LHS grouped cap is six times the `(m+1)·2^(2B)` bound. -/
theorem hNfMulW2 : ∀ j, vMulW2.Nf j = 6 * ((numLimbs + 1) * 2 ^ (2 * secpParams.B)) :=
  fun _ => rfl

/-- The RHS grouped cap keeps the `(m+1)·2^(2B)` bound. -/
theorem hNfrMulW2 : ∀ j, vrMulW2.Nf j = (numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl

/-! ## Limbwise two-vector sums (`λ₁ + w` as an expression vector) -/

lemma value_sum2_two (u v : Emu (F circomPrime))
    (hu : u.Normalized limbBits) (hv : v.Normalized limbBits) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + v[k.val]'k.isLt)
      = BigInt.value limbBits u + BigInt.value limbBits v := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, BigInt.value_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  have hu' : (u[k.val]'k.isLt).val < 2 ^ limbBits := hu k
  have hv' : (v[k.val]'k.isLt).val < 2 ^ limbBits := hv k
  rw [limb_sum2_val hu' hv']
  ring

lemma decodeFe_sum2_two (u v : Emu (F circomPrime))
    (hu : u.Normalized limbBits) (hv : v.Normalized limbBits) :
    decodeFe (Vector.ofFn fun k : Fin numLimbs => u[k.val]'k.isLt + v[k.val]'k.isLt)
      = decodeFe u + decodeFe v := by
  show ((BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
      u[k.val]'k.isLt + v[k.val]'k.isLt) : ℕ) : Specs.Secp256k1.Fp) = _
  rw [value_sum2_two u v hu hv]
  push_cast
  rfl

/-- The limbwise sum of two normalized elements has limbs `< 2^65`. -/
lemma fe_normW2_sum2_two (u v : Emu (F circomPrime))
    (hu : BigInt.Normalized limbBits u) (hv : BigInt.Normalized limbBits v) :
    Fe.NormW2 (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + v[k.val]'k.isLt) := by
  intro i
  rw [Vector.getElem_ofFn]
  exact limb_sum2_lt (hu i) (hv i)

/-- The limbwise sum of two canonical elements is doubly unreduced. -/
lemma fe_validW2_sum2_two (u v : Emu (F circomPrime))
    (hu : Fe.Valid u) (hv : Fe.Valid v) :
    Fe.ValidW2 (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + v[k.val]'k.isLt) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [Vector.getElem_ofFn]
    exact limb_sum2_lt (hu.1 i) (hv.1 i)
  · rw [value_sum2_two u v hu.1 hv.1]
    have h1 := hu.2
    have h2 := hv.2
    omega

/-- Evaluation of a limbwise two-vector sum of expression vectors. -/
lemma map_eval_sum2_two (env : Environment (F circomPrime))
    (uv vv : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun k : Fin numLimbs => uv[k.val]'k.isLt + vv[k.val]'k.isLt)
      = Vector.ofFn fun k : Fin numLimbs =>
          (Vector.map (Expression.eval env) uv)[k.val]'k.isLt
          + (Vector.map (Expression.eval env) vv)[k.val]'k.isLt := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rfl

end Solution.Secp256k1ScalarMul
