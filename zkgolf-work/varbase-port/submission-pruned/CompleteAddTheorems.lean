import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.Theorems
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
import Mathlib.Tactic.LinearCombination

namespace Solution.Secp256k1ScalarMul
namespace CompleteAdd

lemma P256_pos : 0 < P256 := by decide

lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

lemma fe_valid_emuOfNat {v : ℕ} (hv : v < P256) : Fe.Valid (emuOfNat v) :=
  ⟨emuOfNat_normalized v, by rw [value_emuOfNat (lt_trans hv P256_lt)]; exact hv⟩

lemma decodeFe_emuOfNat_val (v : Specs.Secp256k1.Fp) :
    decodeFe (emuOfNat v.val) = v := by
  rw [decodeFe, value_emuOfNat (lt_trans (ZMod.val_lt v) P256_lt), ZMod.natCast_zmod_val]

lemma split3_sub {t a b c : Specs.Secp256k1.Fp} (h : t = a - b - c) :
    ∃ g : Emu (F circomPrime), decodeFe g = a - b ∧ t = decodeFe g - c :=
  ⟨emuOfNat ((a - b).val), decodeFe_emuOfNat_val _,
    by rw [decodeFe_emuOfNat_val]; exact h⟩

lemma split_mulsub {t u v x y : Specs.Secp256k1.Fp} (h : t = u * v - x - y) :
    ∃ g : Emu (F circomPrime), decodeFe g = u * v ∧ t = decodeFe g - x - y :=
  ⟨emuOfNat ((u * v).val), decodeFe_emuOfNat_val _,
    by rw [decodeFe_emuOfNat_val]; exact h⟩

lemma split_mulsub1 {t u v x : Specs.Secp256k1.Fp} (h : t = u * v - x) :
    ∃ g : Emu (F circomPrime), decodeFe g = u * v ∧ t = decodeFe g - x :=
  ⟨emuOfNat ((u * v).val), decodeFe_emuOfNat_val _,
    by rw [decodeFe_emuOfNat_val]; exact h⟩

lemma limb_sum3_val {u v w : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) (hw : w.val < 2 ^ limbBits) :
    (u + v + w).val = u.val + v.val + w.val := by
  have hwrap : 2 ^ limbBits + 2 ^ limbBits + 2 ^ limbBits < circomPrime := by decide
  have h1 : (u + v).val = u.val + v.val := ZMod.val_add_of_lt (by omega)
  rw [ZMod.val_add_of_lt (by rw [h1]; omega), h1]

lemma limb_sum3_lt {u v w : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) (hw : w.val < 2 ^ limbBits) :
    (u + v + w).val < 3 * 2 ^ limbBits := by
  rw [limb_sum3_val hu hv hw]
  omega

lemma value_sum3 (u v w : Emu (F circomPrime))
    (hu : u.Normalized limbBits) (hv : v.Normalized limbBits) (hw : w.Normalized limbBits) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + v[k.val]'k.isLt + w[k.val]'k.isLt)
      = BigInt.value limbBits u + BigInt.value limbBits v + BigInt.value limbBits w := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, BigInt.value_eq_sum, BigInt.value_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  have hu' : (u[k.val]'k.isLt).val < 2 ^ limbBits := hu k
  have hv' : (v[k.val]'k.isLt).val < 2 ^ limbBits := hv k
  have hw' : (w[k.val]'k.isLt).val < 2 ^ limbBits := hw k
  rw [limb_sum3_val hu' hv' hw']
  ring

lemma twoPBorrowDigit_ge (k : ℕ) : 2 ^ limbBits ≤ twoPBorrowDigit k := by
  unfold twoPBorrowDigit; split <;> decide

lemma twoPBorrowDigit_lt (k : ℕ) : twoPBorrowDigit k < 2 ^ 65 := by
  unfold twoPBorrowDigit; split <;> decide

lemma twoPBorrowDigit_sum :
    (∑ k ∈ Finset.range numLimbs, twoPBorrowDigit k * 2 ^ (limbBits * k)) = 2 * P256 := by
  simp only [numLimbs, Finset.sum_range_succ, Finset.sum_range_zero, twoPBorrowDigit]
  decide

lemma limb_borrow_val {q p : F circomPrime} (k : ℕ)
    (hq : q.val < 2 ^ limbBits) (hp : p.val < 2 ^ limbBits) :
    (q + (((twoPBorrowDigit k : ℕ) : F circomPrime) - p)).val
      = q.val + (twoPBorrowDigit k - p.val) := by
  have hDlt : twoPBorrowDigit k < circomPrime :=
    lt_trans (twoPBorrowDigit_lt k) (by decide)
  have hDval : ((twoPBorrowDigit k : ℕ) : F circomPrime).val = twoPBorrowDigit k :=
    ZMod.val_natCast_of_lt hDlt
  have hple : p.val ≤ ((twoPBorrowDigit k : ℕ) : F circomPrime).val := by
    rw [hDval]
    have := twoPBorrowDigit_ge k
    omega
  have hsub : ((((twoPBorrowDigit k : ℕ) : F circomPrime)) - p).val
      = twoPBorrowDigit k - p.val := by
    rw [ZMod.val_sub hple, hDval]
  rw [ZMod.val_add_of_lt, hsub]
  rw [hsub]
  have hD := twoPBorrowDigit_lt k
  have hbig : (2 : ℕ) ^ limbBits + 2 ^ 65 < circomPrime := by decide
  omega

lemma limb_borrow_lt {q p : F circomPrime} (k : ℕ)
    (hq : q.val < 2 ^ limbBits) (hp : p.val < 2 ^ limbBits) :
    (q + (((twoPBorrowDigit k : ℕ) : F circomPrime) - p)).val < 3 * 2 ^ limbBits := by
  rw [limb_borrow_val k hq hp]
  have hD := twoPBorrowDigit_lt k
  have h65 : (2 : ℕ) ^ 65 = 2 * 2 ^ limbBits := by decide
  omega

lemma value_borrow (qy py : Emu (F circomPrime))
    (hqy : qy.Normalized limbBits) (hpy : py.Normalized limbBits) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        qy[k.val]'k.isLt + (((twoPBorrowDigit k.val : ℕ) : F circomPrime) - py[k.val]'k.isLt))
      = BigInt.value limbBits qy + 2 * P256 - BigInt.value limbBits py := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, BigInt.value_eq_sum]
  have hterm : ∀ k : Fin numLimbs,
      ((Vector.ofFn fun k : Fin numLimbs =>
          qy[k.val]'k.isLt + (((twoPBorrowDigit k.val : ℕ) : F circomPrime)
            - py[k.val]'k.isLt))[k]).val * 2 ^ (limbBits * k.val)
        = (qy[k]).val * 2 ^ (limbBits * k.val)
          + (twoPBorrowDigit k.val * 2 ^ (limbBits * k.val)
            - (py[k]).val * 2 ^ (limbBits * k.val)) := by
    intro k
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
    have hq : (qy[k.val]'k.isLt).val < 2 ^ limbBits := hqy k
    have hp : (py[k.val]'k.isLt).val < 2 ^ limbBits := hpy k
    rw [limb_borrow_val k.val hq hp]
    have hle := twoPBorrowDigit_ge k.val
    have : (twoPBorrowDigit k.val - (py[k.val]'k.isLt).val) * 2 ^ (limbBits * k.val)
        = twoPBorrowDigit k.val * 2 ^ (limbBits * k.val)
          - (py[k.val]'k.isLt).val * 2 ^ (limbBits * k.val) := by
      rw [Nat.sub_mul]
    rw [Nat.add_mul, this]
    rfl
  simp only [hterm]
  rw [Finset.sum_add_distrib]
  have hple : ∀ x : Fin numLimbs, (py[x]).val * 2 ^ (limbBits * x.val)
      ≤ twoPBorrowDigit x.val * 2 ^ (limbBits * x.val) := fun x =>
    Nat.mul_le_mul_right _ (le_trans (le_of_lt (hpy x)) (twoPBorrowDigit_ge x.val))
  have hDsum : (∑ x : Fin numLimbs, twoPBorrowDigit x.val * 2 ^ (limbBits * x.val))
      = 2 * P256 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => twoPBorrowDigit k * 2 ^ (limbBits * k))]
    exact twoPBorrowDigit_sum
  rw [Finset.sum_tsub_distrib Finset.univ (fun x _ => hple x), hDsum]
  have hpy_le : (∑ x : Fin numLimbs, (py[x]).val * 2 ^ (limbBits * x.val)) ≤ 2 * P256 := by
    rw [← hDsum]
    exact Finset.sum_le_sum fun x _ => hple x
  omega

lemma value_borrow_lt (qy py : Emu (F circomPrime))
    (hqy : Fe.Valid qy) (hpy : Fe.Valid py) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        qy[k.val]'k.isLt + (((twoPBorrowDigit k.val : ℕ) : F circomPrime) - py[k.val]'k.isLt))
      < 3 * P256 := by
  rw [value_borrow qy py hqy.1 hpy.1]
  have := hqy.2
  omega

lemma decodeFe_borrow (qy py : Emu (F circomPrime))
    (hqy : qy.Normalized limbBits) (hpy : Fe.Valid py) :
    decodeFe (Vector.ofFn fun k : Fin numLimbs =>
        qy[k.val]'k.isLt + (((twoPBorrowDigit k.val : ℕ) : F circomPrime) - py[k.val]'k.isLt))
      = decodeFe qy - decodeFe py := by
  show ((BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
      qy[k.val]'k.isLt + (((twoPBorrowDigit k.val : ℕ) : F circomPrime)
        - py[k.val]'k.isLt)) : ℕ) : Specs.Secp256k1.Fp) = _
  rw [value_borrow qy py hqy hpy.1,
    Nat.cast_sub (by have := hpy.2; omega)]
  push_cast
  have h2p : ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 := ZMod.natCast_self _
  rw [h2p]
  ring_nf
  rfl

lemma map_eval_sum3 (env : Environment (F circomPrime)) (u : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env) (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt + u[k.val]'k.isLt)
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env) u)[k.val]
          + (Vector.map (Expression.eval env) u)[k.val]
          + (Vector.map (Expression.eval env) u)[k.val]) := by
  apply Vector.ext
  intro j hj
  simp [Vector.getElem_map, Vector.getElem_ofFn]
  rfl

lemma map_eval_borrow (env : Environment (F circomPrime)) (qy py : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env) (Vector.ofFn fun k : Fin numLimbs =>
        qy[k.val]'k.isLt
          + ((((twoPBorrowDigit k.val : ℕ) : F circomPrime) : Expression (F circomPrime))
            - py[k.val]'k.isLt))
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env) qy)[k.val]
          + (((twoPBorrowDigit k.val : ℕ) : F circomPrime)
            - (Vector.map (Expression.eval env) py)[k.val])) := by
  apply Vector.ext
  intro j hj
  simp [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn]
  ring

lemma map_eval_rawdiff (env : Environment (F circomPrime)) (qx px : Var Emu (F circomPrime)) :
    Vector.map (Expression.eval env) (Vector.ofFn fun k : Fin numLimbs =>
        qx[k.val]'k.isLt - px[k.val]'k.isLt)
      = Vector.ofFn (fun k : Fin numLimbs =>
        (Vector.map (Expression.eval env) qx)[k.val]
          - (Vector.map (Expression.eval env) px)[k.val]) := by
  apply Vector.ext
  intro j hj
  simp [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn]
  ring

/-- The raw limbwise difference of two canonical field elements has `BigInt.value`
zero exactly when the two elements decode equal.  Used to derive the `sameX` flag
directly from the unreduced coordinate differences (no `SubMod`). -/
lemma rawdiff_value_zero_iff (qxv pxv : Emu (F circomPrime))
    (hq : Fe.Valid qxv) (hp : Fe.Valid pxv) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        qxv[k.val]'k.isLt - pxv[k.val]'k.isLt) = 0
      ↔ decodeFe qxv = decodeFe pxv := by
  rw [BigInt.value_eq_zero_iff]
  constructor
  · intro h
    have hqp : qxv = pxv := by
      apply Vector.ext
      intro i hi
      have hc := h ⟨i, hi⟩
      rw [Fin.getElem_fin, Vector.getElem_ofFn] at hc
      exact sub_eq_zero.mp hc
    rw [hqp]
  · intro hdec i
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
    have hcast : ((BigInt.value limbBits qxv : ℕ) : Specs.Secp256k1.Fp)
        = ((BigInt.value limbBits pxv : ℕ) : Specs.Secp256k1.Fp) := hdec
    have hmod : BigInt.value limbBits qxv % P256 = BigInt.value limbBits pxv % P256 :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    rw [Nat.mod_eq_of_lt hq.2, Nat.mod_eq_of_lt hp.2] at hmod
    have hqp : qxv = pxv := BigInt.value_inj hq.1 hp.1 hmod
    rw [hqp, sub_self]

lemma cast_of_target3_mod {rv s1v s2v av bv : ℕ}
    (h : (rv + s1v + s2v) % P256 = av * bv % P256) :
    (rv : Specs.Secp256k1.Fp)
      = (av : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp)
        - (s1v : Specs.Secp256k1.Fp) - (s2v : Specs.Secp256k1.Fp) := by
  have hcast : ((rv + s1v + s2v : ℕ) : Specs.Secp256k1.Fp)
      = ((av * bv : ℕ) : Specs.Secp256k1.Fp) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hcast
  linear_combination hcast

lemma witness_cert_sub2 (av bv s1v s2v : ℕ) :
    ((((av : ℕ) : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp)
        - (s1v : Specs.Secp256k1.Fp) - (s2v : Specs.Secp256k1.Fp)).val + s1v + s2v) % P256
      = av * bv % P256 := by
  set x := ((av : ℕ) : Specs.Secp256k1.Fp) * (bv : Specs.Secp256k1.Fp)
      - (s1v : Specs.Secp256k1.Fp) - (s2v : Specs.Secp256k1.Fp) with hx
  have h1 : ((x.val + s1v + s2v : ℕ) : Specs.Secp256k1.Fp)
      = ((av * bv : ℕ) : Specs.Secp256k1.Fp) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rw [hx]; ring
  calc (x.val + s1v + s2v) % P256
      = (((x.val + s1v + s2v : ℕ) : Specs.Secp256k1.Fp)).val := by rw [ZMod.val_natCast]
    _ = (((av * bv : ℕ) : Specs.Secp256k1.Fp)).val := by rw [h1]
    _ = av * bv % P256 := by rw [ZMod.val_natCast]

lemma eval_emuConst_getElem (env : Environment (F circomPrime)) (v k : ℕ)
    (hk : k < numLimbs) :
    Expression.eval env ((emuConst v)[k]'hk) = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuConst]
  rw [Vector.getElem_ofFn]
  rfl

lemma eval_emuConst (env : Environment (F circomPrime)) (v : ℕ) :
    Vector.map (Expression.eval env) (emuConst v) = emuOfNat v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_emuConst_getElem env v k hk, emuOfNat_getElem v k hk]

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [pConst, eval_emuConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [pConst, eval_emuConst]
  exact value_emuOfNat P256_lt

lemma fe_valid_eval_zeroConst (env : Environment (F circomPrime)) :
    Fe.Valid (Vector.map (Expression.eval env) zeroConst) := by
  rw [zeroConst, eval_emuConst]
  exact fe_valid_emuOfNat P256_pos

lemma two_ne_zero_fp : (2 : Specs.Secp256k1.Fp) ≠ 0 := by
  have h2 : ((2 : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : P256 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 < P256 := by decide
    omega
  simpa using h2

lemma eq_or_eq_neg_of_sq_eq {K : Type} [Field K] {a b : K} (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -b := by
  have hz : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hz with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

theorem chord_oncurve {K : Type} [Field K] {x₁ y₁ x₂ y₂ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (h₂ : y₂ ^ 2 = x₂ ^ 3 + bb)
    (hne : x₂ - x₁ ≠ 0) (hs : s * (x₂ - x₁) = y₂ - y₁)
    (hx₃ : x₃ = s * s - x₁ - x₂) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  apply mul_left_cancel₀ hne
  linear_combination ((x₂ - x₁) - (s * s - x₁ - x₂ - x₁)) * h₁
    + (s * s - x₁ - x₂ - x₁) * h₂
    + (s * s - x₁ - x₂ - x₁) * (y₁ + y₂ + s * (x₂ - x₁)) * hs

theorem tangent_oncurve {K : Type} [Field K] {x₁ y₁ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (hs : s * (2 * y₁) = 3 * x₁ ^ 2)
    (hx₃ : x₃ = s * s - x₁ - x₁) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  linear_combination h₁ + (s * s - x₁ - x₁ - x₁) * hs

open Specs.ShortWeierstrass in
lemma add_inf_left (q : GroupPoint Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve .infinity q = q := rfl

open Specs.ShortWeierstrass in
lemma add_inf_right (p : Point Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine p) .infinity = .affine p := rfl

open Specs.ShortWeierstrass in
lemma add_affine (px py qx qy : Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine ⟨px, py⟩) (.affine ⟨qx, qy⟩)
      = if px = qx then
          (if py = -qy then .infinity
            else .affine (tangent Specs.Secp256k1.curve ⟨px, py⟩))
        else .affine (chord ⟨px, py⟩ ⟨qx, qy⟩) := rfl

open Specs.ShortWeierstrass in

lemma onCurve_iff (p : Point Specs.Secp256k1.Fp) :
    OnCurve Specs.Secp256k1.curve p ↔ p.y ^ 2 = p.x ^ 3 + 7 := by
  simp [OnCurve, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in

lemma tangent_eq (px py : Specs.Secp256k1.Fp) :
    tangent Specs.Secp256k1.curve ⟨px, py⟩
      = { x := (3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px,
          y := 3 * px ^ 2 / (2 * py)
            * (px - ((3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px)) - py } := by
  simp [tangent, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in

lemma chord_eq (px py qx qy : Specs.Secp256k1.Fp) :
    chord ⟨px, py⟩ ⟨qx, qy⟩
      = { x := ((qy - py) / (qx - px)) ^ 2 - px - qx,
          y := (qy - py) / (qx - px)
            * (px - (((qy - py) / (qx - px)) ^ 2 - px - qx)) - py } := rfl

lemma decodePoint_of_isInf {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 1) :
    decodePoint p = .infinity := by
  simp only [decodePoint]
  rw [if_pos h]

lemma decodePoint_of_finite {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 0) :
    decodePoint p = .affine { x := decodeFe p.x, y := decodeFe p.y } := by
  simp only [decodePoint]
  rw [if_neg (by rw [h]; exact zero_ne_one)]

lemma decodePoint_mk_zero (x y : Emu (F circomPrime)) :
    decodePoint ⟨x, y, 0⟩ = .affine { x := decodeFe x, y := decodeFe y } :=
  decodePoint_of_finite rfl

lemma isBool_ite {c : Prop} [Decidable c] :
    IsBool (if c then (1 : F circomPrime) else 0) := by
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma fe_valid_ite {c : Prop} [Decidable c] {a b : Emu (F circomPrime)}
    (ha : Fe.Valid a) (hb : Fe.Valid b) : Fe.Valid (if c then a else b) := by
  split <;> assumption

lemma isBool_of_eq_ite {x : F circomPrime} {c : Prop} [Decidable c]
    (h : x = if c then (1 : F circomPrime) else 0) : IsBool x := by
  rw [h]; exact isBool_ite

lemma fe_valid_of_eq_ite {x : Emu (F circomPrime)} {c : Prop} [Decidable c]
    {a b : Emu (F circomPrime)} (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h : x = if c then a else b) : Fe.Valid x := by
  rw [h]; exact fe_valid_ite ha hb

open Specs.ShortWeierstrass in
theorem soundness_core
    {P Q s1 s2 out infv finv : FlaggedPoint (F circomPrime)}
    {dxv dyv syv x1sqv x1sq2v tNumv tDenv numv denv lamv lamSqv xsv x3v xdv yprodv y3v
      : Emu (F circomPrime)}
    {sameX oppY cancel : F circomPrime}
    (hP : P.Valid) (hQ : Q.Valid)
    (hdx : decodeFe dxv = decodeFe Q.x - decodeFe P.x)
    (hdy : decodeFe dyv = decodeFe Q.y - decodeFe P.y)
    (hsameX : sameX = if decodeFe dxv = 0 then 1 else 0)
    (hsy : decodeFe syv = decodeFe P.y + decodeFe Q.y)
    (hoppY : oppY = if decodeFe syv = 0 then 1 else 0)
    (hx1sq : decodeFe x1sqv = decodeFe P.x * decodeFe P.x)
    (hx1sq2 : decodeFe x1sq2v = decodeFe x1sqv + decodeFe x1sqv)
    (htNum : decodeFe tNumv = decodeFe x1sq2v + decodeFe x1sqv)
    (htDen : decodeFe tDenv = decodeFe P.y + decodeFe P.y)
    (hnum : numv = if sameX = 1 then tNumv else dyv)
    (hden : denv = if sameX = 1 then tDenv else dxv)
    (hlam : decodeFe denv ≠ 0 → decodeFe lamv * decodeFe denv = decodeFe numv)
    (hlamSq : decodeFe lamSqv = decodeFe lamv * decodeFe lamv)
    (hxs : decodeFe xsv = decodeFe lamSqv - decodeFe P.x)
    (hx3v : Fe.Valid x3v) (hx3 : decodeFe x3v = decodeFe xsv - decodeFe Q.x)
    (hxd : decodeFe xdv = decodeFe P.x - decodeFe x3v)
    (hyprod : decodeFe yprodv = decodeFe lamv * decodeFe xdv)
    (hy3v : Fe.Valid y3v) (hy3 : decodeFe y3v = decodeFe yprodv - decodeFe P.y)
    (hcancel : Q.isInf = 0 → cancel = sameX * oppY)
    (hinfx : Fe.Valid infv.x) (hinfy : Fe.Valid infv.y) (hinff : infv.isInf = 1)
    (hfin : finv = ⟨x3v, y3v, 0⟩)
    (hs1 : s1 = if cancel = 1 then infv else finv)
    (hs2 : s2 = if Q.isInf = 1 then P else s1)
    (hout : out = if P.isInf = 1 then Q else s2) :
    out.Valid ∧
      decodePoint out =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint Q) := by
  rcases hP.1 with hPinf | hPinf
  · -- P is finite
    have hPne1 : P.isInf ≠ 1 := by rw [hPinf]; exact zero_ne_one
    rw [hout, if_neg hPne1]
    rcases hQ.1 with hQinf | hQinf
    · -- Q is finite too: the generic affine case analysis
      have hQne1 : Q.isInf ≠ 1 := by rw [hQinf]; exact zero_ne_one
      rw [hs2, if_neg hQne1, decodePoint_of_finite hPinf, decodePoint_of_finite hQinf,
        add_affine]
      have hPc : decodeFe P.y ^ 2 = decodeFe P.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hP.2.2.2 hPinf)
      have hQc : decodeFe Q.y ^ 2 = decodeFe Q.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hQ.2.2.2 hQinf)
      by_cases hxx : decodeFe Q.x = decodeFe P.x
      · -- equal x-coordinates
        have hsx : sameX = 1 := by rw [hsameX, hdx, if_pos (by rw [hxx, sub_self])]
        rw [if_pos hxx.symm]
        by_cases hyy : decodeFe P.y + decodeFe Q.y = 0
        · -- opposite y: cancellation, the output is 𝒪
          have hoy : oppY = 1 := by rw [hoppY, hsy, if_pos hyy]
          have hc1 : cancel = 1 := by rw [hcancel hQinf, hsx, hoy, one_mul]
          rw [hs1, if_pos hc1, if_pos (eq_neg_of_add_eq_zero_left hyy),
            decodePoint_of_isInf hinff]
          exact ⟨⟨Or.inr hinff, hinfx, hinfy,
            fun h0 => absurd (hinff.symm.trans h0) one_ne_zero⟩, rfl⟩
        · -- same y ≠ 0: doubling by the tangent rule
          have hoy : oppY = 0 := by rw [hoppY, hsy, if_neg hyy]
          have hc0 : cancel = 0 := by rw [hcancel hQinf, hoy, mul_zero]
          rw [hs1, if_neg (by rw [hc0]; exact zero_ne_one), hfin,
            if_neg (fun h => hyy (by rw [h]; ring))]
          -- both points coincide, with nonzero y-coordinate
          have hqy : decodeFe Q.y = decodeFe P.y := by
            rcases eq_or_eq_neg_of_sq_eq (show decodeFe Q.y ^ 2 = decodeFe P.y ^ 2 by
              rw [hQc, hPc, hxx]) with h | h
            · exact h
            · exact absurd (by rw [h]; ring) hyy
          have hpy0 : decodeFe P.y ≠ 0 := by
            intro h0
            exact hyy (by rw [hqy, h0, add_zero])
          have h2py : decodeFe P.y + decodeFe P.y ≠ 0 := by
            rw [← two_mul]
            exact mul_ne_zero two_ne_zero_fp hpy0
          have hdenv : decodeFe denv = decodeFe P.y + decodeFe P.y := by
            rw [hden, if_pos hsx, htDen]
          have hlam' : decodeFe lamv * (decodeFe P.y + decodeFe P.y)
              = decodeFe P.x * decodeFe P.x + decodeFe P.x * decodeFe P.x
                + decodeFe P.x * decodeFe P.x := by
            have h := hlam (by rw [hdenv]; exact h2py)
            rw [hdenv] at h
            rw [h, hnum, if_pos hsx, htNum, hx1sq2, hx1sq]
          have hslope : decodeFe lamv = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y) := by
            rw [eq_div_iff (by rw [two_mul]; exact h2py)]
            linear_combination hlam'
          have hX : decodeFe x3v
              = (3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x := by
            rw [hx3, hxs, hlamSq, hslope, hxx]; ring
          have hY : decodeFe y3v
              = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)
                * (decodeFe P.x
                  - ((3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x))
                - decodeFe P.y := by
            rw [hy3, hyprod, hxd, hslope, hX]
          refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
          · rw [onCurve_iff]
            exact tangent_oncurve (s := decodeFe lamv) hPc (by linear_combination hlam')
              (by rw [hx3, hxs, hlamSq, hxx]) (by rw [hy3, hyprod, hxd])
          · rw [decodePoint_mk_zero, tangent_eq]
            simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
              Specs.ShortWeierstrass.Point.mk.injEq]
            exact ⟨hX, hY⟩
      · -- distinct x-coordinates: the chord rule
        have hdne : decodeFe Q.x - decodeFe P.x ≠ 0 := sub_ne_zero.mpr hxx
        have hsx : sameX = 0 := by rw [hsameX, hdx, if_neg hdne]
        have hc0 : cancel = 0 := by rw [hcancel hQinf, hsx, zero_mul]
        rw [if_neg (fun h => hxx h.symm), hs1,
          if_neg (by rw [hc0]; exact zero_ne_one), hfin]
        have hdenv : decodeFe denv = decodeFe Q.x - decodeFe P.x := by
          rw [hden, if_neg (by rw [hsx]; exact zero_ne_one), hdx]
        have hlam' : decodeFe lamv * (decodeFe Q.x - decodeFe P.x)
            = decodeFe Q.y - decodeFe P.y := by
          have h := hlam (by rw [hdenv]; exact hdne)
          rw [hdenv] at h
          rw [h, hnum, if_neg (by rw [hsx]; exact zero_ne_one), hdy]
        have hslope : decodeFe lamv
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x) := by
          rw [eq_div_iff hdne]
          exact hlam'
        have hX : decodeFe x3v
            = ((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
              - decodeFe P.x - decodeFe Q.x := by
          rw [hx3, hxs, hlamSq, hslope]; ring
        have hY : decodeFe y3v
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)
              * (decodeFe P.x
                - (((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
                  - decodeFe P.x - decodeFe Q.x))
              - decodeFe P.y := by
          rw [hy3, hyprod, hxd, hslope, hX]
        refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
        · rw [onCurve_iff]
          exact chord_oncurve hPc hQc hdne hlam'
            (by rw [hx3, hxs, hlamSq]) (by rw [hy3, hyprod, hxd])
        · rw [decodePoint_mk_zero, chord_eq]
          simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
            Specs.ShortWeierstrass.Point.mk.injEq]
          exact ⟨hX, hY⟩
    · -- Q = 𝒪: the output is P
      rw [hs2, if_pos hQinf]
      refine ⟨hP, ?_⟩
      rw [decodePoint_of_isInf hQinf, decodePoint_of_finite hPinf, add_inf_right]
  · -- P = 𝒪: the output is Q
    rw [hout, if_pos hPinf]
    refine ⟨hQ, ?_⟩
    rw [decodePoint_of_isInf hPinf, add_inf_left]

end CompleteAdd

lemma limb_sum2_val {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val = u.val + v.val := by
  apply ZMod.val_add_of_lt
  have : (2:ℕ) ^ limbBits + 2 ^ limbBits < circomPrime := by decide
  omega

lemma value_sum2 (u : Emu (F circomPrime)) (hu : u.Normalized limbBits) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt)
      = BigInt.value limbBits u + BigInt.value limbBits u := by
  rw [BigInt.value_eq_sum, BigInt.value_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  have h := hu k
  rw [Fin.getElem_fin] at h
  rw [limb_sum2_val h h]
  ring

lemma decodeFe_sum2 (u : Emu (F circomPrime)) (hu : u.Normalized limbBits) :
    decodeFe (Vector.ofFn fun k : Fin numLimbs => u[k.val]'k.isLt + u[k.val]'k.isLt)
      = decodeFe u + decodeFe u := by
  show ((BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
      u[k.val]'k.isLt + u[k.val]'k.isLt) : ℕ) : Specs.Secp256k1.Fp) = _
  rw [value_sum2 u hu]
  push_cast
  rfl

lemma limb_sum2_lt {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val < 2 ^ (limbBits + 1) := by
  rw [limb_sum2_val hu hv]
  have : (2:ℕ) ^ (limbBits + 1) = 2 ^ limbBits + 2 ^ limbBits := by rw [pow_succ]; ring
  omega

lemma limb_sum2_bound (u : Emu (F circomPrime)) (hu : u.Normalized limbBits)
    (i : Fin numLimbs) :
    ((Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt)[i.val]'i.isLt).val < 2 ^ (limbBits + 1) := by
  rw [Vector.getElem_ofFn]
  have h : (u[i.val]'i.isLt).val < 2 ^ limbBits := hu i
  exact limb_sum2_lt h h

lemma value_sum2_bound (u : Emu (F circomPrime)) (hu : Fe.Valid u) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt) < 2 * P256 := by
  rw [value_sum2 u hu.1]
  have := hu.2
  omega

lemma value_sum2_alias (u : Emu (F circomPrime)) (hu : Fe.Valid u) :
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt) % P256 = 0 →
    BigInt.value limbBits (Vector.ofFn fun k : Fin numLimbs =>
        u[k.val]'k.isLt + u[k.val]'k.isLt) = 0 := by
  intro h
  rw [value_sum2 u hu.1] at h ⊢
  have hv := hu.2
  have hdvd : P256 ∣ (BigInt.value limbBits u + BigInt.value limbBits u) :=
    Nat.dvd_of_mod_eq_zero h
  rcases hdvd with ⟨c, hc⟩
  have hodd : P256 % 2 = 1 := by decide
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · have hcc : c = 0 ∨ c = 1 := by omega
    rcases hcc with rfl | rfl
    · omega
    · omega
  · have hle : P256 * 2 ≤ P256 * c := Nat.mul_le_mul_left _ hc2
    omega

lemma map_eval_sum2_input (env : Environment (F circomPrime))
    (yv : Var Emu (F circomPrime)) (y : Emu (F circomPrime))
    (h : Vector.map (Expression.eval env) yv = y) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun k : Fin numLimbs => yv[k.val]'k.isLt + yv[k.val]'k.isLt)
      = Vector.ofFn fun k : Fin numLimbs => y[k.val]'k.isLt + y[k.val]'k.isLt := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  have hcell : Expression.eval env (yv[i]'hi) = y[i]'hi := by
    have := congrArg (fun v : Emu (F circomPrime) => v[i]'hi) h
    simpa only [Vector.getElem_map] using this
  rw [show Expression.eval env (yv[i]'hi + yv[i]'hi)
        = Expression.eval env (yv[i]'hi) + Expression.eval env (yv[i]'hi) from rfl, hcell]

end Solution.Secp256k1ScalarMul
