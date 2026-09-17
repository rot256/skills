import Solution.Secp256k1ScalarMul.Lazy.LazyMSMSound

/-!
# Soundness of the lazy chain: the final check and the theorem

With `sp = 0` the certified halves of `acc − E(1111)` force the accumulator to
decode to `E(1111)`; with `sp = 1` the four unit-defect rows force the
magnitudes to `1`.
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.Sparse32
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

/-! ### The final certificates -/

lemma fin_of_ydiff {y : Words ℤ} {Ty : Fin 4 → ℤ} (hy : YIn depth y) (hTy : Canon Ty) :
    ∀ k, slotLo .fin k ≤ xeq1Z y Ty k ∧ xeq1Z y Ty k ≤ slotHi .fin k := by
  intro k
  have hyk := hy k
  have htk := embed_in hTy k
  simp only [slotLo, slotHi, finLo, finHi, xeq1Z, wmin, wmax, wsub, wzero, yLo, yHi] at *
  constructor
  · exact (min_le_left _ _).trans (by omega)
  · exact le_trans (by omega) (le_max_left _ _)

/-- Certified halves of `a − embed t` in a layout that contains the slot's
range force `valZ (zwords a) = decodeFe t`. -/
lemma cert_diff_value (l : VarLayout) (env : Environment (F circomPrime))
    (a : Var (fields 8) (F circomPrime)) (t : Var Emu (F circomPrime)) (lo hi : F circomPrime)
    (hbnd : ∀ k, slotLo l k ≤
        xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)) k ∧
      xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)) k ≤
        slotHi l k)
    (hlo : lo = Expression.eval env (Certs.half (Products.vsubE a (embedExpr t)) false))
    (hhi : hi = Expression.eval env (Certs.half (Products.vsubE a (embedExpr t)) true))
    (hc : Cert.Assumptions l #v[lo, hi] → Cert.Spec #v[lo, hi]) :
    valZ (zwords (Vector.map (Expression.eval env) a)) =
      Solution.Secp256k1ScalarMulFixedBase.decodeFe (Vector.map (Expression.eval env) t) := by
  have hcast := Certs.eval_half_cast env (Products.vsubE a (embedExpr t))
    (xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)))
    (fun k => by
      rw [Products.map_vsubE, Products.map_embedExpr]
      exact Certs.vsub_cast _ _ _ _ (zwords_cast _) (embedVec_cast _) k)
  have hb := slot_half_bounds l _ hbnd
  have hm := Cert.model l #v[lo, hi] _ _ hb.1 hb.2 (by rw [hlo]; exact hcast.1)
    (by rw [hhi]; exact hcast.2)
  have hv : valZ (xeq1Z (zwords (Vector.map (Expression.eval env) a))
      (emuz (Vector.map (Expression.eval env) t))) = 0 := by
    rw [← dvd_iff, eval_eq_halves]
    exact hm.2.mp (hc hm.1)
  rw [xeq1Z_value] at hv
  exact sub_eq_zero.mp hv

/-! ### The unit-defect rows -/

lemma eval_foldl_add (env : Environment (F circomPrime)) (n : ℕ)
    (f : Fin n → Expression (F circomPrime)) (e : Expression (F circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + f i) e) =
      Fin.foldl n (fun acc i => acc + Expression.eval env (f i)) (Expression.eval env e) := by
  induction n generalizing e with
  | zero => simp only [Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ, ih]
      simp only [circuit_norm]

lemma foldl_nat_cast (n : ℕ) (g : Fin n → ℕ) (c : ℕ) :
    Fin.foldl n (fun acc i => acc + ((g i : ℕ) : F circomPrime)) ((c : ℕ) : F circomPrime) =
      ((Fin.foldl n (fun acc i => acc + g i) c : ℕ) : F circomPrime) := by
  induction n generalizing c with
  | zero => simp only [Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ, ← Nat.cast_add, ih]

lemma foldl_sum_zero (n : ℕ) (g : Fin n → ℕ) (c : ℕ)
    (h : Fin.foldl n (fun acc i => acc + g i) c = 0) : c = 0 ∧ ∀ i, g i = 0 := by
  induction n generalizing c with
  | zero => exact ⟨by simpa only [Fin.foldl_zero] using h, fun i => i.elim0⟩
  | succ n ih =>
      rw [Fin.foldl_succ] at h
      obtain ⟨h0, hs⟩ := ih (fun i => g i.succ) (c + g 0) h
      refine ⟨by omega, ?_⟩
      intro i
      refine Fin.cases (by omega) (fun j => hs j) i

lemma foldl_sum_le (n : ℕ) (g : Fin n → ℕ) (hg : ∀ i, g i ≤ 1) (c : ℕ) :
    Fin.foldl n (fun acc i => acc + g i) c ≤ c + n := by
  induction n generalizing c with
  | zero => simp only [Fin.foldl_zero, add_zero, le_refl]
  | succ n ih =>
      rw [Fin.foldl_succ]
      have := ih (fun i => g i.succ) (fun i => hg _) (c + g 0)
      have h0 := hg 0
      omega

lemma circomPrime_gt : 65 < circomPrime := by
  decide

lemma isBool_val_le {x : F circomPrime} (h : IsBool x) : x.val ≤ 1 := by
  rcases h with h | h <;> subst h
  · rw [ZMod.val_zero]; omega
  · rw [LazyChain.val_one]

lemma unitBits_of_defect (env : Environment (F circomPrime))
    (m : Var (fields GLVMSM.coeffBits) (F circomPrime))
    (hb : ∀ i : Fin GLVMSM.coeffBits, IsBool (Vector.map (Expression.eval env) m)[i])
    (h : Expression.eval env (unitDefect m) = 0) :
    UnitBits (Vector.map (Expression.eval env) m) := by
  have hg : ∀ i : Fin 63, Expression.eval env (m[i.val + 1]'(by
      have := i.isLt; simp only [GLVMSM.coeffBits]; omega)) =
      (((Vector.map (Expression.eval env) m)[i.val + 1]'(by
        have := i.isLt; simp only [GLVMSM.coeffBits]; omega)).val : F circomPrime) := by
    intro i
    rw [Vector.getElem_map, ZMod.natCast_zmod_val]
  simp only [unitDefect, circuit_norm, eval_foldl_add] at h
  simp only [hg] at h
  have h0 : Expression.eval env m[0] = (((Vector.map (Expression.eval env) m)[0]).val : F circomPrime) := by
    rw [Vector.getElem_map, ZMod.natCast_zmod_val]
  rw [h0, show ((0 : F circomPrime)) = ((0 : ℕ) : F circomPrime) from rfl, foldl_nat_cast] at h
  -- now h : 1 - (v0 : F) + (N : F) = 0
  have hb0 := hb ⟨0, by simp only [GLVMSM.coeffBits]; omega⟩
  have hle := foldl_sum_le 63 (fun i => ((Vector.map (Expression.eval env) m)[i.val + 1]'(by
      have := i.isLt; simp only [GLVMSM.coeffBits]; omega)).val)
    (fun i => isBool_val_le (hb ⟨i.val + 1, by have := i.isLt; simp only [GLVMSM.coeffBits]; omega⟩)) 0
  simp only [Fin.getElem_fin] at hb0
  rcases hb0 with hb0 | hb0
  · exfalso
    rw [hb0] at h
    rw [ZMod.val_zero, Nat.cast_zero, neg_zero, add_zero] at h
    have hz : ((1 + Fin.foldl 63 (fun acc i => acc + ((Vector.map (Expression.eval env) m)[i.val + 1]'(by
        have := i.isLt; simp only [GLVMSM.coeffBits]; omega)).val) 0 : ℕ) : F circomPrime) = 0 := by
      push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at hz
    have := Nat.le_of_dvd (by omega) hz
    have := circomPrime_gt
    omega
  · rw [hb0] at h
    rw [LazyChain.val_one, Nat.cast_one, add_neg_cancel, zero_add, Nat.cast_zero] at h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hN : Fin.foldl 63 (fun acc i => acc + ((Vector.map (Expression.eval env) m)[i.val + 1]'(by
        have := i.isLt; simp only [GLVMSM.coeffBits]; omega)).val) 0 = 0 := by
      rcases Nat.eq_zero_or_pos (Fin.foldl 63 (fun acc i => acc + ((Vector.map (Expression.eval env) m)[i.val + 1]'(by
        have := i.isLt; simp only [GLVMSM.coeffBits]; omega)).val) 0) with hz | hpos
      · exact hz
      · have := Nat.le_of_dvd hpos h
        have := circomPrime_gt
        omega
    obtain ⟨-, hall⟩ := foldl_sum_zero 63 _ 0 hN
    refine ⟨hb0, ?_⟩
    intro i hi
    have hi' : i.val - 1 < 63 := by have := i.isLt; simp only [GLVMSM.coeffBits] at this; omega
    have := hall ⟨i.val - 1, hi'⟩
    simp only at this
    have hidx : i.val - 1 + 1 = i.val := by omega
    simp only [hidx] at this
    exact (ZMod.val_eq_zero _).mp this

/-! ### The theorem -/

lemma tinf15_eq (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) :
    Expression.eval env (spE input) = (eval env input).tinf[15] := by
  simp only [spE, circuit_norm, eval_vector, Vector.getElem_map]

lemma tx15_eq (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) :
    Vector.map (Expression.eval env) input.tx[15] = (eval env input).tx[15] := by
  simp only [circuit_norm, eval_vector, Vector.getElem_map]

lemma ty15_eq (env : Environment (F circomPrime)) (input : Var Inputs (F circomPrime)) :
    Vector.map (Expression.eval env) input.ty[15] = (eval env input).ty[15] := by
  simp only [circuit_norm, eval_vector, Vector.getElem_map]

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (F circomPrime) (Output := unit) main
    (fun i _ => Assumptions i) (fun i _ _ => Spec i) := by
  circuit_proof_start_core
  subst h_input
  have hall : GLVMSM.Assumptions (eval env input_var) := h_assumptions
  simp only [main, circuit_norm] at h_holds
  obtain ⟨h_fold, h_rest⟩ := h_holds
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, GLVMSM.varLookup_output,
    step_output', foldlAcc_eq_accL, step_localLength'] at h_fold
  simp only [circuit_norm, stepBody_localLength', stepBody_output', fin_foldl_eq_accL,
    dif_pos (show (0:ℕ) < 64 by norm_num), MulCell.circuit,
    MulCell.Assumptions, MulCell.Spec, Cert.circuit] at h_rest
  have hsteps : ∀ k : Fin 64, StepHyp input_var i₀ env k := fun k => by
    simpa only [StepHyp, tVar, stepIn, accL_succ, Step.circuit, circuit_norm] using h_fold k
  obtain ⟨hz, hxl, hxh, cx, hyl, hyh, cy, hu0, hu1, hu2, hu3⟩ := h_rest
  have hsp' := tinf15_eq env input_var
  refine ⟨?_, ?_⟩
  · unfold Spec
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · -- ordinary scalar: the chain result is `E(1111)`
      have hsp : Expression.eval env (spE input_var) = 0 := by rw [hsp', h0]
      have hinv := fold_inv input_var i₀ env hall hsp hsteps 64 le_rfl
      rw [hsp] at hz hxl hxh hyl hyh
      simp only [neg_zero, add_zero, one_mul] at hz hxl hxh hyl hyh
      have hacc : eval env (accL input_var i₀ 64) =
          { x := Vector.map (Expression.eval env) (accL input_var i₀ 64).x,
            y := Vector.map (Expression.eval env) (accL input_var i₀ 64).y,
            isInf := Expression.eval env (accL input_var i₀ 64).isInf } := by
        simp only [circuit_norm]
      rw [hacc] at hinv
      obtain ⟨⟨-, hX, hY⟩, -, hd⟩ := hinv
      have h15 := hall.1 ⟨15, by norm_num⟩
      simp only [GLVMSM.tableEntry] at h15
      have htx := tx15_eq env input_var
      have hty := ty15_eq env input_var
      have hCx : Canon (emuz (Vector.map (Expression.eval env) input_var.tx[15])) := by
        rw [htx]; exact canon_emuz h15.2.1.1
      have hCy : Canon (emuz (Vector.map (Expression.eval env) input_var.ty[15])) := by
        rw [hty]; exact canon_emuz h15.2.2.1.1
      have hvx := cert_diff_value .rel1 env (accL input_var i₀ 64).x input_var.tx[15] _ _
        (rel1_of_xeq1 hX hCx) hxl hxh cx
      have hvy := cert_diff_value .fin env (accL input_var i₀ 64).y input_var.ty[15] _ _
        (fin_of_ydiff hY hCy) hyl hyh cy
      show LazyChain.chainAcc (eval env input_var) 64 = _
      rw [← hd]
      simp only [Step.decodeL, GLVMSM.tableEntry, decodePoint]
      rw [if_neg (by rw [hz]; exact zero_ne_one), if_neg (by rw [h0]; exact zero_ne_one),
        hvx, hvy, htx, hty]
      rfl
    · -- special scalar: unit magnitudes
      have hsp : Expression.eval env (spE input_var) = 1 := by rw [hsp', h1]
      rw [hsp, one_mul] at hu0 hu1 hu2 hu3
      obtain ⟨-, -, hm0, hm1, hm2, hm3⟩ := hall
      have e0 : (eval env input_var).m0 = Vector.map (Expression.eval env) input_var.m0 := by
        simp only [circuit_norm]
      have e1 : (eval env input_var).m1 = Vector.map (Expression.eval env) input_var.m1 := by
        simp only [circuit_norm]
      have e2 : (eval env input_var).m2 = Vector.map (Expression.eval env) input_var.m2 := by
        simp only [circuit_norm]
      have e3 : (eval env input_var).m3 = Vector.map (Expression.eval env) input_var.m3 := by
        simp only [circuit_norm]
      rw [e0] at hm0 ⊢; rw [e1] at hm1 ⊢; rw [e2] at hm2 ⊢; rw [e3] at hm3 ⊢
      exact ⟨unitBits_of_defect env _ hm0 hu0, unitBits_of_defect env _ hm1 hu1,
        unitBits_of_defect env _ hm2 hu2, unitBits_of_defect env _ hm3 hu3⟩
  · have hM : MulCell.circuit.channelsWithRequirements = [] := rfl
    have hC : ∀ l, (Cert.circuit l).channelsWithRequirements = [] := fun _ => rfl
    have hV : VarLookup.circuit.channelsWithRequirements = [] := rfl
    have hS : ∀ n hn, (Step.circuit n hn).channelsWithRequirements = [] := fun _ _ => rfl
    simp only [main, stepBody, circuit_norm, hM, hC, hV, hS, true_or, and_self, implies_true]

end Solution.Secp256k1ScalarMul.LazyMSM
