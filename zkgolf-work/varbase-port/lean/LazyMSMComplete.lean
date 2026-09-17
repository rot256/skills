import Solution.Secp256k1ScalarMul.Lazy.LazyMSMFinal

/-!
# Completeness of the lazy chain

For an ordinary scalar (`sp = 0`, no infinite table entry, chain result
`E(1111)`) every step's assumptions follow from the invariant; for a special
scalar (`sp = 1`) only the range invariant is needed and the gated certificate
rows are trivially satisfied.
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.Sparse32
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

/-- What one iteration of the fold provides to the honest prover. -/
def StepHypC (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (k : Fin 64) : Prop :=
  (VarLookup.circuit.Assumptions (eval env (lkInput input k)) →
    VarLookup.circuit.Spec (eval env (lkInput input k)) (eval env (tVar i₀ k))) ∧
  (Step.ProverAssumptions k.val (eval env (stepIn input i₀ k)) →
    Step.Assumptions k.val (eval env (stepIn input i₀ k)) →
    Step.Spec k.val (eval env (stepIn input i₀ k)) (eval env (accL input i₀ (k.val + 1))))

lemma seed_valid (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) :
    Step.LazyValid 0 (eval env (seed input)) := by
  have h15 := hall.1 ⟨15, by norm_num⟩
  simp only [GLVMSM.tableEntry] at h15
  obtain ⟨hb, hx, hy, -⟩ := h15
  have hseed : eval env (seed input) =
      { x := embedVec (eval env input).tx[15], y := embedVec (eval env input).ty[15],
        isInf := (eval env input).tinf[15] } := by
    simp only [seed, circuit_norm]
    rw [Products.map_embedExpr, Products.map_embedExpr]
  rw [hseed]
  simp only [Step.LazyValid, embed_zwords _ hx.1, embed_zwords _ hy.1]
  exact ⟨hb, xIn_embed (canon_emuz hx.1), yIn_embed (canon_emuz hy.1) 0⟩

lemma stepIn_eval (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (k : Fin 64) :
    eval env (stepIn input i₀ k) =
      { acc := eval env (accL input i₀ k.val), t := eval env (tVar i₀ k),
        sp := Expression.eval env (spE input) } := by
  simp only [stepIn, circuit_norm]

/-! ### Ordinary scalars -/

lemma stepHyp_of_C (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input))
    (hnoinf : ∀ i : Fin 16, (eval env input).tinf[i] = 0)
    (k : Fin 64) (hk : StepHypC input i₀ env k) : StepHyp input i₀ env k := by
  obtain ⟨hlk, hst⟩ := hk
  refine ⟨hlk, fun hass => hst ⟨hass, fun _ => ?_⟩ hass⟩
  have hlks := hlk (lk_assumptions input env hall k)
  obtain ⟨hn, ht⟩ := lookup_value input env k _ hlks
  rw [stepIn_eval]
  show (eval env (tVar i₀ k)).isInf = 0
  rw [ht]
  exact hnoinf ⟨_, hn⟩

/-- Honest halves of `a − embed t` with `valZ (zwords a) = decodeFe t` satisfy
the certificate's assumptions and its spec. -/
lemma cert_diff_complete (l : VarLayout) (env : Environment (F circomPrime))
    (a : Var (fields 8) (F circomPrime)) (t : Var Emu (F circomPrime)) (lo hi : F circomPrime)
    (hbnd : ∀ k, slotLo l k ≤
        xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)) k ∧
      xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)) k ≤
        slotHi l k)
    (hlo : lo = Expression.eval env (Certs.half (Products.vsubE a (embedExpr t)) false))
    (hhi : hi = Expression.eval env (Certs.half (Products.vsubE a (embedExpr t)) true))
    (hv : valZ (zwords (Vector.map (Expression.eval env) a)) =
      Solution.Secp256k1ScalarMulFixedBase.decodeFe (Vector.map (Expression.eval env) t)) :
    Cert.Assumptions l #v[lo, hi] ∧ Cert.Spec #v[lo, hi] := by
  have hcast := Certs.eval_half_cast env (Products.vsubE a (embedExpr t))
    (xeq1Z (zwords (Vector.map (Expression.eval env) a)) (emuz (Vector.map (Expression.eval env) t)))
    (fun k => by
      rw [Products.map_vsubE, Products.map_embedExpr]
      exact Certs.vsub_cast _ _ _ _ (zwords_cast _) (embedVec_cast _) k)
  have hb := slot_half_bounds l _ hbnd
  have hm := Cert.model l #v[lo, hi] _ _ hb.1 hb.2 (by rw [hlo]; exact hcast.1)
    (by rw [hhi]; exact hcast.2)
  refine ⟨hm.1, hm.2.mpr ?_⟩
  rw [← eval_eq_halves, dvd_iff, xeq1Z_value, hv, sub_self]

/-! ### Special scalars -/

lemma lazyValid_fold (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (hsp : Expression.eval env (spE input) = 1)
    (hsteps : ∀ k : Fin 64, StepHypC input i₀ env k) :
    ∀ j, j ≤ 64 → Step.LazyValid j (eval env (accL input i₀ j)) := by
  intro j
  induction j with
  | zero => intro _; exact seed_valid input env hall
  | succ j ih =>
      intro hle
      have hj : j < 64 := by omega
      obtain ⟨hlk, hst⟩ := hsteps ⟨j, hj⟩
      have hlks := hlk (lk_assumptions input env hall ⟨j, hj⟩)
      obtain ⟨htv, -⟩ := lookup_selected input env hall ⟨j, hj⟩ _ hlks
      have hass : Step.Assumptions j (eval env (stepIn input i₀ ⟨j, hj⟩)) := by
        rw [stepIn_eval]
        exact ⟨ih (by omega), fun h => absurd (h.symm.trans hsp) zero_ne_one,
          tValid_of_valid htv, Or.inr hsp⟩
      have hpass : Step.ProverAssumptions j (eval env (stepIn input i₀ ⟨j, hj⟩)) := by
        refine ⟨hass, fun h => ?_⟩
        rw [stepIn_eval] at h
        exact absurd (h.symm.trans hsp) zero_ne_one
      exact (hst hpass hass).1

lemma cert_zero (l : VarLayout) :
    Cert.Assumptions l #v[(0 : F circomPrime), 0] ∧ Cert.Spec #v[(0 : F circomPrime), 0] := by
  have hb := slot_half_bounds l (fun _ => 0) (slot_zero l)
  have h0 : lowHalf (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp only [lowHalf]; ring
  have h1 : highHalf (fun _ : Fin 8 => (0 : ℤ)) = 0 := by simp only [highHalf]; ring
  rw [h0] at hb; rw [h1] at hb
  have hm := Cert.model l #v[(0 : F circomPrime), 0] 0 0 hb.1 hb.2 (by simp) (by simp)
  exact ⟨hm.1, hm.2.mpr (by simp)⟩

lemma foldl_zero_of (n : ℕ) (g : Fin n → F circomPrime) (hg : ∀ i, g i = 0) (c : F circomPrime) :
    Fin.foldl n (fun acc i => acc + g i) c = c := by
  induction n generalizing c with
  | zero => simp only [Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ, hg 0, add_zero]
      exact ih (fun i => g i.succ) (fun i => hg _) c

lemma defect_of_unitBits (env : Environment (F circomPrime))
    (m : Var (fields GLVMSM.coeffBits) (F circomPrime))
    (h : UnitBits (Vector.map (Expression.eval env) m)) :
    Expression.eval env (unitDefect m) = 0 := by
  obtain ⟨h0, hrest⟩ := h
  simp only [unitDefect, circuit_norm, eval_foldl_add]
  rw [foldl_zero_of 63 _ (fun i => by
    have := hrest ⟨i.val + 1, by have := i.isLt; simp only [GLVMSM.coeffBits]; omega⟩
      (by simp only; omega)
    simpa only [Vector.getElem_map] using this)]
  have h0' : Expression.eval env m[0] = 1 := by
    have := h0; rw [Vector.getElem_map] at this; exact this
  rw [h0']; ring

/-! ### The theorem -/

set_option maxHeartbeats 16000000 in
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) (Output := unit) main
    (fun i _ _ => ProverAssumptions i) (fun _ _ _ => True) := by
  circuit_proof_start_core
  subst h_input
  obtain ⟨hall, hnoinf, hchain, hunit⟩ := h_assumptions
  simp only [main, circuit_norm] at h_env ⊢
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, GLVMSM.varLookup_output,
    step_output', Step.output_eq_outputAt, foldlAcc_eq_accL, step_localLength', fin_foldl_eq_accL,
    dif_pos (show (0:ℕ) < 64 by norm_num), MulCell.circuit, MulCell.Assumptions, MulCell.Spec,
    Cert.circuit] at h_env ⊢
  obtain ⟨h_fold, hxl, hxh, hyl, hyh⟩ := h_env
  have hsteps : ∀ k : Fin 64, StepHypC input_var i₀ env.toEnvironment k := fun k => by
    simpa only [StepHypC, tVar, stepIn, accL_succ, Step.circuit, circuit_norm] using h_fold k
  have hsp' := tinf15_eq env.toEnvironment input_var
  have hb15 : IsBool (eval env.toEnvironment input_var).tinf[15] := (hall.1 ⟨15, by norm_num⟩).1
  refine ⟨fun k => ⟨lk_assumptions input_var env.toEnvironment hall k, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals sorry

end Solution.Secp256k1ScalarMul.LazyMSM
