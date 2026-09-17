import Solution.Secp256k1ScalarMul.Lazy.LazyMSMFold
import Solution.Secp256k1ScalarMul.Lazy.ChainAlgebra

/-!
# Soundness of the lazy chain: value-level lemmas

Lookup outputs are table entries, the seed is `E(1111)`, and each step keeps
the invariant `decodeL acc = chainAcc k` (for ordinary scalars, `sp = 0`).
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

/-! ### Variables of the fold -/

/-- The lookup output of step `k`. -/
def tVar (i₀ : ℕ) (k : Fin 64) : Var FlaggedPoint (F circomPrime) :=
  varFromOffset FlaggedPoint (i₀ + k.val * 1622 + 112)

def stepIn (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (k : Fin 64) :
    Var Step.Inputs (F circomPrime) :=
  { acc := accL input i₀ k.val, t := tVar i₀ k, sp := spE input }

lemma accL_succ (input : Var Inputs (F circomPrime)) (i₀ k : ℕ) :
    accL input i₀ (k + 1) = Step.outputAt (i₀ + k * 1622 + 122) := rfl

lemma step_hk (k : Fin 64) : k.val + 1 ≤ depth := by
  have := k.isLt; simp only [depth]; omega

/-- What one iteration of the fold guarantees. -/
def StepHyp (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (k : Fin 64) : Prop :=
  (VarLookup.circuit.Assumptions (eval env (lkInput input k)) →
    VarLookup.circuit.Spec (eval env (lkInput input k)) (eval env (tVar i₀ k))) ∧
  (Step.Assumptions k.val (eval env (stepIn input i₀ k)) →
    Step.Spec k.val (eval env (stepIn input i₀ k)) (eval env (accL input i₀ (k.val + 1))))

/-! ### Lookups -/

lemma entry_lk (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (k : Fin 64) (i : ℕ) (h : i < 16) :
    VarLookup.entry (eval env (lkInput input k)) i h = GLVMSM.tableEntry (eval env input) i h := by
  simp only [VarLookup.entry, lkInput, GLVMSM.tableEntry, circuit_norm]

lemma nibble_lk (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (k : Fin 64) :
    VarLookup.nibble (eval env (lkInput input k)) =
      GLVMSM.nibbleAt (eval env input) k.val k.isLt := by
  simp only [VarLookup.nibble, lkInput, GLVMSM.nibbleAt, bitIdx, circuit_norm]

lemma lk_assumptions (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (k : Fin 64) :
    VarLookup.circuit.Assumptions (eval env (lkInput input k)) := by
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  simp only [VarLookup.circuit, VarLookup.Assumptions]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [lkInput, circuit_norm] using hm3 ⟨bitIdx k, bitIdx_lt k⟩
  · simpa only [lkInput, circuit_norm] using hm2 ⟨bitIdx k, bitIdx_lt k⟩
  · simpa only [lkInput, circuit_norm] using hm1 ⟨bitIdx k, bitIdx_lt k⟩
  · simpa only [lkInput, circuit_norm] using hm0 ⟨bitIdx k, bitIdx_lt k⟩
  · intro j; simpa only [entry_lk] using htab j
  · intro j; simpa only [entry_lk] using htabCanon j

lemma lookup_value (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (k : Fin 64) (t : FlaggedPoint (F circomPrime))
    (h : VarLookup.circuit.Spec (eval env (lkInput input k)) t) :
    ∃ hn : GLVMSM.nibbleAt (eval env input) k.val k.isLt < 16,
      t = GLVMSM.tableEntry (eval env input) (GLVMSM.nibbleAt (eval env input) k.val k.isLt) hn := by
  simp only [VarLookup.circuit, VarLookup.Spec] at h
  obtain ⟨hn, ht⟩ := h
  have hNe := nibble_lk input env k
  refine ⟨hNe ▸ hn, ?_⟩
  rw [ht, entry_lk]
  exact GLVMSM.tableEntry_index_congr _ _ _ hn _ hNe

lemma decodeT_eq (t : FlaggedPoint (F circomPrime)) : Step.decodeT t = decodePoint t := rfl

lemma tValid_of_valid {t : FlaggedPoint (F circomPrime)} (h : t.Valid) : Step.TValid t :=
  ⟨h.1, h.2.1.1, h.2.2.1.1, fun h0 => (CompleteAdd.onCurve_iff _).mp (h.2.2.2 h0)⟩

/-- The lookup of step `k` decodes to `selectedAt k` and is a valid point. -/
lemma lookup_selected (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (k : Fin 64) (t : FlaggedPoint (F circomPrime))
    (h : VarLookup.circuit.Spec (eval env (lkInput input k)) t) :
    t.Valid ∧ Step.decodeT t = GLVMSM.selectedAt (eval env input) k.val k.isLt := by
  obtain ⟨hn, ht⟩ := lookup_value input env k t h
  refine ⟨ht ▸ hall.1 ⟨_, hn⟩, ?_⟩
  rw [decodeT_eq, ht, GLVMSM.selectedAt, dif_pos hn]

/-! ### Seed -/

def Inv (input : Inputs (F circomPrime)) (k : ℕ) (P : LazyPt (F circomPrime)) : Prop :=
  Step.LazyValid k P ∧ Step.OnCurveLazy P ∧ Step.decodeL P = LazyChain.chainAcc input k

lemma canon_emuz {t : Emu (F circomPrime)} (ht : BigInt.Normalized 64 t) : Canon (emuz t) :=
  fun i => emuz_bounds t ht i

lemma seed_inv (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (hsp : (eval env input).tinf[15] = 0) :
    Inv (eval env input) 0 (eval env (seed input)) := by
  have h15 := hall.1 ⟨15, by norm_num⟩
  simp only [GLVMSM.tableEntry] at h15
  obtain ⟨hb, hx, hy, hoc⟩ := h15
  have hCx : Canon (emuz (eval env input).tx[15]) := canon_emuz hx.1
  have hCy : Canon (emuz (eval env input).ty[15]) := canon_emuz hy.1
  have hseed : eval env (seed input) =
      { x := embedVec (eval env input).tx[15], y := embedVec (eval env input).ty[15],
        isInf := (eval env input).tinf[15] } := by
    simp only [seed, circuit_norm]
    rw [Products.map_embedExpr, Products.map_embedExpr]
    simp only [circuit_norm, eval_vector, Vector.getElem_map]
  rw [hseed]
  simp only [Inv, Step.LazyValid, Step.OnCurveLazy, Step.decodeL, LazyChain.chainAcc,
    GLVMSM.tableEntry, decodePoint, embed_zwords _ hx.1, embed_zwords _ hy.1, valZ_embed]
  refine ⟨⟨hb, xIn_embed hCx, yIn_embed hCy 0⟩, fun h0 => (CompleteAdd.onCurve_iff _).mp (hoc h0), ?_⟩
  have hne : ¬ (eval env input).tinf[15] = 1 := by rw [hsp]; exact zero_ne_one
  rw [if_neg hne, if_neg hne]
  rfl

/-! ### Steps -/

lemma step_inv (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (hsp : Expression.eval env (spE input) = 0)
    (k : Fin 64) (hk : StepHyp input i₀ env k)
    (hinv : Inv (eval env input) k.val (eval env (accL input i₀ k.val))) :
    Inv (eval env input) (k.val + 1) (eval env (accL input i₀ (k.val + 1))) := by
  obtain ⟨hlk, hst⟩ := hk
  have hlks := hlk (lk_assumptions input env hall k)
  obtain ⟨htv, htd⟩ := lookup_selected input env hall k _ hlks
  have hspB : IsBool (Expression.eval env (spE input)) := Or.inl hsp
  have hin : eval env (stepIn input i₀ k) =
      { acc := eval env (accL input i₀ k.val), t := eval env (tVar i₀ k),
        sp := Expression.eval env (spE input) } := by
    simp only [stepIn, circuit_norm]
  have hass : Step.Assumptions k.val (eval env (stepIn input i₀ k)) := by
    rw [hin]
    exact ⟨hinv.1, hinv.2.1, tValid_of_valid htv, hspB⟩
  have hspec := hst hass
  rw [hin] at hspec
  obtain ⟨hv, hrest⟩ := hspec
  obtain ⟨-, hoc, hd⟩ := hrest hsp
  refine ⟨hv, hoc, ?_⟩
  rw [hd, htd, hinv.2.2, LazyChain.chainAcc, dif_pos (show k.val < GLVMSM.coeffBits from k.isLt)]

lemma fold_inv (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (env : Environment (F circomPrime))
    (hall : GLVMSM.Assumptions (eval env input)) (hsp : Expression.eval env (spE input) = 0)
    (hsteps : ∀ k : Fin 64, StepHyp input i₀ env k) :
    ∀ j, j ≤ 64 → Inv (eval env input) j (eval env (accL input i₀ j)) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact seed_inv input env hall (by simpa only [spE, circuit_norm] using hsp)
  | succ j ih =>
      intro hle
      exact step_inv input i₀ env hall hsp ⟨j, by omega⟩ (hsteps ⟨j, by omega⟩) (ih (by omega))

end Solution.Secp256k1ScalarMul.LazyMSM
