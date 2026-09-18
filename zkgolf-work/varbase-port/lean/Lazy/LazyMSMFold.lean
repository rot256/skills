import Solution.Secp256k1ScalarMul.Lazy.LazyMSM
import Solution.Secp256k1ScalarMul.Lazy.StepCost
import Solution.Secp256k1ScalarMul.Lazy.ChainAlgebra

/-! ## merged from `Lazy/LazyMSMFold.lean` -/
section
/-!
# Fold bookkeeping for the lazy chain

The accumulator after `k` steps is a fixed variable pattern (`accL`), because
each step's output consists of fresh witnesses.  The lemmas here restate the
step's `localLength`/`output` facts at the scalar-mul field instance so that
`simp` can key on them inside the fold hypotheses.
-/

namespace Solution.Secp256k1ScalarMul.LazyMSM

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.SparseX
open Solution.Secp256k1ScalarMulFixedBase.LazyVar
open Solution.Secp256k1ScalarMul.Lazy

set_option maxHeartbeats 4000000

/-- Accumulator variables: the seed, then the output of step `k`. -/
def accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) : ℕ → Var LazyPt (F circomPrime)
  | 0 => seed input
  | k + 1 => Step.outputAt (i₀ + k * stepLen + 122)

lemma step_localLength' (k : ℕ) (hk : k + 1 ≤ depth) (i : Var Step.Inputs (F circomPrime)) :
    @FormalCircuitBase.localLength (F circomPrime) _ Step.Inputs Step.LazyPt _ _
      (@GeneralFormalCircuit.base (F circomPrime) Step.Inputs Step.LazyPt _ _ _ (Step.circuit k hk)) i
      = 1482 :=
  Step.circuit_localLength k hk i

lemma step_output' (k : ℕ) (hk : k + 1 ≤ depth) (i : Var Step.Inputs (F circomPrime)) (n₀ : ℕ) :
    @FormalCircuitBase.output (F circomPrime) _ Step.Inputs Step.LazyPt _ _
      (@GeneralFormalCircuit.base (F circomPrime) Step.Inputs Step.LazyPt _ _ _ (Step.circuit k hk)) i n₀
      = Step.outputAt n₀ :=
  Step.output_eq_outputAt k hk i n₀

lemma stepBody_localLength (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k).localLength n = 1604 := by
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, step_localLength']

lemma stepBody_localLength' (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : Operations.localLength (stepBody input acc k n).2 = 1604 :=
  stepBody_localLength input acc k n

lemma stepBody_output (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k).output n = Step.outputAt (n + 122) := by
  simp only [stepBody, circuit_norm, GLVMSM.varLookup_localLength, step_output', Step.output_eq_outputAt]

lemma stepBody_output' (input : Var Inputs (F circomPrime)) (acc : Var LazyPt (F circomPrime))
    (k : Fin 64) (n : ℕ) : (stepBody input acc k n).1 = Step.outputAt (n + 122) :=
  stepBody_output input acc k n

lemma fin_foldl_ignore_acc {α : Type} (k : ℕ) (f : ℕ → α) (init : α) :
    Fin.foldl (k + 1) (fun _ i => f i.val) init = f k := by
  rw [Fin.foldl_succ_last]
  simp

lemma foldlAcc_eq_accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (i : Fin 64) :
    Circuit.FoldlM.foldlAcc (β := LazyPt (Expression (F circomPrime))) i₀ (Vector.finRange 64)
      (stepBody input) (seed input) i = accL input i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, stepBody, circuit_norm,
    GLVMSM.varLookup_localLength, step_output', step_localLength']
  rcases i with ⟨k, hk⟩
  cases k with
  | zero => simp [Fin.foldl_zero, accL]
  | succ k =>
      exact fin_foldl_ignore_acc k (fun v => Step.outputAt (i₀ + v * stepLen + 122)) (seed input)

lemma fin_foldl_eq_accL (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    Fin.foldl 64 (fun (_ : LazyPt (Expression (F circomPrime))) (i : Fin 64) =>
      Step.outputAt (i₀ + i.val * 1604 + 122)) (seed input) = accL input i₀ 64 :=
  fin_foldl_ignore_acc 63 (fun v => Step.outputAt (i₀ + v * 1604 + 122)) (seed input)

end Solution.Secp256k1ScalarMul.LazyMSM
end

/-! ## merged from `Lazy/LazyMSMSound.lean` -/
section
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
  varFromOffset FlaggedPoint (i₀ + k.val * 1604 + 112)

def stepIn (input : Var Inputs (F circomPrime)) (i₀ : ℕ) (k : Fin 64) :
    Var Step.Inputs (F circomPrime) :=
  { acc := accL input i₀ k.val, t := tVar i₀ k, sp := spE input }

lemma accL_succ (input : Var Inputs (F circomPrime)) (i₀ k : ℕ) :
    accL input i₀ (k + 1) = Step.outputAt (i₀ + k * 1604 + 122) := rfl

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
    exact ⟨hinv.1, fun _ => hinv.2.1, tValid_of_valid htv, hspB⟩
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
end

/-! ## merged from `Lazy/LazyMSMFinal.lean` -/
section
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
end

/-! ## merged from `Lazy/LazyMSMComplete.lean` -/
section
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
    simp only [circuit_norm, eval_vector, Vector.getElem_map]
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
    simpa only [Fin.getElem_fin, Vector.getElem_map] using this)]
  have h0' : Expression.eval env m[0] = 1 := by
    have := h0; rw [Vector.getElem_map] at this; exact this
  rw [h0']; ring

/-! ### The theorem -/

set_option maxHeartbeats 16000000 in
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) (Output := unit) main
    (fun i _ _ => ProverAssumptions i) (fun _ _ _ => True) := by
  circuit_proof_start_core
  have h_input' : eval env.toEnvironment input_var = input := by
    simpa only [CircuitType.eval_expression_prover_to_verifier (M := Inputs)] using h_input
  subst h_input'
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
  have hlkA : ∀ k : Fin 64, VarLookup.circuit.Assumptions
      (eval env.toEnvironment (lkInput input_var k)) :=
    fun k => lk_assumptions input_var env.toEnvironment hall k
  rcases hb15 with hsp0 | hsp1
  · -- ordinary scalar
    have hsp : Expression.eval env.toEnvironment (spE input_var) = 0 := by rw [hsp', hsp0]
    have hni := hnoinf hsp0
    have hsteps' : ∀ k : Fin 64, StepHyp input_var i₀ env.toEnvironment k :=
      fun k => stepHyp_of_C input_var i₀ env.toEnvironment hall hni k (hsteps k)
    have hinv := fold_inv input_var i₀ env.toEnvironment hall hsp hsteps'
    have hacc : eval env.toEnvironment (accL input_var i₀ 64) =
        { x := Vector.map (Expression.eval env.toEnvironment) (accL input_var i₀ 64).x,
          y := Vector.map (Expression.eval env.toEnvironment) (accL input_var i₀ 64).y,
          isInf := Expression.eval env.toEnvironment (accL input_var i₀ 64).isInf } := by
      simp only [circuit_norm]
    have hinv64 := hinv 64 le_rfl
    rw [hacc] at hinv64
    obtain ⟨⟨hib, hX, hY⟩, -, hd⟩ := hinv64
    have hE : LazyChain.chainAcc (eval env.toEnvironment input_var) 64 =
        decodePoint (GLVMSM.tableEntry (eval env.toEnvironment input_var) 15 (by norm_num)) :=
      hchain hsp0
    have hdec := hd.trans hE
    simp only [Step.decodeL, GLVMSM.tableEntry, decodePoint, hsp0, zero_ne_one, ↓reduceIte] at hdec
    have hi0 : Expression.eval env.toEnvironment (accL input_var i₀ 64).isInf = 0 := by
      rcases hib with h | h
      · exact h
      · rw [if_pos h] at hdec; cases hdec
    rw [if_neg (by rw [hi0]; exact zero_ne_one)] at hdec
    simp only [GroupPoint.affine.injEq, Point.mk.injEq] at hdec
    obtain ⟨hvx, hvy⟩ := hdec
    have h15 := hall.1 ⟨15, by norm_num⟩
    simp only [GLVMSM.tableEntry] at h15
    have htx := tx15_eq env.toEnvironment input_var
    have hty := ty15_eq env.toEnvironment input_var
    have hCx : Canon (emuz (Vector.map (Expression.eval env.toEnvironment) input_var.tx[15])) := by
      rw [htx]; exact canon_emuz h15.2.1.1
    have hCy : Canon (emuz (Vector.map (Expression.eval env.toEnvironment) input_var.ty[15])) := by
      rw [hty]; exact canon_emuz h15.2.2.1.1
    rw [hsp] at hxl hxh hyl hyh
    simp only [neg_zero, add_zero, one_mul] at hxl hxh hyl hyh
    refine ⟨fun k => ⟨by simpa only [circuit_norm] using hlkA k, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hk := hinv k.val (by omega)
      have hlks := (hsteps k).1 (hlkA k)
      obtain ⟨hn, ht⟩ := lookup_value input_var env.toEnvironment k _ hlks
      obtain ⟨htv, -⟩ := lookup_selected input_var env.toEnvironment hall k _ hlks
      have hpa : Step.ProverAssumptions k.val (eval env.toEnvironment (stepIn input_var i₀ k)) := by
        rw [stepIn_eval]
        refine ⟨⟨hk.1, fun _ => hk.2.1, tValid_of_valid htv, Or.inl hsp⟩, fun _ => ?_⟩
        show (eval env.toEnvironment (tVar i₀ k)).isInf = 0
        rw [ht]; exact hni ⟨_, hn⟩
      simpa only [stepIn, tVar, circuit_norm, Step.circuit] using hpa
    · rw [hsp, hi0]; ring
    · exact cert_diff_complete .rel1 env.toEnvironment (accL input_var i₀ 64).x input_var.tx[15] _ _
        (rel1_of_xeq1 hX hCx) hxl hxh (by rw [htx]; exact hvx)
    · exact cert_diff_complete .fin env.toEnvironment (accL input_var i₀ 64).y input_var.ty[15] _ _
        (fin_of_ydiff hY hCy) hyl hyh (by rw [hty]; exact hvy)
    all_goals rw [hsp, zero_mul]
  · -- special scalar
    have hsp : Expression.eval env.toEnvironment (spE input_var) = 1 := by rw [hsp', hsp1]
    have hlv := lazyValid_fold input_var i₀ env.toEnvironment hall hsp hsteps
    obtain ⟨hu0, hu1, hu2, hu3⟩ := hunit hsp1
    have e0 : (eval env.toEnvironment input_var).m0 =
        Vector.map (Expression.eval env.toEnvironment) input_var.m0 := by simp only [circuit_norm]
    have e1 : (eval env.toEnvironment input_var).m1 =
        Vector.map (Expression.eval env.toEnvironment) input_var.m1 := by simp only [circuit_norm]
    have e2 : (eval env.toEnvironment input_var).m2 =
        Vector.map (Expression.eval env.toEnvironment) input_var.m2 := by simp only [circuit_norm]
    have e3 : (eval env.toEnvironment input_var).m3 =
        Vector.map (Expression.eval env.toEnvironment) input_var.m3 := by simp only [circuit_norm]
    rw [e0] at hu0; rw [e1] at hu1; rw [e2] at hu2; rw [e3] at hu3
    rw [hsp] at hxl hxh hyl hyh
    simp only [add_neg_cancel, zero_mul] at hxl hxh hyl hyh
    refine ⟨fun k => ⟨by simpa only [circuit_norm] using hlkA k, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hlks := (hsteps k).1 (hlkA k)
      obtain ⟨htv, -⟩ := lookup_selected input_var env.toEnvironment hall k _ hlks
      have hpa : Step.ProverAssumptions k.val (eval env.toEnvironment (stepIn input_var i₀ k)) := by
        rw [stepIn_eval]
        exact ⟨⟨hlv k.val (by omega), fun h => absurd (h.symm.trans hsp) zero_ne_one,
          tValid_of_valid htv, Or.inr hsp⟩, fun h => absurd (h.symm.trans hsp) zero_ne_one⟩
      simpa only [stepIn, tVar, circuit_norm, Step.circuit] using hpa
    · rw [hsp]; ring
    · simp only [hxl, hxh]; exact cert_zero _
    · simp only [hyl, hyh]; exact cert_zero _
    · rw [hsp, one_mul]; exact defect_of_unitBits _ _ hu0
    · rw [hsp, one_mul]; exact defect_of_unitBits _ _ hu1
    · rw [hsp, one_mul]; exact defect_of_unitBits _ _ hu2
    · rw [hsp, one_mul]; exact defect_of_unitBits _ _ hu3

end Solution.Secp256k1ScalarMul.LazyMSM
end
