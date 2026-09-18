import Solution.Secp256k1ScalarMul.GLVStepLastLow
import Solution.Secp256k1ScalarMul.ScalarMulTheorems



namespace Solution.Secp256k1ScalarMul
namespace GLVMSM

open Specs.ShortWeierstrass Specs.Secp256k1

def coeffBits : ℕ := 64

structure Inputs (F : Type) where
  tx : Vector (Emu F) 16
  ty : Vector (Emu F) 16
  tinf : Vector F 16
  m0 : Vector F coeffBits
  m1 : Vector F coeffBits
  m2 : Vector F coeffBits
  m3 : Vector F coeffBits
deriving ProvableStruct

def stepInput (input : Var Inputs (F circomPrime))
    (acc : Var FlaggedPoint (F circomPrime)) (i : Fin coeffBits) :
    Var GLVStep.Inputs (F circomPrime) :=
  { acc, tx := input.tx, ty := input.ty, tinf := input.tinf,
    b3 := input.m3[coeffBits - 1 - i.val]'(by have := i.isLt; simp only [coeffBits] at this ⊢; omega),
    b2 := input.m2[coeffBits - 1 - i.val]'(by have := i.isLt; simp only [coeffBits] at this ⊢; omega),
    b1 := input.m1[coeffBits - 1 - i.val]'(by have := i.isLt; simp only [coeffBits] at this ⊢; omega),
    b0 := input.m0[coeffBits - 1 - i.val]'(by have := i.isLt; simp only [coeffBits] at this ⊢; omega) }

def lk0Input (input : Var Inputs (F circomPrime)) : Var VarLookup.Inputs (F circomPrime) :=
  { tx := input.tx, ty := input.ty, tinf := input.tinf,
    b3 := input.m3[coeffBits - 1]'(by simp only [coeffBits]; omega),
    b2 := input.m2[coeffBits - 1]'(by simp only [coeffBits]; omega),
    b1 := input.m1[coeffBits - 1]'(by simp only [coeffBits]; omega),
    b0 := input.m0[coeffBits - 1]'(by simp only [coeffBits]; omega) }

private def stepLength' (input : Var Inputs (F circomPrime)) :
    Circuit.ConstantLength
      (fun (x : Var FlaggedPoint (F circomPrime) × Fin 62) =>
        subcircuit GLVStep.circuit
          (stepInput input x.1 ⟨x.2.val + 1, by have := x.2.isLt; simp only [coeffBits]; omega⟩)) where
  localLength := 2149
  localLength_eq x _ := by
    simpa only using
      GLVStep.localLength (stepInput input x.1 ⟨x.2.val + 1, by have := x.2.isLt; simp only [coeffBits]; omega⟩)

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let ent0 ← subcircuit VarLookup.circuit (lk0Input input)
  let acc ← Circuit.foldlRange 62 ent0
    (fun acc i => subcircuit GLVStep.circuit
      (stepInput input acc ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩))
    (stepLength' input)
  subcircuit GLVStepLastLow.circuit
    (stepInput input acc ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩)

private def elaboratedNaive : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

def tableEntry (input : Inputs (F circomPrime)) (i : ℕ) (h : i < 16) :
    FlaggedPoint (F circomPrime) :=
  { x := input.tx[i]'h, y := input.ty[i]'h, isInf := input.tinf[i]'h }

def nibbleAt (input : Inputs (F circomPrime)) (k : ℕ) (hk : k < coeffBits) : ℕ :=
  8 * (input.m3[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
  4 * (input.m2[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
  2 * (input.m1[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val +
      (input.m0[coeffBits - 1 - k]'(by simp only [coeffBits] at hk ⊢; omega)).val

def selectedAt (input : Inputs (F circomPrime)) (k : ℕ) (hk : k < coeffBits) :
    GroupPoint Fp :=
  if hn : nibbleAt input k hk < 16 then
    decodePoint (tableEntry input (nibbleAt input k hk) hn)
  else .infinity

def specAcc (input : Inputs (F circomPrime)) : ℕ → GroupPoint Fp
  | 0 => .infinity
  | k + 1 =>
      if hk : k < coeffBits then
        add curve (GLVStep.dbl (specAcc input k)) (selectedAt input k hk)
      else specAcc input k

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin 16, (tableEntry input i.val i.isLt).Valid) ∧
  (∀ i : Fin 16, (tableEntry input i.val i.isLt).isInf = 1 →
    decodeFe (tableEntry input i.val i.isLt).x = 0) ∧
  (∀ i : Fin coeffBits, IsBool input.m0[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m1[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m2[i]) ∧
  (∀ i : Fin coeffBits, IsBool input.m3[i])

def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.isInf = if specAcc input coeffBits = .infinity then 1 else 0

-- index 0 = infinity placeholder, index 1 = VarLookup seed, index k+2 = fold-step k output
def accVar (i₀ : ℕ) : ℕ → Var FlaggedPoint (F circomPrime)
  | 0 => infConst
  | 1 => varFromOffset FlaggedPoint (i₀ + 112)
  | (k + 2) =>
      if k < 62 then
        GLVStep.outputAt (i₀ + 122 + k * 2149)
      else
        GLVStepLastLow.outputAt (i₀ + 122 + 62 * 2149)

/-- The VarLookup output sits at offset `n + 112` (localLength 122, size 9). -/
lemma varLookup_output (input : Var VarLookup.Inputs (F circomPrime)) (n : ℕ) :
    VarLookup.circuit.output input n = varFromOffset FlaggedPoint (n + 112) := by
  show VarLookup.elaborated.output input n = _
  rw [← VarLookup.elaborated.output_eq input n]
  exact VarLookup.output_eq input n

lemma varLookup_localLength (input : Var VarLookup.Inputs (F circomPrime)) :
    VarLookup.circuit.localLength input = 122 := rfl

-- The VarLookup seed output equals the (opaque) accVar index-1 var.
lemma varLookup_output_seed (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    VarLookup.circuit.output (lk0Input input) i₀ = accVar i₀ 1 := varLookup_output _ _

private lemma fin_foldl_ignore_acc {α : Type} (k : ℕ) (f : ℕ → α) (init : α) :
    Fin.foldl (k + 1) (fun _ i => f i.val) init = f k := by
  rw [Fin.foldl_succ_last]
  simp

-- Fold over the normal steps, starting the accumulator at the VarLookup seed.
lemma fin_foldl_eq_accVar (i₀ k : ℕ) (hk : k ≤ 62) :
    Fin.foldl k
      (fun (_ : FlaggedPoint (Expression (F circomPrime))) (j : Fin k) =>
        GLVStep.outputAt (i₀ + 122 + j.val * 2149)) (accVar i₀ 1) = accVar i₀ (k + 1) := by
  cases k with
  | zero => simp [Fin.foldl_zero, accVar]
  | succ k =>
      have hklt : k < 62 := by omega
      simpa only [accVar, if_pos hklt] using
        (fin_foldl_ignore_acc k
          (fun v => GLVStep.outputAt (i₀ + 122 + v * 2149)) (accVar i₀ 1))

lemma foldlAcc_eq_accVar (input : Var Inputs (F circomPrime)) (i₀ : ℕ)
    (i : Fin 62) :
    Circuit.FoldlM.foldlAcc (β := FlaggedPoint (Expression (F circomPrime))) (i₀ + 122)
      (Vector.finRange 62)
      (fun acc (j : Fin 62) => subcircuit GLVStep.circuit
        (stepInput input acc ⟨j.val + 1, by have := j.isLt; simp only [coeffBits]; omega⟩))
      (accVar i₀ 1) i = accVar i₀ (i.val + 1) := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, circuit_norm]
  simp only [GLVStep.localLength, GLVStep.output_eq_outputAt]
  exact fin_foldl_eq_accVar i₀ i.val (by have := i.isLt; omega)

lemma fin_foldl_eq_accVar_62 (i₀ : ℕ) :
    Fin.foldl 62
      (fun (_ : FlaggedPoint (Expression (F circomPrime))) (j : Fin 62) =>
        GLVStep.outputAt (i₀ + 122 + j.val * 2149)) (accVar i₀ 1) = accVar i₀ 63 :=
  fin_foldl_eq_accVar i₀ 62 (by omega)

lemma foldlLastAcc_eq_accVar (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    Fin.foldl 62
      (fun acc (i : Fin 62) =>
        GLVStep.circuit.output
          (stepInput input acc
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)
          (i₀ + VarLookup.circuit.localLength (lk0Input input) +
            i.val * GLVStep.circuit.localLength
              (stepInput input default
                ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)))
      (VarLookup.circuit.output (lk0Input input) i₀) = accVar i₀ 63 := by
  simp only [varLookup_localLength, varLookup_output_seed,
    GLVStep.localLength, GLVStep.output_eq_outputAt]
  exact fin_foldl_eq_accVar_62 i₀

lemma lastStepOffset_eq (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    i₀ + VarLookup.circuit.localLength (lk0Input input) +
      (if _ : 0 < 62 then
        62 * GLVStep.circuit.localLength
          (stepInput input default ⟨1, by simp only [coeffBits]; omega⟩)
       else 0) =
      i₀ + 122 + 62 * 2149 := by
  rw [dif_pos (by omega : 0 < 62)]
  simp only [varLookup_localLength, GLVStep.localLength]

lemma lastStepOffset_simp_eq (i₀ : ℕ) :
    i₀ + 122 + (if _ : 0 < 62 then 62 * 2149 else 0) =
      i₀ + 122 + 62 * 2149 := by
  rw [dif_pos (by omega : 0 < 62)]

lemma glvStepLast_circuit_output_eq (input : Var GLVStep.Inputs (F circomPrime)) (i₀ : ℕ) :
    GLVStepLastLow.circuit.output input i₀ = GLVStepLastLow.outputAt i₀ := by
  simpa only [circuit_norm] using GLVStepLastLow.output_eq input i₀

lemma lastStepOutputAt_eq_accVar (i₀ : ℕ) :
    GLVStepLastLow.outputAt (i₀ + 122 + 62 * 2149) = accVar i₀ coeffBits := by
  simp only [accVar, coeffBits, Nat.reduceSub, if_pos (by omega : 61 < 62),
    if_neg (by omega : ¬ 62 < 62)]

lemma lastStepOutput_eq_accVar (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    GLVStepLastLow.circuit.output
      (stepInput input (accVar i₀ 63)
        ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩)
      (i₀ + 122 + 62 * 2149) = accVar i₀ coeffBits := by
  rw [glvStepLast_circuit_output_eq, lastStepOutputAt_eq_accVar]

-- Generalized GLVStep transition: consuming a GLVStep at bit position `pos`.
set_option maxRecDepth 8192 in
lemma glvstep_transition (input : Var Inputs (F circomPrime))
    (env : Environment (F circomPrime)) (pos : ℕ) (hpos : pos < coeffBits)
    (accPrev outVar : Var FlaggedPoint (F circomPrime))
    (hall : Assumptions (eval env input))
    (ih_valid : (eval env accPrev).Valid)
    (ih_dec : decodePoint (eval env accPrev) = specAcc (eval env input) pos)
    (h_step :
      GLVStep.circuit.Assumptions
          (eval env (stepInput input accPrev ⟨pos, hpos⟩)) →
        GLVStep.circuit.Spec
          (eval env (stepInput input accPrev ⟨pos, hpos⟩))
          (eval env outVar)) :
    (eval env outVar).Valid ∧
      decodePoint (eval env outVar) = specAcc (eval env input) (pos + 1) := by
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  have hsass : GLVStep.circuit.Assumptions
      (eval env (stepInput input accPrev ⟨pos, hpos⟩)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stepInput, circuit_norm] using ih_valid
    · intro j
      simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
        tableEntry, circuit_norm] using htab j
    · intro j
      simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
        using htabCanon j
    · simpa only [stepInput, circuit_norm] using
        hm3 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm2 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm1 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm0 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
  obtain ⟨hout_valid, hnib, hout_dec⟩ := h_step hsass
  have hnib' : nibbleAt (eval env input) pos hpos < 16 := by
    simpa only [GLVStep.nibble, GLVStep.toLk, VarLookup.nibble, stepInput,
      nibbleAt, circuit_norm] using hnib
  have hout_dec' :
      decodePoint (eval env outVar) =
        add curve (GLVStep.dbl (decodePoint (eval env accPrev)))
          (decodePoint (tableEntry (eval env input) (nibbleAt (eval env input) pos hpos) hnib')) := by
    simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry,
      GLVStep.nibble, VarLookup.nibble, stepInput, tableEntry, nibbleAt,
      circuit_norm] using hout_dec
  refine ⟨hout_valid, ?_⟩
  rw [hout_dec', ih_dec, specAcc, dif_pos hpos]
  unfold selectedAt
  simp only [dif_pos hnib']

set_option maxRecDepth 8192 in
lemma glvstepLast_transition (input : Var Inputs (F circomPrime))
    (env : Environment (F circomPrime)) (pos : ℕ) (hpos : pos < coeffBits)
    (accPrev outVar : Var FlaggedPoint (F circomPrime))
    (hall : Assumptions (eval env input))
    (ih_valid : (eval env accPrev).Valid)
    (ih_dec : decodePoint (eval env accPrev) = specAcc (eval env input) pos)
    (h_step :
      GLVStepLastLow.circuit.Assumptions
          (eval env (stepInput input accPrev ⟨pos, hpos⟩)) →
        GLVStepLastLow.circuit.Spec
          (eval env (stepInput input accPrev ⟨pos, hpos⟩))
          (eval env outVar)) :
    (eval env outVar).isInf =
      if specAcc (eval env input) (pos + 1) = .infinity then 1 else 0 := by
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  have hsass : GLVStepLastLow.circuit.Assumptions
      (eval env (stepInput input accPrev ⟨pos, hpos⟩)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stepInput, circuit_norm] using ih_valid
    · intro j
      simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
        tableEntry, circuit_norm] using htab j
    · intro j
      simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
        using htabCanon j
    · simpa only [stepInput, circuit_norm] using
        hm3 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm2 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm1 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm0 ⟨coeffBits - 1 - pos, by simp only [coeffBits] at hpos ⊢; omega⟩
  obtain ⟨hnib, hflag⟩ := h_step hsass
  have hnib' : nibbleAt (eval env input) pos hpos < 16 := by
    simpa only [GLVStep.nibble, GLVStep.toLk, VarLookup.nibble, stepInput,
      nibbleAt, circuit_norm] using hnib
  have hflag' :
      (eval env outVar).isInf =
        if add curve (GLVStep.dbl (decodePoint (eval env accPrev)))
            (decodePoint
              (tableEntry (eval env input) (nibbleAt (eval env input) pos hpos) hnib')) =
          .infinity then 1 else 0 := by
    simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry,
      GLVStep.nibble, VarLookup.nibble, stepInput, tableEntry, nibbleAt,
      circuit_norm] using hflag
  rw [hflag', ih_dec, specAcc, dif_pos hpos]
  unfold selectedAt
  rw [dif_pos hnib']

/-- Relating the VarLookup nibble on the seed input to `nibbleAt _ 0`. -/
lemma nibble_lk0 (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime)) :
    VarLookup.nibble (eval env (lk0Input input)) =
      nibbleAt (eval env input) 0 (by simp only [coeffBits]; omega) := by
  simp only [VarLookup.nibble, lk0Input, nibbleAt, Nat.sub_zero, circuit_norm]

lemma entry_lk0 (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (i : ℕ) (h : i < 16) :
    VarLookup.entry (eval env (lk0Input input)) i h = tableEntry (eval env input) i h := by
  simp only [VarLookup.entry, lk0Input, tableEntry, circuit_norm]

lemma tableEntry_index_congr (input : Inputs (F circomPrime)) (i j : ℕ) (hi : i < 16) (hj : j < 16)
    (h : i = j) : tableEntry input i hi = tableEntry input j hj := by subst h; rfl

-- The VarLookup seed satisfies the invariant for index 1.
lemma seed_ok (input : Var Inputs (F circomPrime)) (i₀ : ℕ)
    (env : Environment (F circomPrime))
    (hall : Assumptions (eval env input))
    (h_lk : VarLookup.circuit.Spec (eval env (lk0Input input)) (eval env (accVar i₀ 1))) :
    (eval env (accVar i₀ 1)).Valid ∧
      decodePoint (eval env (accVar i₀ 1)) = specAcc (eval env input) 1 := by
  obtain ⟨htab, _, _, _, _, _⟩ := hall
  simp only [VarLookup.circuit, VarLookup.Spec] at h_lk
  obtain ⟨hnib, hent⟩ := h_lk
  rw [entry_lk0] at hent
  -- hent : eval env (accVar i₀ 1) = tableEntry (eval env input) N hnib   (N = VarLookup.nibble ...)
  have h0 : (0 : ℕ) < coeffBits := by simp only [coeffBits]; omega
  have hNe : VarLookup.nibble (eval env (lk0Input input)) = nibbleAt (eval env input) 0 h0 :=
    nibble_lk0 input env
  have hnib0 : nibbleAt (eval env input) 0 h0 < 16 := hNe ▸ hnib
  have hval : (eval env (accVar i₀ 1)).Valid := by
    rw [hent]; exact htab ⟨_, hnib⟩
  refine ⟨hval, ?_⟩
  -- specAcc _ 1 = selectedAt _ 0 = decode (tableEntry _ (nibbleAt _ 0) _)
  have hspec1 : specAcc (eval env input) 1 =
      decodePoint (tableEntry (eval env input) (nibbleAt (eval env input) 0 h0) hnib0) := by
    show (if hk : (0 : ℕ) < coeffBits then
        add curve (GLVStep.dbl (specAcc (eval env input) 0)) (selectedAt (eval env input) 0 hk)
      else specAcc (eval env input) 0) = _
    rw [dif_pos h0]
    show add curve (GLVStep.dbl GroupPoint.infinity) (selectedAt (eval env input) 0 h0) = _
    have add_inf_left : ∀ P : GroupPoint Fp, add curve .infinity P = P := fun _ => rfl
    rw [GLVStep.dbl, add_inf_left, add_inf_left]
    unfold selectedAt
    rw [dif_pos hnib0]
  rw [hent, hspec1,
    tableEntry_index_congr (eval env input) _ _ hnib hnib0 hNe]

/-- Invariant: after seeding + `j` fold steps the accumulator decodes to `specAcc _ (j+1)`. -/
lemma fold_invariant (input : Var Inputs (F circomPrime)) (i₀ : ℕ)
    (env : Environment (F circomPrime))
    (hall : Assumptions (eval env input))
    (h_seed : (eval env (accVar i₀ 1)).Valid ∧
      decodePoint (eval env (accVar i₀ 1)) = specAcc (eval env input) 1)
    (h_steps : ∀ i : Fin 62,
      GLVStep.circuit.Assumptions
          (eval env (stepInput input (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)) →
        GLVStep.circuit.Spec
          (eval env (stepInput input (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩))
          (eval env (GLVStep.outputAt (i₀ + 122 + i.val * 2149)))) :
    ∀ j, j + 1 ≤ coeffBits - 1 →
      (eval env (accVar i₀ (j + 1))).Valid ∧
      decodePoint (eval env (accVar i₀ (j + 1))) = specAcc (eval env input) (j + 1) := by
  intro j
  induction j with
  | zero => intro _; exact h_seed
  | succ j ih =>
      intro hle
      have hj : j < 62 := by simp only [coeffBits] at hle; omega
      obtain ⟨ihv, ihd⟩ := ih (by omega)
      have hpos : j + 1 < coeffBits := by simp only [coeffBits] at hle ⊢; omega
      simpa only [accVar, if_pos hj] using
        glvstep_transition input env (j + 1) hpos
          (accVar i₀ (j + 1)) (GLVStep.outputAt (i₀ + 122 + j * 2149))
          hall ihv ihd (h_steps ⟨j, hj⟩)

/-- Assumptions for the VarLookup seed follow from the top-bit IsBool + table validity. -/
lemma lk0_assumptions (input : Var Inputs (F circomPrime)) (env : Environment (F circomPrime))
    (hall : Assumptions (eval env input)) :
    VarLookup.circuit.Assumptions (eval env (lk0Input input)) := by
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  simp only [VarLookup.circuit, VarLookup.Assumptions]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [lk0Input, circuit_norm] using
      hm3 ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩
  · simpa only [lk0Input, circuit_norm] using
      hm2 ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩
  · simpa only [lk0Input, circuit_norm] using
      hm1 ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩
  · simpa only [lk0Input, circuit_norm] using
      hm0 ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩
  · intro j
    simpa only [entry_lk0] using htab j
  · intro j
    simpa only [entry_lk0] using htabCanon j

lemma foldl_output_eq_accVar (input : Var Inputs (F circomPrime)) (i₀ : ℕ) :
    (main input).output i₀ = accVar i₀ coeffBits := by
  unfold main
  simp only [circuit_norm, GLVStep.output_eq_outputAt, GLVStep.localLength,
    GLVStepLastLow.output_eq, varLookup_localLength, varLookup_output_seed,
    fin_foldl_eq_accVar]
  show GLVStepLastLow.outputAt (i₀ + 122 + 62 * 2149) = accVar i₀ coeffBits
  rfl

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main :=
  { elaboratedNaive with
    output := fun _ i₀ => accVar i₀ coeffBits
    output_eq := foldl_output_eq_accVar }

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start_core
  have hall : Assumptions (eval env input_var) := by
    rw [h_input]
    exact h_assumptions
  simp only [main, circuit_norm] at h_holds
  obtain ⟨h_lk, h_fold, h_last⟩ := h_holds
  simp only [varLookup_localLength, varLookup_output_seed, foldlAcc_eq_accVar,
    GLVStep.localLength, GLVStep.output_eq_outputAt] at h_fold
  have h_lk_spec : VarLookup.circuit.Spec (eval env (lk0Input input_var)) (eval env (accVar i₀ 1)) := by
    have := h_lk (by simpa only [circuit_norm] using lk0_assumptions input_var env hall)
    simp only [varLookup_output] at this
    rw [show accVar i₀ 1 = varFromOffset FlaggedPoint (i₀ + 112) from rfl]
    convert this using 2 <;> simp only [circuit_norm]
  have h_seed : (eval env (accVar i₀ 1)).Valid ∧
      decodePoint (eval env (accVar i₀ 1)) = specAcc (eval env input_var) 1 :=
    seed_ok input_var i₀ env hall h_lk_spec
  have hsteps : ∀ i : Fin 62,
      GLVStep.circuit.Assumptions
          (eval env (stepInput input_var (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)) →
        GLVStep.circuit.Spec
          (eval env (stepInput input_var (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩))
          (eval env (GLVStep.outputAt (i₀ + 122 + i.val * 2149))) := by
    intro i
    simpa only [circuit_norm] using h_fold i
  obtain ⟨hprevv, hprevd⟩ :=
    fold_invariant input_var i₀ env hall h_seed hsteps 62 (by simp only [coeffBits]; omega)
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  have h_last_ass :
      GLVStepLastLow.circuit.Assumptions
        (eval env (stepInput input_var (accVar i₀ 63)
          ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stepInput, circuit_norm] using hprevv
    · intro j
      simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
        tableEntry, circuit_norm] using htab j
    · intro j
      simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
        using htabCanon j
    · simpa only [stepInput, circuit_norm] using
        hm3 ⟨0, by simp only [coeffBits]; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm2 ⟨0, by simp only [coeffBits]; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm1 ⟨0, by simp only [coeffBits]; omega⟩
    · simpa only [stepInput, circuit_norm] using
        hm0 ⟨0, by simp only [coeffBits]; omega⟩
  have h_last_spec :
      GLVStepLastLow.circuit.Spec
        (eval env (stepInput input_var (accVar i₀ 63)
          ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩))
        (eval env (accVar i₀ coeffBits)) := by
    have hraw := h_last (by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [varLookup_localLength, varLookup_output_seed, GLVStep.localLength,
          GLVStep.output_eq_outputAt, fin_foldl_eq_accVar_62, stepInput,
          circuit_norm] using hprevv
      · intro j
        simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
          tableEntry, circuit_norm] using htab j
      · intro j
        simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
          using htabCanon j
      · simpa only [stepInput, circuit_norm] using
          hm3 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm2 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm1 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm0 ⟨0, by simp only [coeffBits]; omega⟩)
    convert hraw using 2
    · simp only [varLookup_localLength, varLookup_output_seed, GLVStep.localLength,
        GLVStep.output_eq_outputAt, fin_foldl_eq_accVar_62, stepInput, circuit_norm]
    · simp only [glvStepLast_circuit_output_eq, varLookup_localLength,
        varLookup_output_seed, GLVStep.localLength, GLVStep.output_eq_outputAt,
        fin_foldl_eq_accVar_62, lastStepOffset_simp_eq, lastStepOutputAt_eq_accVar,
        circuit_norm]
  have hout :=
    glvstepLast_transition input_var env (coeffBits - 1)
      (by simp only [coeffBits]; omega) (accVar i₀ 63) (accVar i₀ coeffBits)
      ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ hprevv hprevd (fun _ => h_last_spec)
  change Spec input (eval env (accVar i₀ coeffBits)) ∧ _
  refine ⟨?_, ?_⟩
  · simpa only [Spec, h_input] using hout
  · simp only [main, circuit_norm]
    refine ⟨?_, ?_, ?_⟩
    · exact Or.inl rfl
    · intro i
      exact Or.inl rfl
    · exact Or.inl rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start_core
  have h_input' : eval env.toEnvironment input_var = input := by
    simpa only [CircuitType.eval_expression_prover_to_verifier (M := Inputs)] using h_input
  have hall : Assumptions (eval env.toEnvironment input_var) := by
    rw [h_input']
    exact h_assumptions
  simp only [main, circuit_norm] at h_env ⊢
  obtain ⟨h_lk_env, h_fold_env, _h_last_env⟩ := h_env
  simp only [varLookup_localLength, varLookup_output_seed, foldlAcc_eq_accVar,
    GLVStep.localLength, GLVStep.output_eq_outputAt, fin_foldl_eq_accVar_62] at h_fold_env ⊢
  have h_lk_spec : VarLookup.circuit.Spec (eval env.toEnvironment (lk0Input input_var))
      (eval env.toEnvironment (accVar i₀ 1)) := by
    have := h_lk_env (by simpa only [circuit_norm] using lk0_assumptions input_var env.toEnvironment hall)
    simp only [varLookup_output] at this
    rw [show accVar i₀ 1 = varFromOffset FlaggedPoint (i₀ + 112) from rfl]
    convert this using 2 <;> simp only [circuit_norm]
  have h_seed : (eval env.toEnvironment (accVar i₀ 1)).Valid ∧
      decodePoint (eval env.toEnvironment (accVar i₀ 1)) = specAcc (eval env.toEnvironment input_var) 1 :=
    seed_ok input_var i₀ env.toEnvironment hall h_lk_spec
  have hsteps : ∀ i : Fin 62,
      GLVStep.circuit.Assumptions
          (eval env.toEnvironment (stepInput input_var (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)) →
        GLVStep.circuit.Spec
          (eval env.toEnvironment (stepInput input_var (accVar i₀ (i.val + 1))
            ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩))
          (eval env.toEnvironment (GLVStep.outputAt (i₀ + 122 + i.val * 2149))) := by
    intro i
    simpa only [circuit_norm] using h_fold_env i
  have hinv := fold_invariant input_var i₀ env.toEnvironment hall h_seed hsteps
  obtain ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩ := hall
  refine ⟨?_, ?_, ?_⟩
  · simpa only [circuit_norm] using lk0_assumptions input_var env.toEnvironment
      ⟨htab, htabCanon, hm0, hm1, hm2, hm3⟩
  · intro i
    obtain ⟨hacc, -⟩ := hinv i.val (by have := i.isLt; simp only [coeffBits] at this ⊢; omega)
    have hsass : GLVStep.circuit.Assumptions
        (eval env.toEnvironment (stepInput input_var (accVar i₀ (i.val + 1))
          ⟨i.val + 1, by have := i.isLt; simp only [coeffBits]; omega⟩)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [stepInput, circuit_norm] using hacc
      · intro j
        simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
          tableEntry, circuit_norm] using htab j
      · intro j
        simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
          using htabCanon j
      · simpa only [stepInput, circuit_norm] using
          hm3 ⟨coeffBits - 1 - (i.val + 1), by have := i.isLt; simp only [coeffBits] at this ⊢; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm2 ⟨coeffBits - 1 - (i.val + 1), by have := i.isLt; simp only [coeffBits] at this ⊢; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm1 ⟨coeffBits - 1 - (i.val + 1), by have := i.isLt; simp only [coeffBits] at this ⊢; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm0 ⟨coeffBits - 1 - (i.val + 1), by have := i.isLt; simp only [coeffBits] at this ⊢; omega⟩
    simpa only [circuit_norm] using hsass
  · obtain ⟨hacc, -⟩ := hinv 62 (by simp only [coeffBits]; omega)
    have hsass : GLVStepLastLow.circuit.Assumptions
        (eval env.toEnvironment (stepInput input_var (accVar i₀ 63)
          ⟨coeffBits - 1, by simp only [coeffBits]; omega⟩)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [stepInput, circuit_norm] using hacc
      · intro j
        simpa only [GLVStep.entry, GLVStep.toLk, VarLookup.entry, stepInput,
          tableEntry, circuit_norm] using htab j
      · intro j
        simpa only [GLVStep.toLk, VarLookup.entry, stepInput, tableEntry, circuit_norm]
          using htabCanon j
      · simpa only [stepInput, circuit_norm] using
          hm3 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm2 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm1 ⟨0, by simp only [coeffBits]; omega⟩
      · simpa only [stepInput, circuit_norm] using
          hm0 ⟨0, by simp only [coeffBits]; omega⟩
    simpa only [circuit_norm] using hsass

def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]

end GLVMSM
end Solution.Secp256k1ScalarMul
