import Solution.Secp256k1ScalarMul.MulModVariants
import Solution.Secp256k1ScalarMul.Cost

namespace Solution.Secp256k1ScalarMul
namespace Cost

open Challenge.CostR1CS

section
variable {m : ℕ}

def mulModLooseCount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ + (⟨m * (B - 1), m * B⟩ +
    (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩ + Count.zero)))))

theorem costIs_mulModLoose (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulModLoose.main P gf posOf G V VR hgv input) (mulModLooseCount m P.B V.Wf G) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModLoose.main mulModLooseCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModLoose (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (subcircuit
        (MulModLoose.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b)
      (mulModLooseCount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.subcircuit
    (fun n => costIs_mulModLoose secpParams gfMul posOfMul 5 vMul vMul hgvMul b n)

theorem isR1CS_mulModLoose (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0) :
    IsR1CSCirc (MulModLoose.main P gf posOf G V VR hgv input) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModLoose.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_interpolatedMul_output input.a input.b _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulModLoose (b : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0) :
    IsR1CSCirc
      (subcircuit
        (MulModLoose.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b) :=
  IsR1CSCirc.subcircuit
    (fun n => isR1CS_mulModLoose secpParams gfMul posOfMul 5 vMul vMul hgvMul b ha hb hn hnd n)

theorem affineW_sub_mulModLoose (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) (n : ℕ) :
    AffineW
      ((subcircuit
        (MulModLoose.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output
        n) := by
  have h : ((subcircuit
        (MulModLoose.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output n)
      = varFromOffset (BigInt numLimbs) (n + numLimbs) := by
    simp only [circuit_norm, subcircuit, MulModLoose.circuit, MulModLoose.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

theorem costIs_sub_mulModLooseWideB (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (subcircuit
        (MulModLoose.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b)
      (mulModLooseCount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.subcircuit
    (fun n => costIs_mulModLoose secpParams gfMul posOfMul 5 vMul vMul hgvMul b n)

theorem isR1CS_sub_mulModLooseWideB (b : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0) :
    IsR1CSCirc
      (subcircuit
        (MulModLoose.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b) :=
  IsR1CSCirc.subcircuit
    (fun n => isR1CS_mulModLoose secpParams gfMul posOfMul 5 vMul vMul hgvMul b ha hb hn hnd n)

theorem affineW_sub_mulModLooseWideB (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) (n : ℕ) :
    AffineW
      ((subcircuit
        (MulModLoose.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output
        n) := by
  have h : ((subcircuit
        (MulModLoose.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output n)
      = varFromOffset (BigInt numLimbs) (n + numLimbs) := by
    simp only [circuit_norm, subcircuit, MulModLoose.circuitWideB, MulModLoose.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ### Constant-`a` variant: no interpolated multiply. -/

def mulModLooseCACount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ + (⟨m * (B - 1), m * B⟩ +
    (⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩ + Count.zero))))

theorem costIs_mulModLooseCA (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulModLooseCA.main P gf posOf G V VR hgv input) (mulModLooseCACount m P.B V.Wf G) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModLooseCA.main mulModLooseCACount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind
    (costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_mulModLooseCA (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (had : ∀ j (hj : j < m), degree input.a[j] = 0) (hb : AffineW input.b)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0) :
    IsR1CSCirc (MulModLooseCA.main P gf posOf G V VR hgv input) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModLooseCA.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_bigIntMulNoReduce_constA input.a input.b had hb
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi
  exact IsR1CSCirc.pure _

theorem costIs_sub_mulModLooseWideBCA (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (subcircuit
        (MulModLooseCA.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b)
      (mulModLooseCACount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.subcircuit
    (fun n => costIs_mulModLooseCA secpParams gfMul posOfMul 5 vMul vMul hgvMul b n)

theorem isR1CS_sub_mulModLooseWideBCA (b : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (had : ∀ j (hj : j < numLimbs), degree b.a[j] = 0) (hb : AffineW b.b)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0) :
    IsR1CSCirc
      (subcircuit
        (MulModLooseCA.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b) :=
  IsR1CSCirc.subcircuit
    (fun n => isR1CS_mulModLooseCA secpParams gfMul posOfMul 5 vMul vMul hgvMul b had hb hnd n)

theorem affineW_sub_mulModLooseWideBCA (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) (n : ℕ) :
    AffineW
      ((subcircuit
        (MulModLooseCA.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul)
          b).output n) := by
  have h : ((subcircuit
        (MulModLooseCA.circuitWideB secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul)
          b).output n)
      = varFromOffset (BigInt numLimbs) (n + numLimbs) := by
    simp only [circuit_norm, subcircuit, MulModLooseCA.circuitWideB, MulModLooseCA.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

end

end Cost
end Solution.Secp256k1ScalarMul
