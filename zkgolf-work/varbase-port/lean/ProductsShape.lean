import Solution.Secp256k1ScalarMul.Lazy.Products

/-! R1CS shape and local length of the product stage.  The `Sparse32Square`
shape lemmas are patchgravity's (d59c8bf7, `UploadPart5`), reproduced here
because that file is not on this solution's import path. -/

namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Square

open SmallSquare Sparse32 Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

private theorem affine_foldl_linear' :
    ∀ {n : ℕ} (coeff : Fin n → Field) (a : Fin n → Expression Field)
      (init : Expression Field), Affine init → (∀ i, Affine (a i)) →
      Affine (Fin.foldl n (fun acc i => acc + coeff i * a i) init)
  | 0, _, _, _, hinit, _ => by simpa using hinit
  | n + 1, coeff, a, init, hinit, ha => by
      rw [Fin.foldl_succ_last]
      exact Affine.add
        (affine_foldl_linear' (fun i => coeff i.castSucc) (fun i => a i.castSucc)
          init hinit (fun i => ha i.castSucc))
        (Affine.fconst_mul _ (ha (Fin.last n)))

lemma affine_linearExpr (row : Fin 8 → Field) (a : Var Inputs Field)
    (ha : AffineW a) : Affine (linearExpr row a) := by
  apply affine_foldl_linear' row (fun i => a[i.val]) 0 Affine.zero
  intro i
  exact ha i.val i.isLt

lemma affine_leftExpr (a : Var Inputs Field) (row : Fin 9) (ha : AffineW a) :
    Affine (leftExpr a row) :=
  affine_linearExpr _ _ ha

lemma affine_rightExpr (a : Var Inputs Field) (row : Fin 9) (ha : AffineW a) :
    Affine (rightExpr a row) :=
  affine_linearExpr _ _ ha

lemma affine_outputExpr (products : Var (fields 9) Field) (hp : AffineW products) :
    AffineW (outputExpr products) := by
  intro k hk
  rw [outputExpr, Vector.getElem_ofFn]
  apply affine_foldl_linear' (squareOut ⟨k, hk⟩) (fun row => products[row.val]) 0 Affine.zero
  intro row
  exact hp row.val row.isLt

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem shape (a : Var Inputs Field) (ha : AffineW a) : IsR1CSCirc (main a) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nproducts => ?_
  have hp := affineW_provableWitness_bigInt (k := 9)
    (fun env => productsValue (eval env a)) nproducts
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression Field) fun row k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_sub (affine_leftExpr a row ha)
    (affine_rightExpr a row ha) (hp row.val row.isLt)

theorem output_eq (a : Var Inputs Field) (n : ℕ) :
    (main a).output n = outputExpr (varFromOffset (fields 9) n) := by
  simp only [main, circuit_norm]

theorem call_output (a : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit a).output n = (main a).output n :=
  (elaborated.output_eq a n).symm

theorem affine_call_output (a : Var Inputs Field) (n : ℕ) :
    AffineW ((subcircuit circuit a).output n) := by
  rw [call_output, output_eq]
  exact affine_outputExpr _ (affineW_mapRange_var _)

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Square

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS
attribute [local irreducible] Sparse32Mul.outputExpr Sparse32Square.outputExpr

def AffineInput (i : Var Inputs Field) : Prop :=
  AffineW i.a ∧ AffineW i.b ∧ AffineW i.x ∧ AffineW i.y ∧ AffineW i.tx ∧ AffineW i.ty

theorem shape (i : Var Inputs Field) (hi : AffineInput i) : IsR1CSCirc (main i) := by
  obtain ⟨ha, hb, hx, hy, htx, hty⟩ := hi
  have hetx := affine_embedExpr i.tx htx
  have hety := affine_embedExpr i.ty hty
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨ha, affine_vsubE _ _ hetx hx⟩)) fun pa => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨ha, affine_vaddE _ _ hy hety⟩)) fun pu => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit (Sparse32Square.shape _ hx)) fun sx => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨hx, hetx⟩)) fun pxt => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit (Sparse32Square.shape _ hetx)) fun st => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit (Sparse32Square.shape _ ha)) fun sa => ?_
  have hsa := Sparse32Square.affine_call_output i.a sa
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨affine_vaddE _ _ ha hb,
      affine_vsubE _ _ hx (affine_vsubE _ _ (affine_vsubE _ _ hsa hx) hetx)⟩)) fun pab => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit (Sparse32Square.shape _ hb)) fun sb => ?_
  have hsb := Sparse32Square.affine_call_output i.b sb
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨hb,
      affine_vsubE _ _ hx (affine_vaddE _ _ (affine_vsubE _ _ hsb hsa) hetx)⟩)) fun pb => ?_
  exact IsR1CSCirc.pure _

theorem shape_call (i : Var Inputs Field) (hi : AffineInput i) :
    IsR1CSCirc (subcircuit circuit i) :=
  IsR1CSCirc.subcircuit (fun n => shape i hi n)

lemma localLength (i : Var Inputs Field) (n : ℕ) : (main i).localLength n = 96 := by
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.elaborated, Sparse32Square.circuit,
    Sparse32Square.elaborated, circuit_norm]

lemma call_output (i : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit i).output n = (main i).output n :=
  (elaborated.output_eq i n).symm

/-- Every output word of the product stage is affine (a free recombination). -/
theorem affine_call_output (i : Var Inputs Field) (n : ℕ) :
    AffineW ((subcircuit circuit i).output n).pa ∧ AffineW ((subcircuit circuit i).output n).pu ∧
    AffineW ((subcircuit circuit i).output n).sx ∧ AffineW ((subcircuit circuit i).output n).pxt ∧
    AffineW ((subcircuit circuit i).output n).st ∧ AffineW ((subcircuit circuit i).output n).sa ∧
    AffineW ((subcircuit circuit i).output n).pab ∧ AffineW ((subcircuit circuit i).output n).sb ∧
    AffineW ((subcircuit circuit i).output n).pb := by
  rw [call_output]
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.elaborated, Sparse32Square.circuit,
    Sparse32Square.elaborated, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
