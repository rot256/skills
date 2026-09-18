import Solution.Secp256k1ScalarMul.Lazy.Products
import Solution.Secp256k1ScalarMul.Lazy_Donor7
import Solution.Secp256k1ScalarMul.Lazy.Interval
import Solution.Secp256k1ScalarMul.Lazy.MuxVec

/-! ## merged from `Lazy/ProductsShape.lean` -/
section
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
  refine IsR1CSCirc.bind_out (IsR1CSCirc.subcircuit
    (Sparse32Mul.shape _ ⟨affine_blendE _ _ _ hx hetx, affine_blendE _ _ _ hx hetx⟩)) fun qxt => ?_
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

lemma localLength (i : Var Inputs Field) (n : ℕ) : (main i).localLength n = 78 := by
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.elaborated, Sparse32Square.circuit,
    Sparse32Square.elaborated, circuit_norm]

lemma call_output (i : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit i).output n = (main i).output n :=
  (elaborated.output_eq i n).symm

/-- Every output word of the product stage is affine (a free recombination). -/
theorem affine_call_output (i : Var Inputs Field) (n : ℕ) :
    AffineW ((subcircuit circuit i).output n).pa ∧ AffineW ((subcircuit circuit i).output n).pu ∧
    AffineW ((subcircuit circuit i).output n).qxt ∧ AffineW ((subcircuit circuit i).output n).sa ∧
    AffineW ((subcircuit circuit i).output n).pab ∧ AffineW ((subcircuit circuit i).output n).sb ∧
    AffineW ((subcircuit circuit i).output n).pb := by
  rw [call_output]
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.elaborated, Sparse32Square.circuit,
    Sparse32Square.elaborated, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Square.affine_outputExpr _ (affineW_mapRange_var _)
  · exact Sparse32Mul.affine_outputExpr _ (affineW_mapRange_var _)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
end

/-! ## merged from `Lazy/SquareCW.lean` -/
section
/-! Computable witnesses and output stability of `Sparse32Square` (the
`UploadPart5` versions are not imported by this tree). -/

namespace Solution.Secp256k1ScalarMul.Lazy.SquareCW

open Solution.Secp256k1ScalarMulFixedBase
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

abbrev Field := SmallSquare.Field
abbrev Coeffs := fields 8

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem output_eq (a : Var Coeffs Field) (n : ℕ) :
    (subcircuit Sparse32Square.circuit a).output n =
      Sparse32Square.outputExpr (varFromOffset (fields 9) n) := by
  simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm]

theorem computableWitnesses : Sparse32Square.circuit.ComputableWitnesses := by
  intro n a env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition a env env')
    ((Sparse32Square.main a).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [Sparse32Square.main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  exact ⟨fun _ hp => congrArg Sparse32Square.productsValue hp, fun _ => trivial, trivial⟩

theorem output_stable (a : Var Coeffs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 9 ≤ k) :
    eval env ((subcircuit Sparse32Square.circuit a).output n) =
      eval env' ((subcircuit Sparse32Square.circuit a).output n) := by
  rw [output_eq]
  let products := (varFromOffset (fields 9) n : Var (fields 9) Field)
  have hp : Vector.map (Expression.eval env.toEnvironment) products =
      Vector.map (Expression.eval env'.toEnvironment) products := by
    apply Vector.ext
    intro row hr
    simp only [products, circuit_norm]
    exact hag (n + row) (by omega)
  have ho : Vector.map (Expression.eval env.toEnvironment) (Sparse32Square.outputExpr products) =
      Vector.map (Expression.eval env'.toEnvironment) (Sparse32Square.outputExpr products) :=
    (Sparse32Square.eval_outputExpr env.toEnvironment products).trans
      ((congrArg Sparse32Square.outputValue hp).trans
        (Sparse32Square.eval_outputExpr env'.toEnvironment products).symm)
  apply Vector.ext
  intro j hj
  rw [← ProvableType.getElem_eval_fields_prover,
    ← ProvableType.getElem_eval_fields_prover]
  simpa only [Vector.getElem_map] using congrArg (fun z : Coeffs Field => z[j]) ho

end Solution.Secp256k1ScalarMul.Lazy.SquareCW
end

/-! ## merged from `Lazy/NormalizeCW.lean` -/
section
/-! Computable witnesses and output stability of `Sparse32Normalize`. -/

namespace Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize

open SmallSquare Sparse32
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    and_true, subcircuitWithAssertion,
    FormalCircuitBase.Operations.StructuralComputableWitnesses, Circuit.operations, and_true]
  exact GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
    (SmallNormalize.circuit .w32) input input n (fun _ _ h => h)
    (SmallNormalize.computableWitnesses .w32) env env'

theorem output_stable (raw : Var Emu Field) {n k : ℕ} {e e' : ProverEnvironment Field}
    (hr : eval e raw = eval e' raw) (h : e.AgreesBelow k e') (hk : n + 252 ≤ k) :
    eval e ((main raw).output n) = eval e' ((main raw).output n) := by
  rw [output_eq]
  have hs := SmallNormalize.output_stable .w32 raw hr h hk
  simp only [circuit_norm, eval_balanceExpr] at hs ⊢
  rw [hs]

theorem call_output_stable (raw : Var Emu Field) {n k : ℕ} {e e' : ProverEnvironment Field}
    (hr : eval e raw = eval e' raw) (h : e.AgreesBelow k e') (hk : n + 252 ≤ k) :
    eval e ((circuit raw).output n) = eval e' ((circuit raw).output n) := by
  rw [call_output]; exact output_stable raw hr h hk

end Solution.Secp256k1ScalarMulFixedBase.Sparse32Normalize
end

/-! ## merged from `Lazy/MuxVecCW.lean` -/
section
/-! Computable witnesses and output stability of the vector mux. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec

open SmallSquare Sparse32 SparseX
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  exact ⟨fun _ hp => by rw [hp], fun _ => trivial, trivial⟩

theorem call_output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {e e' : ProverEnvironment Field} (hag : e.AgreesBelow k e') (hk : n + 8 ≤ k) :
    eval e ((subcircuit circuit i).output n) = eval e' ((subcircuit circuit i).output n) := by
  rw [call_output, ProvableType.eval_varFromOffset_prover, ProvableType.eval_varFromOffset_prover]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange]
  exact hag (n + j) (by change j < 8 at hj; omega)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec
end

/-! ## merged from `Lazy/ProductsCW.lean` -/
section
/-! Computable witnesses and output stability of the seven-product circuit. -/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products

open SmallSquare Sparse32 SparseX
open Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas


set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem input_eval_eq (i : Var Inputs Field) {e e' : ProverEnvironment Field}
    (h : eval e i = eval e' i) :
    Vector.map (Expression.eval e.toEnvironment) i.a =
        Vector.map (Expression.eval e'.toEnvironment) i.a ∧
    Vector.map (Expression.eval e.toEnvironment) i.b =
        Vector.map (Expression.eval e'.toEnvironment) i.b ∧
    Vector.map (Expression.eval e.toEnvironment) i.x =
        Vector.map (Expression.eval e'.toEnvironment) i.x ∧
    Vector.map (Expression.eval e.toEnvironment) i.y =
        Vector.map (Expression.eval e'.toEnvironment) i.y ∧
    Vector.map (Expression.eval e.toEnvironment) i.tx =
        Vector.map (Expression.eval e'.toEnvironment) i.tx ∧
    Vector.map (Expression.eval e.toEnvironment) i.ty =
        Vector.map (Expression.eval e'.toEnvironment) i.ty := by
  exact ⟨by simpa only [circuit_norm] using congrArg Inputs.a h,
    by simpa only [circuit_norm] using congrArg Inputs.b h,
    by simpa only [circuit_norm] using congrArg Inputs.x h,
    by simpa only [circuit_norm] using congrArg Inputs.y h,
    by simpa only [circuit_norm] using congrArg Inputs.tx h,
    by simpa only [circuit_norm] using congrArg Inputs.ty h⟩

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro n input env env'
  change Operations.forAllFlat n
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations n)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  simp only [main, Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    apply FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    rotate_left
    first
    | exact Solution.Secp256k1ScalarMul.Lazy.SquareCW.computableWitnesses
    | exact Sparse32Mul.computableWitnesses
  all_goals
    intro k e e' hk hag hp
    obtain ⟨ha, hb, hx, hy, htx, hty⟩ := input_eval_eq input hp
    simp only [xSExpr, xPExpr, circuit_norm, map_vaddE, map_vsubE, map_blendE, map_embedExpr,
      ha, hb, hx, hy, htx, hty]
  all_goals
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated,
      Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm] at hk
    have hsa := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable input.a (n + 12 + 12 + 12) hag (by omega)
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] at hsa
    simp only [Sparse32Square.circuit, Sparse32Square.elaborated,
      Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm, hsa]
  have hsb := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable input.b (n + 12 + 12 + 12 + 9 + 12) hag (by omega)
  simp only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] at hsb
  simp only [hsb]

lemma mul_reconstruction_stable (n : ℕ) {k : ℕ} {env env' : ProverEnvironment Field}
    (hag : env.AgreesBelow k env') (hk : n + 12 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment)
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := n + j })) =
      Vector.map (Expression.eval env'.toEnvironment)
        (Sparse32Mul.outputExpr (Vector.mapRange 12 fun j => var { index := n + j })) := by
  have h := Sparse32Mul.output_stable ⟨default, default⟩ n hag hk
  simpa only [Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm] using h

lemma square_reconstruction_stable (n : ℕ) {k : ℕ} {env env' : ProverEnvironment Field}
    (hag : env.AgreesBelow k env') (hk : n + 9 ≤ k) :
    Vector.map (Expression.eval env.toEnvironment)
        (Sparse32Square.outputExpr (Vector.mapRange 9 fun j => var { index := n + j })) =
      Vector.map (Expression.eval env'.toEnvironment)
        (Sparse32Square.outputExpr (Vector.mapRange 9 fun j => var { index := n + j })) := by
  have h := Solution.Secp256k1ScalarMul.Lazy.SquareCW.output_stable default n hag hk
  simpa only [Sparse32Square.circuit, Sparse32Square.elaborated, circuit_norm] using h

theorem output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 78 ≤ k) : eval env ((main i).output n) = eval env' ((main i).output n) := by
  simp only [main, Sparse32Square.circuit, Sparse32Square.elaborated,
    Sparse32Mul.circuit, Sparse32Mul.elaborated, circuit_norm, Outputs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact mul_reconstruction_stable _ hag (by omega)
    | exact square_reconstruction_stable _ hag (by omega)

theorem call_output_stable (i : Var Inputs Field) (n : ℕ) {k : ℕ}
    {env env' : ProverEnvironment Field} (hag : env.AgreesBelow k env')
    (hk : n + 78 ≤ k) :
    eval env ((subcircuit circuit i).output n) = eval env' ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact output_stable i n hag hk

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
end
