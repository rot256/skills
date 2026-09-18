import Solution.Secp256k1ScalarMul.Lazy_Interval

/-!
# Boolean select of an eight-word vector: `out = if sel = 1 then v else u`

Eight rank-1 rows `out_k = u_k + sel (v_k − u_k)`; used for the output muxes
of the chain step (cancellation, infinity and zeroing branches).
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec

open SmallSquare Challenge.CostR1CS Cost
open Challenge.Utils.ComputableWitnessLemmas

set_option autoImplicit false

structure Inputs (F : Type) where
  sel : F
  u : fields 8 F
  v : fields 8 F
deriving ProvableStruct

def main (i : Var Inputs Field) : Circuit Field (Var (fields 8) Field) := do
  let out ← ProvableType.witness (α := fields 8) fun env =>
    let iv : Inputs Field := eval env i
    if iv.sel = 1 then iv.v else iv.u
  Circuit.forEach (Vector.ofFn fun k : Fin 8 =>
    i.u[k.val] + i.sel * (i.v[k.val] - i.u[k.val]) - out[k.val]) assertZero
  return out

instance elaborated : ElaboratedCircuit Field Inputs (fields 8) main := by
  elaborate_circuit

def Assumptions (i : Inputs Field) : Prop := IsBool i.sel

def Spec (i : Inputs Field) (o : fields 8 Field) : Prop :=
  o = if i.sel = 1 then i.v else i.u

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hs, hu, hv⟩ := h_input
  simp only [circuit_norm, Vector.getElem_ofFn] at h_holds
  apply Vector.ext
  intro k hk
  have h := h_holds ⟨k, hk⟩
  simp only [Expression.eval, circuit_norm, hs] at h
  rw [← hu, ← hv]
  rcases h_assumptions with h0 | h1
  · rw [h0] at h
    rw [h0, if_neg (zero_ne_one (α := Field))]
    simp only [circuit_norm, Vector.getElem_map]
    linear_combination -h
  · rw [h1] at h
    rw [h1, if_pos rfl]
    simp only [circuit_norm, Vector.getElem_map]
    linear_combination -h

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start
  obtain ⟨hs, hu, hv⟩ := h_input
  simp only [circuit_norm, Vector.getElem_ofFn]
  intro k
  rcases h_assumptions with h0 | h1
  · simp only [h0, zero_ne_one, ↓reduceIte] at h_env
    simp only [Expression.eval, circuit_norm, hs, h0, Vector.getElem_map, varFromOffset,
      ProvableType.toElements_fromElements, Vector.getElem_mapRange, h_env, ← hu]
    ring
  · simp only [h1, ↓reduceIte] at h_env
    simp only [Expression.eval, circuit_norm, hs, h1, Vector.getElem_map, varFromOffset,
      ProvableType.toElements_fromElements, Vector.getElem_mapRange, h_env, ← hu, ← hv]
    ring

def circuit : FormalCircuit Field Inputs (fields 8) where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem costIs_main (i : Var Inputs Field) : CostIs (main i) ⟨8, 8⟩ := by
  rw [show (⟨8, 8⟩ : Count) = ⟨8, 0⟩ + (⟨8 * 0, 8 * 1⟩ + Count.zero) by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (i : Var Inputs Field) : CostIs (subcircuit circuit i) ⟨8, 8⟩ :=
  CostIs.subcircuit (fun n => costIs_main i n)

theorem call_output (i : Var Inputs Field) (n : ℕ) :
    (subcircuit circuit i).output n = varFromOffset (fields 8) n :=
  (elaborated.output_eq i n).symm

theorem affine_call_output (i : Var Inputs Field) (n : ℕ) :
    AffineW ((subcircuit circuit i).output n) := by
  rw [call_output]
  exact affineW_varFromOffset 8 n

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec

open SmallSquare Challenge.CostR1CS Cost

set_option autoImplicit false

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem shape (i : Var Inputs Field) (hs : Affine i.sel) (hu : AffineW i.u) (hv : AffineW i.v) :
    IsR1CSCirc (main i) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun k => ?_
  have ho := affineW_provableWitness_bigInt (k := 8)
    (fun env => if (eval env i).sel = 1 then (eval env i).v else (eval env i).u) k
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression Field) fun j hj => ?_
  refine IsR1CSCirc.assertZero ?_ hj
  rw [Vector.getElem_ofFn]
  exact CompactAdd.isR1CSRow_add_mul_sub (hu _ _) hs (Affine.sub (hv _ _) (hu _ _)) (ho _ _)

theorem shape_call (i : Var Inputs Field) (hs : Affine i.sel) (hu : AffineW i.u)
    (hv : AffineW i.v) : IsR1CSCirc (subcircuit circuit i) :=
  IsR1CSCirc.subcircuit (fun n => shape i hs hu hv n)

theorem localLength (i : Var Inputs Field) (n : ℕ) : (main i).localLength n = 8 := by
  simp only [main, circuit_norm]

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.MuxVec
