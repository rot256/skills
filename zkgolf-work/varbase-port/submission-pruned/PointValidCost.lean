import Solution.Secp256k1ScalarMul.PointValid
import Solution.Secp256k1ScalarMul.Cost
import Solution.Secp256k1ScalarMul.MulModSqN32Cost

namespace Solution.Secp256k1ScalarMul
namespace PointValidCost

open Challenge.CostR1CS
open Cost

def pointValidCount : Count := ⟨1046, 1062⟩

theorem costIs_validPBytes (x : Var Emu (F circomPrime)) :
    CostIs (ValidPBytes.main x) ⟨260, 265⟩ := by
  simpa only [ValidPBytes.main, ValidP.main, Circuit.operations] using
    Cost.costIs_validP x

theorem costIs_sub_validPBytes (x : Var Emu (F circomPrime)) :
    CostIs (ValidPBytes.circuit x) ⟨260, 265⟩ :=
  CostIs.subcircuitWithAssertion (fun n => costIs_validPBytes x n)

theorem costIs_main (P : Var FlaggedPoint (F circomPrime)) :
    CostIs (PointValid.main P) pointValidCount := by
  obtain ⟨x, y, isInf⟩ := P
  rw [show pointValidCount
      = ⟨0, 1⟩ +
        (⟨260, 265⟩ +
          (⟨260, 265⟩ +
            (mulModSqN32Cost +
              (⟨7, 7⟩ +
                (mulModFoldTInvCost + ⟨0, 1⟩))))) from by decide]
  unfold PointValid.main
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_sub_validPBytes _) fun _ => ?_
  refine CostIs.bind (costIs_sub_validPBytes _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModSqN32 _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_assertion (P : Var FlaggedPoint (F circomPrime)) :
    CostIs (PointValid.circuit P) pointValidCount :=
  CostIs.subcircuitWithAssertion (fun n => costIs_main P n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CS_validPBytes (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ValidPBytes.main x) := by
  simpa only [ValidPBytes.main, ValidP.main, Circuit.operations] using
    Cost.isR1CS_validP x hx

theorem isR1CS_sub_validPBytes (x : Var Emu (F circomPrime))
    (hx : AffineW x) :
    IsR1CSCirc (ValidPBytes.circuit x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun n => isR1CS_validPBytes x hx n)

theorem affine_byteFromBits
    (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (hb0 : AffineW b0) (hb1 : AffineW b1)
    (hb2 : AffineW b2) (hb3 : AffineW b3)
    (t : Fin coordBytes) :
    Affine (ValidPBytes.byteFromBits b0 b1 b2 b3 t) := by
  unfold ValidPBytes.byteFromBits
  refine affine_finFoldl' _ _ Affine.zero fun acc j hacc => ?_
  apply Affine.add hacc
  apply Affine.mul_deg0
  · split_ifs
    · apply hb0
    · apply hb1
    · apply hb2
    · apply hb3
  · exact degree_const _

theorem affineW_validPBytes_output
    (x : Var Emu (F circomPrime)) (hx : AffineW x) (n : ℕ) :
    AffineW (ValidPBytes.circuit.output x n) := by
  simp only [ValidPBytes.circuit, circuit_norm, ValidPBytes.elaborated]
  intro i hi
  rw [Vector.getElem_ofFn]
  apply affine_byteFromBits
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 0 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 1 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 2 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))
  · exact affineW_push_top _ _
      (Affine.fconst_mul _
        (Affine.sub (hx 3 (by decide))
          (affine_fieldFromBitsExpr _ (affineW_mapRange_var _))))

theorem affineOut_circuit (P : Var FlaggedPoint (F circomPrime))
    (hx : AffineW P.x) (hy : AffineW P.y) (n : ℕ) :
    AffineW (PointValid.circuit.output P n).x ∧
      AffineW (PointValid.circuit.output P n).y := by
  simpa only [PointValid.circuit, circuit_norm, PointValid.elaborated,
    ValidPBytes.circuit, ValidPBytes.elaborated] using
    And.intro (affineW_validPBytes_output P.x hx n)
      (affineW_validPBytes_output P.y hy (n + 260))

private theorem affineW_curveTarget
    (Pc : Var (fields (2 * numLimbs - 1)) (F circomPrime)) (hPc : AffineW Pc)
    (e : Expression (F circomPrime)) (he : Affine e) :
    AffineW (PointValid.curveTarget Pc e) := by
  intro i hi
  rw [PointValid.curveTarget, Vector.getElem_mapFinRange]
  split
  · exact Affine.add (hPc i hi)
      (Affine.mul_deg0 (Affine.sub (Affine.const 1) he) (degree_const _))
  · exact hPc i hi

theorem isR1CS_main (P : Var FlaggedPoint (F circomPrime))
    (hx : AffineW P.x) (hy : AffineW P.y) (hi : Affine P.isInf) :
    IsR1CSCirc (PointValid.main P) := by
  obtain ⟨x, y, isInf⟩ := P
  unfold PointValid.main
  refine IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul hi (Affine.sub hi (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_validPBytes _ hx) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_validPBytes _ hy) fun _ => ?_
  have hb32 : ∀ n : ℕ, AffineW (Bytes32.ofBytes (ValidPBytes.circuit.output x n)) :=
    fun n => Bytes32.affineW_ofBytes (affineW_validPBytes_output x hx n)
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_mulModSqN32 _ (hb32 _) (hb32 _)) fun nx2 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (Cost.affineW_sub_mulModSqN32 _ nx2) hx) fun nPc => ?_
  refine IsR1CSCirc.bind
    (isR1CS_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _ hy hy
      (affineW_curveTarget _ (affineW_interpolatedMul_output _ _ _) _ hi)) fun _ => ?_
  have hiSum : Affine (x[0] + x[1] + x[2] + x[3] +
      y[0] + y[1] + y[2] + y[3]) :=
    Affine.add (Affine.add (Affine.add (Affine.add (Affine.add (Affine.add
      (Affine.add (hx 0 (by decide)) (hx 1 (by decide)))
      (hx 2 (by decide))) (hx 3 (by decide))) (hy 0 (by decide)))
      (hy 1 (by decide))) (hy 2 (by decide))) (hy 3 (by decide))
  refine IsR1CSCirc.bind
    (IsR1CSCirc.assertZero (isR1CSRow_mul hi hiSum)) fun _ =>
    IsR1CSCirc.pure _

theorem isR1CS_assertion (P : Var FlaggedPoint (F circomPrime))
    (hx : AffineW P.x) (hy : AffineW P.y) (hi : Affine P.isInf) :
    IsR1CSCirc (PointValid.circuit P) :=
  IsR1CSCirc.subcircuitWithAssertion (fun n => isR1CS_main P hx hy hi n)

end PointValidCost
end Solution.Secp256k1ScalarMul
