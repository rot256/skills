import Solution.SHA256.Cost
import Solution.SHA256.CostPack
import Solution.SHA256.CostSparse
import Solution.SHA256.CompressBlockWideSparseD
import Solution.SHA256.CompressBlock1SparseD
import Solution.SHA256.CompressBlock5D
import Solution.SHA256.SelectDigestD
import Challenge.Utils.CostR1CS

/-!
# Cost accounting for the deferred-chain (`D`) pipeline

State words 3 (`d`) and 7 (`h`) are carried between blocks **unreduced**: their
Merkle–Damgård feed-forward is the affine `DeferAdd` gadget, which emits no
operations at all.  The two reductions are paid once, inside `SelectDigestD`.
-/

namespace Solution.SHA256
namespace CostD

open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

set_option maxRecDepth 16384

/-! ## The wide fused adders -/

theorem costIs_fusedEAdderW (input : Var FusedEAdderW.Inputs (F circomPrime)) :
    CostIs (FusedEAdderW.main input) ⟨6, 7⟩ := by
  unfold FusedEAdderW.main
  exact
    CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_fusedEAdderW (input : Var FusedEAdderW.Inputs (F circomPrime)) :
    CostIs (assertion FusedEAdderW.circuit input) ⟨6, 7⟩ :=
  CostIs.assertion (costIs_fusedEAdderW _)

theorem costIs_fusedAAdderW (input : Var FusedAAdderW.Inputs (F circomPrime)) :
    CostIs (FusedAAdderW.main input) ⟨4, 5⟩ := by
  unfold FusedAAdderW.main
  exact
    CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_fusedAAdderW (input : Var FusedAAdderW.Inputs (F circomPrime)) :
    CostIs (assertion FusedAAdderW.circuit input) ⟨4, 5⟩ :=
  CostIs.assertion (costIs_fusedAAdderW _)

/-! ## The wide round pair -/

def sha256RoundPairWCost : Count := ⟨330, 332⟩

theorem costIs_sha256RoundPairW (input : Var SHA256RoundPairW.Inputs (F circomPrime)) :
    CostIs (SHA256RoundPairW.main input) sha256RoundPairWCost := by
  unfold SHA256RoundPairW.main sha256RoundPairWCost
  exact
    CostIs.bind (Cost.costIs_sub_upperSigma1 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_upperSigma0 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_upperSigma1 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_upperSigma0 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_packedCh _) fun _ =>
    CostIs.bind (Cost.costIs_sub_packedMaj _) fun _ =>
    CostIs.bind (costIs_sub_fusedEAdderW _) fun _ =>
    CostIs.bind (costIs_sub_fusedAAdderW _) fun _ => CostIs.pure _

theorem costIs_sub_sha256RoundPairW (b : Var SHA256RoundPairW.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256RoundPairW.circuit b) sha256RoundPairWCost :=
  CostIs.subcircuit (costIs_sha256RoundPairW _)

/-! ## The 62-round loop with a wide first pair -/

def sha256Rounds60From2Cost : Count :=
  ⟨30 * Cost.sha256RoundPairCost.allocations, 30 * Cost.sha256RoundPairCost.constraints⟩

theorem costIs_sha256Rounds60_from2 (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main60_from2 input) sha256Rounds60From2Cost :=
  CostIs.foldlRange (fun _ _ n => Cost.costIs_sub_sha256RoundPair _ n)

theorem costIs_sub_sha256Rounds60_from2 (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit60_from2 b) sha256Rounds60From2Cost :=
  CostIs.subcircuit (costIs_sha256Rounds60_from2 _)

def sha256Rounds62PairedWCost : Count :=
  ⟨sha256RoundPairWCost.allocations + sha256Rounds60From2Cost.allocations,
   sha256RoundPairWCost.constraints + sha256Rounds60From2Cost.constraints⟩

theorem costIs_sha256Rounds62_pairedW (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main62_pairedW input) sha256Rounds62PairedWCost := by
  unfold SHA256Rounds63.main62_pairedW
  rw [show sha256Rounds62PairedWCost =
      sha256RoundPairWCost + sha256Rounds60From2Cost from rfl]
  exact CostIs.bind (costIs_sub_sha256RoundPairW _) fun _ =>
    costIs_sub_sha256Rounds60_from2 _

theorem costIs_sub_sha256Rounds62_pairedW (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit62_pairedW b) sha256Rounds62PairedWCost :=
  CostIs.subcircuit (costIs_sha256Rounds62_pairedW _)

/-! ## The zero-cost deferred feed-forward -/

theorem costIs_deferAdd (input : Var DeferAdd.Inputs (F circomPrime)) :
    CostIs (DeferAdd.main input) Count.zero := by
  unfold DeferAdd.main
  exact CostIs.pure _

theorem costIs_sub_deferAdd (input : Var DeferAdd.Inputs (F circomPrime)) :
    CostIs (subcircuit DeferAdd.circuit input) Count.zero :=
  CostIs.subcircuit (costIs_deferAdd _)

theorem costIs_deferAddConst (c : ℕ) (input : Var DeferAddConst.Inputs (F circomPrime)) :
    CostIs (DeferAddConst.main c input) Count.zero := by
  unfold DeferAddConst.main
  exact CostIs.pure _

theorem costIs_sub_deferAddConst (c : ℕ) (hc : c < 2^32)
    (input : Var DeferAddConst.Inputs (F circomPrime)) :
    CostIs (subcircuit (DeferAddConst.circuit c hc) input) Count.zero :=
  CostIs.subcircuit (costIs_deferAddConst c _)

/-! ## The deferred compressors -/

def compressBlockWideSparseDCost : Count := ⟨14931, 15018⟩

theorem costIs_compressBlockWideSparseD
    (input : Var CompressBlockWideSparseD.Inputs (F circomPrime)) :
    CostIs (CompressBlockWideSparseD.main input) compressBlockWideSparseDCost := by
  rw [show compressBlockWideSparseDCost =
      CostSparse.messageScheduleSparseCost46 +
      (Cost.scheduleStepLastCost + (Cost.scheduleStepLastCost +
        (sha256Rounds62PairedWCost + (Cost.tailPairWideCost +
          (Cost.carrySumAdd32Cost + (Cost.carrySumAdd32Cost + (Count.zero +
            (Cost.carrySumAdd32Cost + (Cost.carrySumAdd32Cost +
              (Count.zero + Count.zero)))))))))) from by
    simp only [compressBlockWideSparseDCost, CostSparse.messageScheduleSparseCost46,
      Cost.scheduleStepLastCost, sha256Rounds62PairedWCost, sha256RoundPairWCost,
      sha256Rounds60From2Cost, Cost.sha256RoundPairCost, Cost.sigmaCost, Cost.ch32Cost,
      Cost.packedMajCost, Cost.tailPairWideCost, Cost.carrySumAdd32Cost]; rfl]
  unfold CompressBlockWideSparseD.main
  exact
    CostIs.bind (CostSparse.costIs_sub_messageScheduleSparse46 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_scheduleStepLast _) fun _ =>
    CostIs.bind (Cost.costIs_sub_scheduleStepLast _) fun _ =>
    CostIs.bind (costIs_sub_sha256Rounds62_pairedW _) fun _ =>
    CostIs.bind (Cost.costIs_sub_tailPairWide _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (costIs_sub_deferAdd _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (costIs_sub_deferAdd _) fun _ =>
    CostIs.pure _

theorem costIs_sub_compressBlockWideSparseD
    (input : Var CompressBlockWideSparseD.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlockWideSparseD.circuit input)
      compressBlockWideSparseDCost :=
  CostIs.subcircuit (costIs_compressBlockWideSparseD input)

def compressBlock5DCost : Count := ⟨10627, 10691⟩

theorem costIs_compressBlock5D (input : Var CompressBlock5D.Inputs (F circomPrime)) :
    CostIs (CompressBlock5D.main input) compressBlock5DCost := by
  rw [show compressBlock5DCost =
      sha256Rounds62PairedWCost + (Cost.tailPairTightCost +
        (Cost.carrySumAdd32Cost + (Cost.carrySumAdd32Cost + (Count.zero +
          (Cost.carrySumAdd32Cost + (Cost.carrySumAdd32Cost +
            (Count.zero + Count.zero))))))) from by
    simp only [compressBlock5DCost, sha256Rounds62PairedWCost, sha256RoundPairWCost,
      sha256Rounds60From2Cost, Cost.sha256RoundPairCost, Cost.sigmaCost, Cost.ch32Cost,
      Cost.packedMajCost, Cost.tailPairTightCost, Cost.carrySumAdd32Cost]; rfl]
  unfold CompressBlock5D.main
  exact
    CostIs.bind (costIs_sub_sha256Rounds62_pairedW _) fun _ =>
    CostIs.bind (Cost.costIs_sub_tailPairTight _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (costIs_sub_deferAdd _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAdd32 _) fun _ =>
    CostIs.bind (costIs_sub_deferAdd _) fun _ =>
    CostIs.pure _

theorem costIs_sub_compressBlock5D (input : Var CompressBlock5D.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlock5D.circuit input) compressBlock5DCost :=
  CostIs.subcircuit (costIs_compressBlock5D input)

def compressBlock1SparseDCost : Count := ⟨14785, 14873⟩

theorem costIs_compressBlock1SparseD (input : Var SHA256Block (F circomPrime)) :
    CostIs (CompressBlock1SparseD.main input) compressBlock1SparseDCost := by
  rw [show compressBlock1SparseDCost =
      CostSparse.messageScheduleSparseCost46 +
      (Cost.scheduleStepLastCost + (Cost.scheduleStepLastCost +
        (CostSparse.sha256Rounds62Block1_pairedSparseCost + (Cost.tailPairWideCost +
          (Cost.carrySumAddOddConst32Cost + (Cost.carrySumAddMod4Const32Cost +
            (Count.zero + (Cost.carrySumAddMod8Const32Cost +
              (Cost.carrySumAddOddConst32Cost + (Count.zero + Count.zero)))))))))) from by
    simp only [compressBlock1SparseDCost, CostSparse.messageScheduleSparseCost46,
      Cost.scheduleStepLastCost, CostSparse.sha256Rounds62Block1_pairedSparseCost,
      CostSparse.round0Block1SparseCost, Cost.round1Block1Cost,
      Cost.sha256RoundPairB1Cost, Cost.sha256RoundPairCost, Cost.sigmaCost,
      Cost.ch32Cost, Cost.packedMajCost, Cost.packedMajB1Cost, Cost.tailPairWideCost,
      Cost.carrySumAddOddConst32Cost, Cost.carrySumAddMod4Const32Cost,
      Cost.carrySumAddMod8Const32Cost]; rfl]
  unfold CompressBlock1SparseD.main
  exact
    CostIs.bind (CostSparse.costIs_sub_messageScheduleSparse46 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_scheduleStepLast _) fun _ =>
    CostIs.bind (Cost.costIs_sub_scheduleStepLast _) fun _ =>
    CostIs.bind (CostSparse.costIs_sub_sha256Rounds62Block1_paired_sparse _) fun _ =>
    CostIs.bind (Cost.costIs_sub_tailPairWide _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAddOddConst32 _ _ _ _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAddMod4Const32 _ _ _ _) fun _ =>
    CostIs.bind (costIs_sub_deferAddConst _ _ _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAddMod8Const32 _ _ _ _) fun _ =>
    CostIs.bind (Cost.costIs_sub_carrySumAddOddConst32 _ _ _ _) fun _ =>
    CostIs.bind (costIs_sub_deferAddConst _ _ _) fun _ =>
    CostIs.pure _

theorem costIs_sub_compressBlock1SparseD (input : Var SHA256Block (F circomPrime)) :
    CostIs (subcircuit CompressBlock1SparseD.circuit input) compressBlock1SparseDCost :=
  CostIs.subcircuit (costIs_compressBlock1SparseD input)

/-! ## The digest selector that pays for the two deferred reductions -/

def selectDigestDCost : Count := ⟨76, 110⟩

theorem costIs_selectDigestD (input : Var SelectDigestD.Inputs (F circomPrime)) :
    CostIs (SelectDigestD.main input) selectDigestDCost := by
  rw [show selectDigestDCost = ⟨6, 0⟩ + (⟨32, 0⟩ + (⟨32, 0⟩ + (⟨3, 0⟩ + (⟨3, 0⟩ +
      (⟨0, 32⟩ + (⟨0, 32⟩ + (⟨0, 3⟩ + (⟨0, 3⟩ + (⟨0, 40⟩ + Count.zero))))))))) from by
    simp only [selectDigestDCost]; rfl]
  unfold SelectDigestD.main
  exact
    CostIs.bind (CostIs.witnessVector 6 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.pure _

theorem costIs_sub_selectDigestD (input : Var SelectDigestD.Inputs (F circomPrime)) :
    CostIs (subcircuit SelectDigestD.circuit input) selectDigestDCost :=
  CostIs.subcircuit (costIs_selectDigestD _)

end CostD
end Solution.SHA256
