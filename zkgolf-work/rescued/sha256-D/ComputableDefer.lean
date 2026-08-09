import Solution.SHA256.Sparse32
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Computable witnesses for the zero-cost deferred feed-forward gadgets
-/

namespace Solution.SHA256

open Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace DeferAdd

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  rw [Circuit.pure_structuralComputableWitnesses_iff]
  trivial

end DeferAdd

namespace DeferAddConst

theorem computableWitnesses (c : ℕ) (hc : c < 2^32) :
    (circuit (p := p) c hc).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main c input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  rw [Circuit.pure_structuralComputableWitnesses_iff]
  trivial

end DeferAddConst

end

end Solution.SHA256
