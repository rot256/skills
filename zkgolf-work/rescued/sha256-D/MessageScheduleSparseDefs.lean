import Solution.SHA256.MessageScheduleSparseCore

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^76)] [Fact (p > 2^120)]

namespace Solution.SHA256.MessageScheduleSparse

open MessageSchedule

def Assumptions (block : SHA256Block (F p)) : Prop :=
  Numeric32 block[0] ∧ ∀ i : Fin 15, Normalized block[i.val + 1]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  (∀ i : Fin 62, valueBits sched[i] = expected[i]) ∧
  Numeric32 sched[0] ∧
  ∀ i : Fin 61, Normalized sched[i.val + 1]

end Solution.SHA256.MessageScheduleSparse
end
