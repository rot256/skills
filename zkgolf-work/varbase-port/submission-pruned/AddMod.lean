import Solution.Secp256k1ScalarMul.AddModTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Solution.Secp256k1ScalarMul.ValidP

namespace Solution.Secp256k1ScalarMul
namespace AddMod

end AddMod

namespace AddMod3
open AddMod

end AddMod3
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace AddMod

theorem emuWitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → Emu (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((ProvableType.witness (α := Emu) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

end AddMod
end Solution.Secp256k1ScalarMul

namespace Solution.Secp256k1ScalarMul
namespace AddMod3
open AddMod

end AddMod3
end Solution.Secp256k1ScalarMul
