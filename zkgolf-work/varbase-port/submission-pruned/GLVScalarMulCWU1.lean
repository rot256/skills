import Solution.Secp256k1ScalarMul.GLVScalarMulCWHelpers

namespace Solution.Secp256k1ScalarMul

local notation "CF" => F circomPrime
open Challenge.Utils.ComputableWitnessLemmas

namespace GLVScalarMul

attribute [local irreducible] main PointValid.main GLVScalarRelation.main

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem structuralU1
    (input : Var ScalarMul.Inputs CF) (offset : ℕ)
    (env env' : ProverEnvironment CF) :
  SCW input env env' (shortOffset offset)
      ((u1Circuit input offset).operations (shortOffset offset)) := by
  unfold u1Circuit
  apply structuralGLVZ input (coeffVar input offset).u1 (shortOffset offset)
  intro k e e' hle h_agree _
  have h := coefficientOutput_stable input (off := coeffOffset offset)
    h_agree (by
      simpa only [shortOffset] using hle)
  simpa only [coeffVar, coeffCircuit, circuit_norm] using
    congrArg (fun c : GLV.Coefficients (CF) => c.u1) h

end GLVScalarMul
end Solution.Secp256k1ScalarMul
