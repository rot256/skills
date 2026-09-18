import Solution.Secp256k1ScalarMul.NegYAffineCompletenessEval

namespace Solution.Secp256k1ScalarMul
namespace NegYAffine

open Specs.ShortWeierstrass Specs.Secp256k1

/-- The two rows of a zero test are satisfied by the honest indicator/inverse pair. -/
private lemma zc_rows (d : F circomPrime) :
    ((if d = 0 then (1 : F circomPrime) else 0) + -1
        + d * (if d = 0 then (0 : F circomPrime) else d⁻¹) = 0)
    ∧ (d * (if d = 0 then (1 : F circomPrime) else 0) = 0) := by
  by_cases h : d = 0
  · simp [h]
  · refine ⟨?_, by simp [h]⟩
    rw [if_neg h, if_neg h, mul_inv_cancel₀ h]
    ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec]
  obtain ⟨hP, hcan⟩ := h_assumptions
  obtain ⟨hx, hy, hi⟩ := h_input
  obtain ⟨hc0env, hv1env, hc1env, hv2env, hc2env⟩ := h_env
  let Pv : Var FlaggedPoint (F circomPrime) :=
    { x := input_var_x, y := input_var_y, isInf := input_var_isInf }
  have hyi : ∀ (i : ℕ) (hip : i < numLimbs),
      Expression.eval env.toEnvironment (input_var_y[i]'hip) = input_y[i]'hip := by
    intro i hip
    simpa only [Vector.getElem_map] using
      congrArg (fun v : Emu (F circomPrime) => v[i]'hip) hy
  -- The single range check, on limb 0 of the result.
  have key :
      ZMod.val (Expression.eval env.toEnvironment
        ((result { x := input_var_x, y := input_var_y, isInf := input_var_isInf }
            (var ⟨i₀⟩) (var ⟨i₀ + 1 + 1⟩) (var ⟨i₀ + 1 + 1 + 1 + 1⟩))[0]))
        < 2 ^ secpParams.B := by
    rcases hP.1 with hinf | hinf
    · have hfin : input_isInf = 0 := by simpa using hinf
      have hfinVar : Expression.eval env.toEnvironment input_var_isInf = 0 := by
        rw [hi, hfin]
      have hyv := hP.2.2.1
      have hc0' : env.get i₀ =
          (borrow p0 input_y[0].val 0 : F circomPrime) := by
        rw [hc0env]
        exact carry0_finite Pv env input_y hfinVar hyi
      have hr0 := borrow_limb_value_lt p0 input_y[0].val 0
        (by decide) (hyv.1 (0 : Fin numLimbs)) (by omega)
      rw [ZMod.natCast_zmod_val] at hr0
      simp only [sub_eq_add_neg] at hr0
      simpa [result, qExpr, circuit_norm, hfinVar, hyi, hc0',
        radix, secpParams] using hr0
    · have hinfInput : input_isInf = 1 := by simpa using hinf
      have hy0 := hcan hinfInput
      have hinfVar : Expression.eval env.toEnvironment input_var_isInf = 1 := by
        rw [hi, hinfInput]
      have hyi0 : ∀ (i : ℕ) (hip : i < numLimbs),
          Expression.eval env.toEnvironment (input_var_y[i]'hip) = 0 := by
        intro i hip
        rw [hyi i hip, hy0]
        simp [emuOfNat, limbOfNat]
      have hc0 : env.get i₀ = 0 := by
        rw [hc0env]
        exact carry0_infinity Pv env hinfVar hyi0
      simp [result, qExpr, circuit_norm, hinfVar, hyi0, hc0, radix, secpParams]
  -- The two zero-test differences, in evaluated form.
  have hd1 : Expression.eval env.toEnvironment
      (d1Expr { x := input_var_x, y := input_var_y, isInf := input_var_isInf } (var ⟨i₀⟩))
      = d1From (eval env Pv) := by
    simp only [d1Expr, d1From, Expression.eval, hc0env, carry0Compute, Pv]
    simp [circuit_norm, sub_eq_add_neg]
  have hd2 : Expression.eval env.toEnvironment
      (d2Expr { x := input_var_x, y := input_var_y, isInf := input_var_isInf }
        (var ⟨i₀ + 1 + 1⟩))
      = d2From (eval env Pv) := by
    simp only [d2Expr, d2From, Expression.eval, hc1env, zc1Compute, Pv]
    simp [circuit_norm, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_, key⟩
  · rw [hc0env]
    simpa only [sub_eq_add_neg] using
      IsBool.iff_mul_sub_one.mp (carry0Compute_bool Pv env)
  · rw [hd1, hc1env, hv1env]
    simp only [zc1Compute, inv1Compute, zc1From, inv1From]
    exact (zc_rows (d1From (eval env Pv))).1
  · rw [hd1, hc1env]
    simp only [zc1Compute, zc1From]
    exact (zc_rows (d1From (eval env Pv))).2
  · rw [hd2, hc2env, hv2env]
    simp only [zc2Compute, inv2Compute, zc2From, inv2From]
    exact (zc_rows (d2From (eval env Pv))).1
  · rw [hd2, hc2env]
    simp only [zc2Compute, zc2From]
    exact (zc_rows (d2From (eval env Pv))).2

end NegYAffine
end Solution.Secp256k1ScalarMul
