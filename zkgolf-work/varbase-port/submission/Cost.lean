import Solution.Secp256k1ScalarMul.ScalarMul
import Solution.Secp256k1ScalarMul.Double
import Solution.Secp256k1ScalarMul.DivOrZeroF3
import Solution.Secp256k1ScalarMul.GroupedEqXV
import Solution.Secp256k1ScalarMul.GroupedEqXVNoTop
import Solution.Secp256k1ScalarMul.PhiPairAdd
import Solution.Secp256k1ScalarMul.ValidP
import Solution.Secp256k1ScalarMul.MulModFold
import Solution.Secp256k1ScalarMul.Split32
import Solution.Secp256k1ScalarMul.MulModFold32
import Solution.Secp256k1ScalarMul.MulModFold32Inv
import Solution.Secp256k1ScalarMul.MulModFoldTInv
import Solution.Secp256k1ScalarMul.MulModFold32MInv
import Solution.Secp256k1ScalarMul.MulModFold32NInv
import Solution.Secp256k1ScalarMul.MulModFold32T
import Solution.Secp256k1ScalarMul.MulModFold32TInv
import Solution.Secp256k1ScalarMul.MulModSub2F32
import Solution.Secp256k1ScalarMul.DivOrZeroS32
import Solution.Secp256k1ScalarMul.CancelLow
import Solution.Secp256k1ScalarMul.CrtMul
import Solution.Secp256k1ScalarMul.MulModSub2W32M
import Solution.Secp256k1ScalarMul.MulModSub2W32N
import Challenge.Utils.CostR1CS
import Clean.Circuit.Loops


namespace Solution.Secp256k1ScalarMul
namespace Cost

open Challenge.CostR1CS


theorem CostIs.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    CostIs (ProvableType.witness (α := α) compute) ⟨size α, 0⟩ := by
  intro n; rfl

theorem IsR1CSCirc.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := α) compute) := by
  intro n; trivial

theorem affineProvable_provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) (n : ℕ) :
    AffineProvable ((ProvableType.witness (α := α) compute).output n) := by
  rw [show ((ProvableType.witness (α := α) compute).output n)
        = varFromOffset α n from rfl]
  exact affineProvable_varFromOffset n

theorem CostIs.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations (F circomPrime)) = nestedCount _
    rw [show operationCount ([] : Operations (F circomPrime)) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)


theorem costIs_toBits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.main n x) ⟨n, n + 1⟩ := by
  unfold Gadgets.ToBits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + (⟨0, 1⟩ + Count.zero)) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp [Count.zero]
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨n * 0, n * 1⟩ from
      CostIs.forEach fun a m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  refine CostIs.bind
    (show CostIs (x === Utils.Bits.fieldFromBitsExpr bits) ⟨0, 1⟩ from ?_) fun _ => CostIs.pure _
  show CostIs (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr bits)) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, Utils.Bits.fieldFromBitsExpr bits)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

theorem isR1CS_toBits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.main n x) := by
  unfold Gadgets.ToBits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output n _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output n _ w i.val i.isLt) (Affine.const 1))
  · show IsR1CSCirc (x === Utils.Bits.fieldFromBitsExpr _)
    show IsR1CSCirc (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr _))
    unfold Expression.assertEquals
    refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
    show operationsIsR1CS ((Gadgets.Equality.main (M := id)
      (x, Utils.Bits.fieldFromBitsExpr ((Circuit.witnessVector n _).output w))).operations k)
    unfold Gadgets.Equality.main
    refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
    exact isR1CSRow_of_affine (Affine.sub hx
      (affine_fieldFromBitsExpr (Vector.mapRange n fun i => Expression.var { index := w + i })
        (affineW_mapRange_var _)))


theorem costIs_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.toBits n hn x) ⟨n, n + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBits n x m)

theorem isR1CS_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.toBits n hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBits n x hx m)


/-! ## Affine-top decomposition gadget -/

theorem costIs_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) :
    CostIs (ToBitsAffine.main w x) ⟨w, w + 1⟩ := by
  unfold ToBitsAffine.main
  rw [show (⟨w, w + 1⟩ : Count)
        = ⟨w, 0⟩ + (⟨w * 0, w * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) w _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨w * 0, w * 1⟩ from
      CostIs.forEach fun a m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_toBitsAffine (w : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ToBitsAffine.main w x) := by
  unfold ToBitsAffine.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector w _) fun ww => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output w _ ww i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output w _ ww i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields w) (F circomPrime) :=
      (Circuit.witnessVector w fun env =>
        Utils.Bits.fieldToBits w (x.eval env)).output ww
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange w fun i => Expression.var { index := ww + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ w : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) :=
      Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (ToBitsAffine.toBitsAffine w hn x) ⟨w, w + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBitsAffine w x m)

theorem isR1CS_toBitsAffine_sub (w : ℕ) (hn : (2 : ℕ) ^ (w + 1) < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ToBitsAffine.toBitsAffine w hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBitsAffine w x hx m)

/-- The returned decomposition vector `(mapRange w var).push top` is affine
throughout (low cells are witnesses, the top cell is an affine residual). -/
theorem affineW_push_top {w : ℕ} (base : ℕ) (top : Expression (F circomPrime))
    (htop : Affine top) :
    AffineW ((Vector.mapRange w fun i => Expression.var { index := base + i }).push top) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · rw [Vector.getElem_push_lt hlt, Vector.getElem_mapRange]; exact Affine.var _
  · rw [Vector.getElem_push_eq]; exact htop

theorem costIs_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs ((Gadgets.ToBits.rangeCheck n hn).main x) ⟨n, n + 1⟩ := by
  show CostIs (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ()) ⟨n, n + 1⟩
  have := CostIs.bind (costIs_toBits_sub n hn x) (fun _ => CostIs.pure ())
  simpa [Count.add_zero] using this

theorem isR1CS_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc ((Gadgets.ToBits.rangeCheck n hn).main x) := by
  show IsR1CSCirc (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ())
  exact IsR1CSCirc.bind (isR1CS_toBits_sub n hn x hx) (fun _ => IsR1CSCirc.pure ())

theorem costIs_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (assertion (Gadgets.ToBits.rangeCheck n hn) x) ⟨n, n + 1⟩ :=
  CostIs.assertion (fun m => costIs_rangeCheck n hn x m)

theorem isR1CS_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (Gadgets.ToBits.rangeCheck n hn) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_rangeCheck n hn x hx m)


theorem costIs_implicitRangeCheck (n : ℕ) (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (RangeCheck.main n x) ⟨n - 1, n⟩ := by
  unfold RangeCheck.main
  rw [show (⟨n - 1, n⟩ : Count)
        = ⟨n - 1, 0⟩ + (⟨(n - 1) * 0, (n - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) (n - 1) _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun a m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_implicitRangeCheck (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (RangeCheck.main n x) := by
  unfold RangeCheck.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector (n - 1) _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields (n - 1)) (F circomPrime) :=
      (Circuit.witnessVector (n - 1) fun env =>
        Utils.Bits.fieldToBits (n - 1) (x.eval env)).output w
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange (n - 1) fun i => Expression.var { index := w + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ (n - 1) : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) := by
      exact Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_assertion_implicitRangeCheck (n : ℕ)
    (hn : (2 : ℕ) ^ n < circomPrime) (hpos : 1 ≤ n)
    (x : Expression (F circomPrime)) :
    CostIs (assertion (RangeCheck.circuit n hn hpos) x) ⟨n - 1, n⟩ :=
  CostIs.assertion (fun m => costIs_implicitRangeCheck n hpos x m)

theorem isR1CS_assertion_implicitRangeCheck (n : ℕ)
    (hn : (2 : ℕ) ^ n < circomPrime) (hpos : 1 ≤ n)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (RangeCheck.circuit n hn hpos) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_implicitRangeCheck n x hx m)


variable {m : ℕ}

theorem costIs_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (Normalize.main P x) ⟨m * (P.B - 1), m * P.B⟩ := by
  unfold Normalize.main
  exact CostIs.forEach
    (fun a n => costIs_assertion_implicitRangeCheck P.B P.hB P.hB1 a n)

theorem isR1CS_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Normalize.main P x) := by
  unfold Normalize.main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n =>
      isR1CS_assertion_implicitRangeCheck P.B P.hB P.hB1 x[i.val] (hx i.val i.isLt) n

theorem costIs_assertion_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (Normalize.circuit P) x) ⟨m * (P.B - 1), m * P.B⟩ :=
  CostIs.assertion (fun n => costIs_normalize P x n)

theorem isR1CS_assertion_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (Normalize.circuit P) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_normalize P x hx n)


theorem costIs_equal (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (Equal.main input) ⟨0, m⟩ := by
  show CostIs (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs)) ⟨0, m⟩
  refine CostIs.assertion (K := ⟨0, m⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := m) (fun a k => CostIs.assertZero _ k) n)

theorem isR1CS_equal (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (Equal.main input) := by
  show IsR1CSCirc (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs))
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit (fields m)) fun n => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_) n
  refine IsR1CSCirc.assertZero ?_ k
  have hi : i.val < m := i.isLt
  rw [Vector.getElem_map, Vector.getElem_zip]
  exact isR1CSRow_of_affine (Affine.sub (hl i.val hi) (hr i.val hi))

theorem costIs_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (assertion (Equal.circuit P) input) ⟨0, m⟩ :=
  CostIs.assertion (fun n => costIs_equal input n)

theorem isR1CS_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (Equal.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_equal input hl hr n)

theorem affineW_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) (nd : ℕ) :
    AffineW ((ProvableType.witness (α := BigInt k) compute).output nd :
      Var (BigInt k) (F circomPrime)) := by
  rw [show ((ProvableType.witness (α := BigInt k) compute).output nd : Var (BigInt k) (F circomPrime))
        = varFromOffset (BigInt k) nd from rfl]
  exact affineW_varFromOffset _ _

theorem isR1CS_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := BigInt k) compute) :=
  IsR1CSCirc.provableWitness _

theorem isR1CS_witnessVec (k : ℕ) (c : ProverEnvironment (F circomPrime) → Vector (F circomPrime) k) :
    IsR1CSCirc (Circuit.witnessVector k c) := IsR1CSCirc.witnessVector k c


theorem costIs_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (LessThan.main P input)
      ⟨m + m * (P.B - 1) + m, m * P.B + m + m + 1⟩ := by
  have hne : ¬ (m = 0) := NeZero.ne m
  rw [show (⟨m + m * (P.B - 1) + m, m * P.B + m + m + 1⟩ : Count)
        = ⟨m, 0⟩ + (⟨m * (P.B - 1), m * P.B⟩ + (⟨m, 0⟩ +
            (⟨m * 0, m * 1⟩ + (⟨m * 0, m * 1⟩ + (⟨0, 1⟩ + Count.zero))))) from by
      simp only [Count.zero]; congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThan.main
  refine CostIs.bind (CostIs.provableWitness _) fun d => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector m _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  rw [dif_neg hne]
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThan.main P input) := by
  have hne : ¬ (m = 0) := NeZero.ne m
  unfold LessThan.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nd => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nd))
    fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec m _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- boolean forEach: each `c * (c - 1)` is a single row
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- linear forEach: each constraint is affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (Affine.add (Affine.add
      (hl i.val i.isLt) (affineW_provableWitness_bigInt _ nd i.val i.isLt)) ?_) ?_)
      (hr i.val i.isLt))
      (Affine.mul_fconst _ (affineW_witnessVector_output _ _ _ i.val i.isLt))
    · split
      · exact Affine.zero
      · exact affineW_witnessVector_output _ _ _ _ (by omega)
    · split
      · exact Affine.const 1
      · exact Affine.zero
  rw [dif_neg hne]
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (affineW_witnessVector_output _ _ _ (m - 1) (by omega))))
    fun _ => IsR1CSCirc.pure _

theorem costIs_assertion_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThan.circuit P) input)
      ⟨m + m * (P.B - 1) + m, m * P.B + m + m + 1⟩ :=
  CostIs.assertion (fun n => costIs_lessThan P input n)

theorem isR1CS_assertion_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThan.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThan P input hl hr n)


theorem costIs_eqViaCarries (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (EqViaCarries.main P input)
      ⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  rw [show (⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1)⟩ +
            (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero))) from by
      simp only [Count.zero]
      congr 1; simp only [Count.add_constraints]; ring]
  unfold EqViaCarries.main
  refine CostIs.bind (CostIs.witnessVector (2 * m - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => costIs_assertion_rangeCheck P.W P.hW a n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  rw [dif_neg hne]
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_eqViaCarries (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (EqViaCarries.main P input) := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  unfold EqViaCarries.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (2 * m - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- range-check each carry: `W`-bit, R1CS since carry entries are affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_rangeCheck P.W P.hW _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- per-index linear constraint is affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (hl i.val i.isLt) ?_) (hr i.val i.isLt))
      (Affine.mul_fconst _ (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt)
        (Affine.const _)))
    · split
      · exact Affine.zero
      · exact Affine.sub (affineW_witnessVector_output _ _ _ _ (by omega)) (Affine.const _)
  rw [dif_neg hne]
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (Affine.sub
      (affineW_witnessVector_output _ _ _ (2 * m - 1 - 1) (by omega)) (Affine.const _))))
    fun _ => IsR1CSCirc.pure _

theorem costIs_assertion_eqViaCarries (P : BigIntParams circomPrime m)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqViaCarries.circuit P) input)
      ⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ :=
  CostIs.assertion (fun n => costIs_eqViaCarries P input n)


theorem costIs_eqViaCarriesN (N : EqViaCarriesN.NParams circomPrime) [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (EqViaCarriesN.main N input)
      ⟨(2 * m - 1) + (2 * m - 1) * N.W, (2 * m - 1) * (N.W + 1) + (2 * m - 1) + 1⟩ := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  rw [show (⟨(2 * m - 1) + (2 * m - 1) * N.W, (2 * m - 1) * (N.W + 1) + (2 * m - 1) + 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * N.W, (2 * m - 1) * (N.W + 1)⟩ +
            (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero))) from by
      simp only [Count.zero]
      congr 1; simp only [Count.add_constraints]; ring]
  unfold EqViaCarriesN.main
  refine CostIs.bind (CostIs.witnessVector (2 * m - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => costIs_assertion_rangeCheck N.W N.hW a n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  rw [dif_neg hne]
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_eqViaCarriesN (N : EqViaCarriesN.NParams circomPrime) [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (EqViaCarriesN.main N input) := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  unfold EqViaCarriesN.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (2 * m - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_rangeCheck N.W N.hW _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (hl i.val i.isLt) ?_) (hr i.val i.isLt))
      (Affine.mul_fconst _ (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt)
        (Affine.const _)))
    · split
      · exact Affine.zero
      · exact Affine.sub (affineW_witnessVector_output _ _ _ _ (by omega)) (Affine.const _)
  rw [dif_neg hne]
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (Affine.sub
      (affineW_witnessVector_output _ _ _ (2 * m - 1 - 1) (by omega)) (Affine.const _))))
    fun _ => IsR1CSCirc.pure _

theorem costIs_assertion_eqViaCarriesN (N : EqViaCarriesN.NParams circomPrime)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqViaCarriesN.circuit N) input)
      ⟨(2 * m - 1) + (2 * m - 1) * N.W, (2 * m - 1) * (N.W + 1) + (2 * m - 1) + 1⟩ :=
  CostIs.assertion (fun n => costIs_eqViaCarriesN N input n)

theorem isR1CS_assertion_eqViaCarriesN (N : EqViaCarriesN.NParams circomPrime)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarriesN.circuit N) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqViaCarriesN N input hl hr n)


theorem affine_polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F circomPrime)) n)
    (x : F circomPrime)
    (h : ∀ i (hi : i < n), Affine coeffs[i]) :
    Affine (MulMod.polyEvalExpr coeffs x) := by
  simp only [MulMod.polyEvalExpr]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

theorem affine_groupExprW (B L : ℕ) (gf posOf : ℕ → ℕ)
    (x : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hx : AffineW x) (k : ℕ) :
    Affine (GroupedEqX.groupExprW B L gf posOf x k) := by
  unfold GroupedEqX.groupExprW
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  split
  · rename_i h
    exact hx _ h
  · exact Affine.zero

section GroupedXV
variable {L : ℕ}

theorem costIs_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [NeZero L]
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime)) :
    ∀ (c k₀ : ℕ),
      CostIs (GroupedEqXV.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀)
        ⟨GroupedEqXV.widthAllocFrom Wf c k₀, GroupedEqXV.widthConsFrom Wf c k₀⟩ := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact CostIs.pure _
  | succ n ih =>
    intro k₀
    rw [show (⟨GroupedEqXV.widthAllocFrom Wf (n + 1) k₀,
          GroupedEqXV.widthConsFrom Wf (n + 1) k₀⟩ : Count)
        = (⟨Wf k₀ - 1, Wf k₀⟩
            + ⟨GroupedEqXV.widthAllocFrom Wf n (k₀ + 1),
               GroupedEqXV.widthConsFrom Wf n (k₀ + 1)⟩ : Count) from by
      congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints,
          GroupedEqXV.widthAllocFrom, GroupedEqXV.widthConsFrom]]
    exact CostIs.bind
      (costIs_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _)
      fun _ => ih (k₀ + 1)

theorem costIs_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqXV.main B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ := by
  rw [show (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
        GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ : Count)
      = (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
          GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ + ⟨0, 1⟩ : Count) from by
    congr 1 <;> simp only [Count.add_allocations, Count.add_constraints]]
  unfold GroupedEqXV.main
  refine CostIs.bind (costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqXV.circuit B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqXV B gf posOf G V VR hgv hB1 input n)

theorem affine_carryExprXV [NeZero L] (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ k, Affine (GroupedEqXV.carryExpr B gf posOf OFFf lhs rhs k)
  | 0 => by
      unfold GroupedEqXV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub (affine_groupExprW B L gf posOf lhs hl 0) (affine_groupExprW B L gf posOf rhs hr 0)))
        (Affine.const _)
  | k + 1 => by
      unfold GroupedEqXV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub
            (Affine.add (affine_groupExprW B L gf posOf lhs hl (k + 1))
              (Affine.sub (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k) (Affine.const _)))
            (affine_groupExprW B L gf posOf rhs hr (k + 1))))
        (Affine.const _)

theorem isR1CS_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [NeZero L]
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ (c k₀ : ℕ),
      IsR1CSCirc (GroupedEqXV.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀) := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact IsR1CSCirc.pure _
  | succ n ih =>
    intro k₀
    refine IsR1CSCirc.bind
      (isR1CS_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _
        (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k₀))
      fun _ => ih (k₀ + 1)

theorem isR1CS_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqXV.main B gf posOf G V VR hgv input) := by
  unfold GroupedEqXV.main
  refine IsR1CSCirc.bind (isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _) fun _ => ?_
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  exact Affine.sub (hl i hi) (hr i hi)

theorem isR1CS_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqXV.circuit B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEqXV B gf posOf G V VR hgv hB1 input hl hr n)

end GroupedXV

section GroupedXVNoTop
variable {L : ℕ}

theorem costIs_groupedEqXVNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqXV.mainNoTop B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ := by
  unfold GroupedEqXV.mainNoTop
  exact costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _

theorem costIs_assertion_groupedEqXVNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqXV.circuitNoTop B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqXVNoTop B gf posOf G V VR hgv input n)

theorem isR1CS_groupedEqXVNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqXV.mainNoTop B gf posOf G V VR hgv input) := by
  unfold GroupedEqXV.mainNoTop
  exact isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _

theorem isR1CS_assertion_groupedEqXVNoTop (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqXV.circuitNoTop B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_groupedEqXVNoTop B gf posOf G V VR hgv input hl hr n)

end GroupedXVNoTop

theorem isR1CS_assertion_eqViaCarries (P : BigIntParams circomPrime m)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarries.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqViaCarries P input hl hr n)


theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

theorem affineW_bigIntMulVars [NeZero m] (pp : Vector (Expression (F circomPrime)) (m * m))
    (hpp : ∀ t (ht : t < m * m), Affine pp[t]) :
    AffineW (bigIntMulVars pp) := by
  intro k hk
  simp only [bigIntMulVars]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · exact Affine.add hacc (hpp _ _)
  · exact hacc

theorem affineW_witnessedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.witnessedMul a b).output off) := by
  rw [show (MulMod.witnessedMul a b).output off
        = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.witnessedMul_output off a b]
  refine affineW_bigIntMulVars _ fun t ht => ?_
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem affineW_bigIntMulNoReduce [NeZero m] (a n : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hnd : ∀ j (hj : j < m), degree n[j] = 0) :
    AffineW (bigIntMulNoReduce a n) := by
  intro k hk
  simp only [bigIntMulNoReduce]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · rename_i h
    exact Affine.add hacc (Affine.mul_deg0 (ha _ i.isLt) (hnd _ h.2))
  · exact hacc

/-- A degree-0 (constant) form times a degree-≤1 form is affine. -/
theorem affine_deg0_mul {a b : Expression (F circomPrime)} (ha : degree a = 0) (hb : Affine b) :
    Affine (a * b) := by
  simp only [Affine, degree_mul, ha, Nat.zero_add]; exact hb

/-- Constant-on-the-left companion of `affineW_bigIntMulNoReduce`. -/
theorem affineW_bigIntMulNoReduce_constA [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (had : ∀ j (hj : j < m), degree a[j] = 0) (hb : AffineW b) :
    AffineW (bigIntMulNoReduce a b) := by
  intro k hk
  simp only [bigIntMulNoReduce]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · rename_i h
    exact Affine.add hacc (affine_deg0_mul (had _ i.isLt) (hb _ h.2))
  · exact hacc

theorem affineW_interpolatedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.interpolatedMul a b).output off) := by
  rw [show (MulMod.interpolatedMul a b).output off
        = (Vector.mapRange (2 * m - 1) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.interpolatedMul_output off a b]
  intro k hk
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem costIs_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.interpolatedMul a b) ⟨2 * m - 1, 2 * m - 1⟩ := by
  rw [show (⟨2 * m - 1, 2 * m - 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.interpolatedMul
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.interpolatedMul a b) := by
  unfold MulMod.interpolatedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := 2 * m - 1) _ nz i hi))
  exact IsR1CSCirc.pure _

/-! ### The residue-ring (CRT) four-point multiply -/

theorem affineW_crtMul_output (a b : Var Emu (F circomPrime)) (off : ℕ) :
    AffineW ((CrtMul.crtMul a b).output off) := by
  rw [show (CrtMul.crtMul a b).output off
        = (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := off + i })
      from CrtMul.crtMul_output off a b]
  intro k hk
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem costIs_crtMul (a b : Var Emu (F circomPrime)) :
    CostIs (CrtMul.crtMul a b) ⟨numLimbs, numLimbs⟩ := by
  rw [show (⟨numLimbs, numLimbs⟩ : Count)
        = ⟨numLimbs, 0⟩ + (⟨numLimbs * 0, numLimbs * 1⟩ + Count.zero) from by decide]
  unfold CrtMul.crtMul
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_crtMul (a b : Var Emu (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (CrtMul.crtMul a b) := by
  unfold CrtMul.crtMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := numLimbs) _ nz i hi))
  exact IsR1CSCirc.pure _

/-! ### The sparse fourteen-point multiply -/

theorem affineW_pushZero14 (z : Vector (Expression (F circomPrime)) 14)
    (h : ∀ (i : ℕ) (hi : i < 14), Affine (z[i]'hi)) :
    AffineW (MulMod.pushZero14 z) := by
  intro i hi
  simp only [MulMod.pushZero14]
  by_cases h14 : i < 14
  · rw [Vector.getElem_push_lt h14]; exact h i h14
  · have hi14 : i = 14 := by omega
    subst hi14
    rw [Vector.getElem_push_eq]
    exact Affine.const _

theorem affineW_interpolatedMul14_output (a b : Var (BigInt 8) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.interpolatedMul14 a b).output off) := by
  rw [show (MulMod.interpolatedMul14 a b).output off = MulMod.zVec14 off from
    MulMod.interpolatedMul14_output off a b]
  refine affineW_pushZero14 _ fun i hi => ?_
  rw [Vector.getElem_mapRange]; exact Affine.var _

theorem costIs_interpolatedMul14 (a b : Var (BigInt 8) (F circomPrime)) :
    CostIs (MulMod.interpolatedMul14 a b) ⟨14, 14⟩ := by
  rw [show (⟨14, 14⟩ : Count) = ⟨14, 0⟩ + (⟨14 * 0, 14 * 1⟩ + Count.zero) from by decide]
  unfold MulMod.interpolatedMul14
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_interpolatedMul14 (a b : Var (BigInt 8) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.interpolatedMul14 a b) := by
  unfold MulMod.interpolatedMul14
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_pushZero14 _
          (fun j hj => affineW_provableWitness_bigInt (k := 14) _ nz j hj) i hi))
  exact IsR1CSCirc.pure _

theorem costIs_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.witnessedMul a b) ⟨m * m, m * m⟩ := by
  rw [show (⟨m * m, m * m⟩ : Count)
        = ⟨m * m, 0⟩ + (⟨m * m * 0, m * m * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.witnessedMul
  refine CostIs.bind (CostIs.provableWitness _) fun pp => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.witnessedMul a b) := by
  unfold MulMod.witnessedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (ha _ (Nat.div_lt_of_lt_mul t.isLt))
      (hb _ (Nat.mod_lt _ (Nat.pos_of_neZero m)))
      (affineW_provableWitness_bigInt (k := m * m) _ npp t.val t.isLt)
  exact IsR1CSCirc.pure _

def mulModCount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ + (⟨m * (B - 1), m * B⟩ +
    (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩ +
      (⟨m + m * (B - 1) + m, m * B + m + m + 1⟩ + Count.zero))))))

theorem costIs_mulMod (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulMod.main P gf posOf G V VR hgv input) (mulModCount m P.B V.Wf G) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulMod.main mulModCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulMod (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (subcircuit
        (MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b)
      (mulModCount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.subcircuit
    (fun n => costIs_mulMod secpParams gfMul posOfMul 5 vMul vMul hgvMul b n)

theorem isR1CS_mulMod (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0) :
    IsR1CSCirc (MulMod.main P gf posOf G V VR hgv input) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  -- the `a·b` interpolation check (`2m−1` rank-1 point rows)
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  -- GroupedEqXV on the affine coefficient vectors `Pc = interpolated cells` and
  -- `S = bigIntMulNoReduce q n + r` (constant-modulus convolution, witness-free).
  refine IsR1CSCirc.bind
    (isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · -- `Pc` is the affine output of `interpolatedMul a b`
    exact affineW_interpolatedMul_output input.a input.b _
  · -- `S[i] = (q·n)[i] (+ r[i])` is affine: affine·deg-0 convolution plus a cell
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- LessThan {r, n}: r is the witnessed remainder (affine), n is affine
    refine isR1CS_assertion_lessThan P _ ?_ hn
    intro i hi
    change Affine (varFromOffset (BigInt m) nr : Var (BigInt m) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulMod (b : Var (MulMod.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0) :
    IsR1CSCirc
      (subcircuit
        (MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b) :=
  IsR1CSCirc.subcircuit
    (fun n => isR1CS_mulMod secpParams gfMul posOfMul 5 vMul vMul hgvMul b ha hb hn hnd n)

theorem affineW_sub_mulMod (b : Var (MulMod.Inputs numLimbs) (F circomPrime)) (n : ℕ) :
    AffineW
      ((subcircuit
        (MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output
        n) := by
  have h : ((subcircuit
        (MulMod.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b).output n)
      = varFromOffset (BigInt numLimbs) (n + numLimbs) := by
    simp only [circuit_norm, subcircuit, MulMod.circuit, MulMod.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _


def mulModTargetCount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩))

theorem costIs_mulModTarget (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulModTarget.Inputs m) (F circomPrime)) :
    CostIs (MulModTarget.main P gf posOf G V VR hgv input) (mulModTargetCount m P.B V.Wf G) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTarget.main mulModTargetCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  exact costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _

theorem costIs_sub_mulModTarget (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (assertion
        (MulModTarget.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b)
      (mulModTargetCount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.assertion
    (fun n => costIs_mulModTarget secpParams gfMul posOfMul 5 vMul vMul hgvMul b n)

theorem isR1CS_mulModTarget (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (input : Var (MulModTarget.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModTarget.main P gf posOf G V VR hgv input) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTarget.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_
  · -- `Pc` is the affine output of `interpolatedMul a b`
    exact affineW_interpolatedMul_output input.a input.b _
  · -- `S[i] = (q·n)[i] (+ target[i])` is affine
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi)
        (ht i (by assumption))
    · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi

theorem isR1CS_sub_mulModTarget (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0)
    (ht : AffineW b.target) :
    IsR1CSCirc
      (assertion
        (MulModTarget.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul) b) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_mulModTarget secpParams gfMul posOfMul 5 vMul vMul hgvMul b ha hb hn hnd ht n)


theorem costIs_mulModTarget3 (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m - 1))
    (input : Var (MulModTarget.Inputs m) (F circomPrime)) :
    CostIs (MulModTarget3.main P gf posOf G V VR hgv c input)
      (mulModTargetCount m P.B V.Wf G) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTarget3.main mulModTargetCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  exact costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _

theorem costIs_sub_mulModTarget3 (c : Vector (F circomPrime) 7) (hB2 : 2 ≤ secpParams.B)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (assertion
        (MulModTarget3.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul c hB2) b)
      (mulModTargetCount numLimbs secpParams.B vMul.Wf 5) :=
  CostIs.assertion
    (fun n => costIs_mulModTarget3 secpParams gfMul posOfMul 5 vMul vMul hgvMul c b n)

theorem isR1CS_mulModTarget3 (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m - 1))
    (input : Var (MulModTarget.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModTarget3.main P gf posOf G V VR hgv c input) := by
  letI : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTarget3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_
  · -- `L[i] = Pc[i] + (3n)[i]` is affine (interp output plus a constant)
    intro i hi
    rw [Vector.getElem_mapFinRange]
    exact Affine.add (affineW_interpolatedMul_output input.a input.b _ i hi) (Affine.const _)
  · -- `S[i] = (q·n)[i] (+ target[i])` is affine
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi)
        (ht i (by assumption))
    · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hi

theorem isR1CS_sub_mulModTarget3 (c : Vector (F circomPrime) 7) (hB2 : 2 ≤ secpParams.B)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0)
    (ht : AffineW b.target) :
    IsR1CSCirc
      (assertion
        (MulModTarget3.circuit secpParams gfMul posOfMul 5 vMul vMul hgvMul hNfMul hNfMul c hB2) b) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_mulModTarget3 secpParams gfMul posOfMul 5 vMul vMul hgvMul c b ha hb hn hnd ht n)


theorem count_eq (a c : ℕ) {x : Count} (ha : x.allocations = a) (hc : x.constraints = c) :
    (⟨a, c⟩ : Count) = x := by
  cases x; cases ha; cases hc; rfl

theorem affine_one : Affine (1 : Expression (F circomPrime)) := Affine.const 1

theorem isR1CSRow_mul_add_sub {A B C D : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) (hD : Affine D) :
    isR1CSRow (A * B + C - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

theorem isR1CSRow_sub_add_sub_mul {w A B : Expression (F circomPrime)}
    (hw : Affine w) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (w - (A + B - A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (w + -((A + B) + -(A * B))) = some 0
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
      r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hw,
      r1csProducts_of_affine hA, r1csProducts_of_affine hB, h]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (w + -((A + B) + -(A * B))) = some 1
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
      r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hw,
      r1csProducts_of_affine hA, r1csProducts_of_affine hB, h]

theorem isR1CSRow_sub_one_sub_mul {w A B : Expression (F circomPrime)}
    (hw : Affine w) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (w - (1 - A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (w + -((1 : Expression (F circomPrime)) + -(A * B))) = some 0
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine affine_one]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (w + -((1 : Expression (F circomPrime)) + -(A * B))) = some 1
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine affine_one]


theorem costIs_assertEqField (x y : Expression (F circomPrime)) :
    CostIs (x === y) ⟨0, 1⟩ := by
  show CostIs (Expression.assertEquals x y) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, y)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

theorem isR1CS_assertEqField {x y : Expression (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (Expression.assertEquals x y)
  unfold Expression.assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := id) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

theorem costIs_assignEqField (rhs : Expression (F circomPrime)) :
    CostIs (HasAssignEq.assignEq (F := F circomPrime) rhs) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) from by decide]
  exact CostIs.bind (CostIs.witnessField _) fun w =>
    CostIs.bind (costIs_assertEqField _ rhs) fun _ => CostIs.pure _

theorem isR1CS_assignEqField (rhs : Expression (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (F := F circomPrime) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqField (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

theorem affine_assignEq_output (rhs : Expression (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (F := F circomPrime) rhs).output n) := Affine.var _


theorem costIs_assertEqFieldM (x y : Var field (F circomPrime)) :
    CostIs (x === y) ⟨0, 1⟩ := by
  show CostIs (assertEquals (M := field) x y) ⟨0, 1⟩
  unfold assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := field) (x, y)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) n)

theorem isR1CS_assertEqFieldM {x y : Var field (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (assertEquals (M := field) x y)
  unfold assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit field) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := field) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

theorem costIs_assignEqFieldM (rhs : Var field (F circomPrime)) :
    CostIs (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) from by decide]
  exact CostIs.bind (CostIs.provableWitness (α := field) _) fun w =>
    CostIs.bind (costIs_assertEqFieldM _ rhs) fun _ => CostIs.pure _

theorem isR1CS_assignEqFieldM (rhs : Var field (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqFieldM (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

theorem affine_assignEqFieldM_output (rhs : Var field (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs).output n) :=
  Affine.var _


theorem costIs_isZeroField (x : Expression (F circomPrime)) :
    CostIs (Gadgets.IsZeroField.main x) ⟨2, 2⟩ := by
  rw [show (⟨2, 2⟩ : Count) = ⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + Count.zero)) from by decide]
  unfold Gadgets.IsZeroField.main
  refine CostIs.bind (CostIs.witnessField _) fun xInv => ?_
  refine CostIs.bind (costIs_assignEqField _) fun isZero => ?_
  exact CostIs.bind (costIs_assertEqField _ _) fun _ => CostIs.pure _

theorem isR1CS_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.IsZeroField.main x) := by
  unfold Gadgets.IsZeroField.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nInv => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_one_sub_mul (Affine.var w) hx (Affine.var _)) fun nz => ?_
  refine IsR1CSCirc.bind (isR1CS_assertEqField ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_mul_sub (affine_assignEq_output _ nz) hx (Affine.const 0)

theorem costIs_sub_isZeroField (x : Expression (F circomPrime)) :
    CostIs (subcircuit Gadgets.IsZeroField.circuit x) ⟨2, 2⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroField x n)

theorem isR1CS_sub_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (subcircuit Gadgets.IsZeroField.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroField x hx n)

theorem affine_sub_isZeroField (x : Expression (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit Gadgets.IsZeroField.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.elaborated]
  exact Affine.var _


theorem costIs_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (Mux.main input) ⟨size M, size M⟩ := by
  obtain ⟨sel, t, f⟩ := input
  rw [show (⟨size M, size M⟩ : Count)
        = ⟨size M, 0⟩ + (⟨size M * 0, size M * 1⟩ + Count.zero) from
      count_eq _ _ (by simp only [Count.add_allocations, Count.zero]; omega)
        (by simp only [Count.add_constraints, Count.zero]; omega)]
  unfold Mux.main
  refine CostIs.bind (CostIs.provableWitness _) fun out => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine input.selector)
    (ht : AffineProvable input.ifTrue) (hf : AffineProvable input.ifFalse) :
    IsR1CSCirc (Mux.main input) := by
  obtain ⟨sel, t, f⟩ := input
  unfold Mux.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nout => ?_
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_add_sub hsel
    (Affine.sub (ht i.val i.isLt) (hf i.val i.isLt)) (hf i.val i.isLt)
    (affineProvable_provableWitness _ nout i.val i.isLt)

theorem costIs_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (subcircuit (Mux.circuit (M := M)) b) ⟨size M, size M⟩ :=
  CostIs.subcircuit (fun n => costIs_mux b n)

theorem isR1CS_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine b.selector)
    (ht : AffineProvable b.ifTrue) (hf : AffineProvable b.ifFalse) :
    IsR1CSCirc (subcircuit (Mux.circuit (M := M)) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mux b hsel ht hf n)

theorem affineProvable_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) (n : ℕ) :
    AffineProvable ((subcircuit (Mux.circuit (M := M)) b).output n) := by
  have h : (subcircuit (Mux.circuit (M := M)) b).output n = varFromOffset M n := by
    simp only [circuit_norm, subcircuit, Mux.circuit, Mux.elaborated]
  rw [h]
  exact affineProvable_varFromOffset n


theorem costIs_isZeroFe (x : Var Emu (F circomPrime)) :
    CostIs (IsZeroFe.main x) ⟨11, 11⟩ := by
  rw [show (⟨11, 11⟩ : Count)
        = ⟨2, 2⟩ + (⟨2, 2⟩ + (⟨2, 2⟩ + (⟨2, 2⟩ +
            (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + Count.zero)))))) from by decide]
  unfold IsZeroFe.main
  refine CostIs.bind (costIs_sub_isZeroField _) fun z0 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z1 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z2 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z3 => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun t01 => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun t23 => ?_
  exact CostIs.bind (costIs_assignEqFieldM _) fun z => CostIs.pure _

theorem isR1CS_isZeroFe (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (IsZeroFe.main x) := by
  unfold IsZeroFe.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 0 (by decide))) fun n0 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 1 (by decide))) fun n1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 2 (by decide))) fun n2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 3 (by decide))) fun n3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroField _ n0)
      (affine_sub_isZeroField _ n1)) fun n4 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroField _ n2)
      (affine_sub_isZeroField _ n3)) fun n5 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_assignEqFieldM_output _ n4)
      (affine_assignEqFieldM_output _ n5)) fun n6 => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_isZeroFe (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit IsZeroFe.circuit x) ⟨11, 11⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroFe x n)

theorem isR1CS_sub_isZeroFe (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit IsZeroFe.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroFe x hx n)

theorem affine_sub_isZeroFe (x : Var Emu (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit IsZeroFe.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, IsZeroFe.circuit, IsZeroFe.elaborated]
  exact Affine.var _


theorem degree_emuConst (v : ℕ) (i : ℕ) (hi : i < numLimbs) :
    degree (emuConst v : Var Emu (F circomPrime))[i] = 0 := by
  unfold emuConst
  rw [Vector.getElem_ofFn]
  exact degree_const _

theorem affineW_emuConst (v : ℕ) : AffineW (emuConst v : Var Emu (F circomPrime)) := by
  intro i hi
  unfold emuConst
  rw [Vector.getElem_ofFn]
  exact Affine.const _

theorem affineW_pConst : AffineW (pConst : Var Emu (F circomPrime)) :=
  affineW_emuConst P256

theorem degree_pConst (i : ℕ) (hi : i < numLimbs) :
    degree (pConst : Var Emu (F circomPrime))[i] = 0 :=
  degree_emuConst P256 i hi

theorem affine_provableWitness_field
    (c : ProverEnvironment (F circomPrime) → field (F circomPrime)) (n : ℕ) :
    Affine ((ProvableType.witness (α := field) c).output n) := Affine.var _


/-! ## Sparse-prime canonical validator -/

/-- `ValidP` performs four 64-bit decompositions, three zero tests, two
one-cell prefix products, and one merged quadratic assertion. -/
theorem costIs_validP (x : Var Emu (F circomPrime)) :
    CostIs (ValidP.main x) (⟨260, 265⟩ : Count) := by
  rw [show (⟨260, 265⟩ : Count) =
      ⟨63, 64⟩ + (⟨63, 64⟩ + (⟨63, 64⟩ + (⟨63, 64⟩ +
      (⟨2, 2⟩ + (⟨2, 2⟩ + (⟨2, 2⟩ + (⟨1, 1⟩ +
      (⟨1, 1⟩ + (⟨0, 1⟩ + Count.zero)))))))))
      from by decide]
  unfold ValidP.main
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b0 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b1 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b2 => ?_
  refine CostIs.bind (costIs_toBitsAffine_sub 63 secpParams.hB _) fun b3 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun topEq => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun midEq => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun lowEq => ?_
  refine CostIs.bind (costIs_assignEqField _) fun u => ?_
  refine CostIs.bind (costIs_assignEqField _) fun v => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_assertion_validP (x : Var Emu (F circomPrime)) :
    CostIs (assertion ValidP.circuit x) (⟨260, 265⟩ : Count) :=
  CostIs.assertion (fun n => costIs_validP x n)

/-- A deficit slice is affine whenever its source bits are affine. -/
theorem affine_deficitSlice {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (hbits : AffineW bits) (start len : ℕ) (h : start + len ≤ n) :
    Affine (ValidP.deficitSlice bits start len h) := by
  unfold ValidP.deficitSlice
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc
      (Affine.sub (Affine.const 1) (hbits (start + i.val) (by omega)))

/-- Every row in the sparse-prime validator is rank-1 when its four input
limbs are affine. -/
theorem isR1CS_validPTail (b0 b1 b2 b3 : Var (fields limbBits) (F circomPrime))
    (hb0 : AffineW b0) (hb1 : AffineW b1) (hb2 : AffineW b2) (hb3 : AffineW b3) :
    IsR1CSCirc (ValidP.tail b0 b1 b2 b3) := by
  unfold ValidP.tail
  let topDef : Expression (F circomPrime) :=
    ValidP.deficitSlice b0 33 31 (by decide) +
    ValidP.deficitSlice b1 0 64 (by decide) +
    ValidP.deficitSlice b2 0 64 (by decide) +
    ValidP.deficitSlice b3 0 64 (by decide)
  have htopDef : Affine topDef := by
    exact Affine.add (Affine.add (Affine.add
      (affine_deficitSlice _ hb0 33 31 (by decide))
      (affine_deficitSlice _ hb1 0 64 (by decide)))
      (affine_deficitSlice _ hb2 0 64 (by decide)))
      (affine_deficitSlice _ hb3 0 64 (by decide))
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField topDef htopDef) fun ntop => ?_
  let topEq : Var field (F circomPrime) :=
    (subcircuit Gadgets.IsZeroField.circuit topDef).output ntop
  have htopEq : Affine topEq := affine_sub_isZeroField topDef ntop
  let midDef := ValidP.deficitSlice b0 10 22 (by decide)
  have hmidDef : Affine midDef := affine_deficitSlice b0 hb0 10 22 (by decide)
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField midDef hmidDef) fun nmid => ?_
  let midEq : Var field (F circomPrime) :=
    (subcircuit Gadgets.IsZeroField.circuit midDef).output nmid
  have hmidEq : Affine midEq := affine_sub_isZeroField midDef nmid
  let lowDef := ValidP.deficitSlice b0 0 4 (by decide)
  have hlowDef : Affine lowDef := affine_deficitSlice b0 hb0 0 4 (by decide)
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField lowDef hlowDef) fun nlow => ?_
  let lowEq : Expression (F circomPrime) :=
    (subcircuit Gadgets.IsZeroField.circuit lowDef).output nlow
  have hlowEq : Affine lowEq := affine_sub_isZeroField lowDef nlow
  refine IsR1CSCirc.bind_out
    (isR1CS_assignEqField (b0[5] * (b0[4] + lowEq)) fun w =>
      isR1CSRow_sub_mul (Affine.var w) (hb0 5 (by decide))
        (Affine.add (hb0 4 (by decide)) hlowEq)) fun nu => ?_
  let u : Expression (F circomPrime) := Expression.var { index := nu }
  have hu : Affine u := Affine.var _
  let midSum := b0[9] + b0[8] + b0[7] + b0[6] + u
  have hmidSum : Affine midSum :=
    Affine.add (Affine.add (Affine.add (Affine.add
      (hb0 9 (by decide)) (hb0 8 (by decide))) (hb0 7 (by decide)))
      (hb0 6 (by decide))) hu
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField (midEq * midSum) fun w =>
    isR1CSRow_sub_mul (Affine.var w) hmidEq hmidSum) fun nv => ?_
  let v : Expression (F circomPrime) := Expression.var { index := nv }
  have hv : Affine v := Affine.var _
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_mul htopEq (Affine.add (hb0 32 (by decide)) hv)

theorem isR1CS_validP (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ValidP.main x) := by
  unfold ValidP.main
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 0 (by decide))) fun n0 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 1 (by decide))) fun n1 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 2 (by decide))) fun n2 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_toBitsAffine_sub 63 secpParams.hB _ (hx 3 (by decide))) fun n3 => ?_
  exact isR1CS_validPTail _ _ _ _
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 0 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 1 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 2 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))
    (affineW_push_top _ _ (Affine.fconst_mul _
      (Affine.sub (hx 3 (by decide)) (affine_fieldFromBitsExpr _ (affineW_mapRange_var _)))))

theorem isR1CS_assertion_validP (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion ValidP.circuit x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_validP x hx n)


def addModCost : Count := ⟨285, 292⟩

theorem costIs_addMod (input : Var AddMod.Inputs (F circomPrime)) :
    CostIs (AddMod.main input) addModCost := by
  obtain ⟨a, b⟩ := input
  rw [show addModCost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨260, 265⟩ +
            (⟨20, 26⟩ + Count.zero)))) from by decide]
  unfold AddMod.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarriesN eqNParamsAdd _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_addMod (input : Var AddMod.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (AddMod.main input) := by
  obtain ⟨a, b⟩ := input
  unfold AddMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarriesN eqNParamsAdd _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = a[k] + b[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (ha _ (by assumption)) (hb _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = q·p[k] + r[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
        (affineW_provableWitness_bigInt _ nr _ (by assumption))
    · exact Affine.zero

theorem costIs_sub_addMod (b : Var AddMod.Inputs (F circomPrime)) :
    CostIs (subcircuit AddMod.circuit b) addModCost :=
  CostIs.subcircuit (fun n => costIs_addMod b n)

theorem isR1CS_sub_addMod (b : Var AddMod.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) :
    IsR1CSCirc (subcircuit AddMod.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_addMod b ha hb n)

theorem affineW_sub_addMod (b : Var AddMod.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit AddMod.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, AddMod.circuit, AddMod.elaborated]
  exact affineW_varFromOffset _ _

def subModCost : Count := ⟨285, 292⟩

theorem costIs_subMod (input : Var SubMod.Inputs (F circomPrime)) :
    CostIs (SubMod.main input) subModCost := by
  obtain ⟨a, b⟩ := input
  rw [show subModCost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨260, 265⟩ +
            (⟨20, 26⟩ + Count.zero)))) from by decide]
  unfold SubMod.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarriesN eqNParamsAdd _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_subMod (input : Var SubMod.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (SubMod.main input) := by
  obtain ⟨a, b⟩ := input
  unfold SubMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarriesN eqNParamsAdd _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = r[k] + b[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_provableWitness_bigInt _ nr _ (by assumption))
        (hb _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = a[k] + q·p[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (ha _ (by assumption))
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
    · exact Affine.zero

theorem costIs_sub_subMod (b : Var SubMod.Inputs (F circomPrime)) :
    CostIs (subcircuit SubMod.circuit b) subModCost :=
  CostIs.subcircuit (fun n => costIs_subMod b n)

theorem isR1CS_sub_subMod (b : Var SubMod.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) :
    IsR1CSCirc (subcircuit SubMod.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_subMod b ha hb n)

theorem affineW_sub_subMod (b : Var SubMod.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit SubMod.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, SubMod.circuit, SubMod.elaborated]
  exact affineW_varFromOffset _ _


def addMod3Cost : Count := ⟨291, 298⟩

theorem costIs_addMod3 (input : Var AddMod3.Inputs (F circomPrime)) :
    CostIs (AddMod3.main input) addMod3Cost := by
  rw [show addMod3Cost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨260, 265⟩ +
            (⟨25, 31⟩ + Count.zero)))))) from by decide]
  unfold AddMod3.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun t => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarriesN eqNParams3Add _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_addMod3 (input : Var AddMod3.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c) :
    IsR1CSCirc (AddMod3.main input) := by
  unfold AddMod3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nt => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul_sub (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1))
      (affine_provableWitness_field _ nt))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nt)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 2)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarriesN eqNParams3Add _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = a[k] + b[k] + c[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (Affine.add (ha _ (by assumption)) (hb _ (by assumption)))
        (hc _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = q·p[k] + r[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
        (affineW_provableWitness_bigInt _ nr _ (by assumption))
    · exact Affine.zero

theorem costIs_sub_addMod3 (b : Var AddMod3.Inputs (F circomPrime)) :
    CostIs (subcircuit AddMod3.circuit b) addMod3Cost :=
  CostIs.subcircuit (fun n => costIs_addMod3 b n)

theorem isR1CS_sub_addMod3 (b : Var AddMod3.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit AddMod3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_addMod3 b ha hb hc n)

theorem affineW_sub_addMod3 (b : Var AddMod3.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit AddMod3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, AddMod3.circuit, AddMod3.elaborated]
  exact affineW_varFromOffset _ _

def subMod3Cost : Count := ⟨291, 298⟩

theorem costIs_subMod3 (input : Var SubMod3.Inputs (F circomPrime)) :
    CostIs (SubMod3.main input) subMod3Cost := by
  rw [show subMod3Cost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨260, 265⟩ +
            (⟨25, 31⟩ + Count.zero)))))) from by decide]
  unfold SubMod3.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun t => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarriesN eqNParams3Add _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_subMod3 (input : Var SubMod3.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c) :
    IsR1CSCirc (SubMod3.main input) := by
  unfold SubMod3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nt => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul_sub (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1))
      (affine_provableWitness_field _ nt))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nt)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 2)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarriesN eqNParams3Add _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = r[k] + b[k] + c[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (Affine.add (affineW_provableWitness_bigInt _ nr _ (by assumption))
          (hb _ (by assumption)))
        (hc _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = a[k] + q·p[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (ha _ (by assumption))
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
    · exact Affine.zero

theorem costIs_sub_subMod3 (b : Var SubMod3.Inputs (F circomPrime)) :
    CostIs (subcircuit SubMod3.circuit b) subMod3Cost :=
  CostIs.subcircuit (fun n => costIs_subMod3 b n)

theorem isR1CS_sub_subMod3 (b : Var SubMod3.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit SubMod3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_subMod3 b ha hb hc n)

theorem affineW_sub_subMod3 (b : Var SubMod3.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit SubMod3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, SubMod3.circuit, SubMod3.elaborated]
  exact affineW_varFromOffset _ _


/-- One quotient wire, a 68-bit range check, the four CRT residue-ring product
coefficients, and a single 99-bit carry. -/
def mulModFoldCount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold - 1, qBitsFold⟩ + (⟨numLimbs, numLimbs⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFoldL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFoldL.Wf (3 - 2) 0 + 1⟩))

theorem costIs_mulModFold (input : Var MulModFold.Inputs (F circomPrime)) :
    CostIs (MulModFold.main input) mulModFoldCount := by
  unfold MulModFold.main mulModFoldCount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_crtMul _ _) fun Pc => ?_
  exact costIs_assertion_groupedEqXV 64 gfFold posOfFold 3 vFoldL vFoldR hgvFold (by norm_num) _

theorem costIs_sub_mulModFold (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (b : Var MulModFold.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold.circuit Ca Cb hcap) b) mulModFoldCount :=
  CostIs.assertion (fun n => costIs_mulModFold b n)

theorem affineW_foldLhs (Pc : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (h : AffineW Pc) : AffineW (MulModFold.foldLhs Pc) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 4 (by decide)))) (Affine.const _)
  · exact Affine.add (Affine.add (h 1 (by decide))
      (Affine.fconst_mul _ (h 5 (by decide)))) (Affine.const _)
  · exact Affine.add (Affine.add (h 2 (by decide))
      (Affine.fconst_mul _ (h 6 (by decide)))) (Affine.const _)
  · exact Affine.add (h 3 (by decide)) (Affine.const _)

theorem affineW_foldRhs (q : Expression (F circomPrime)) (hq : Affine q)
    (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    AffineW (MulModFold.foldRhs q t) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;>
    exact Affine.add (Affine.mul_deg0 hq (degree_const _)) (ht _ (by decide))

theorem affineW_foldLhsCF (d : Vector (Expression (F circomPrime)) numLimbs)
    (h : AffineW d) : AffineW (MulModFold.foldLhsC d) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;>
    exact Affine.add (h _ (by decide)) (Affine.const _)

theorem isR1CS_mulModFold (input : Var MulModFold.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold.main input) := by
  unfold MulModFold.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_crtMul _ _ ha hb) fun nPc => ?_
  exact isR1CS_assertion_groupedEqXV 64 gfFold posOfFold 3 vFoldL vFoldR hgvFold (by norm_num) _
    (affineW_foldLhsCF _ (affineW_crtMul_output input.a input.b _))
    (affineW_foldRhs _ (Affine.var _) _ ht)

theorem isR1CS_sub_mulModFold (Ca Cb : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (b : Var MulModFold.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (ht : AffineW b.target) :
    IsR1CSCirc (assertion (MulModFold.circuit Ca Cb hcap) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold b ha hb ht n)


def mulModSub2Cost : Count := ⟨434, 437⟩

theorem costIs_mulModSub2 (input : Var MulModSub2.Inputs (F circomPrime)) :
    CostIs (MulModSub2.main input) mulModSub2Cost := by
  obtain ⟨a, b, s1, s2⟩ := input
  rw [show mulModSub2Cost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (⟨170, 172⟩ + Count.zero)) from by decide]
  unfold MulModSub2.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModFold _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_mulModSub2 (input : Var MulModSub2.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (MulModSub2.main input) := by
  obtain ⟨a, b, s1, s2⟩ := input
  unfold MulModSub2.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_sub_mulModFold _ _ _ _ ha hb ?_)
    fun _ => IsR1CSCirc.pure _
  -- the target limbs r[k] + s1[k] + s2[k] are affine
  intro i hi
  rw [Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ (hs1 i hi)) (hs2 i hi)
  exact affineW_provableWitness_bigInt _ nr i hi

theorem costIs_sub_mulModSub2 (b : Var MulModSub2.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSub2.circuit b) mulModSub2Cost :=
  CostIs.subcircuit (fun n => costIs_mulModSub2 b n)

theorem isR1CS_sub_mulModSub2 (b : Var MulModSub2.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b)
    (hs1 : AffineW b.s1) (hs2 : AffineW b.s2) :
    IsR1CSCirc (subcircuit MulModSub2.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModSub2 b ha hb hs1 hs2 n)

theorem affineW_sub_mulModSub2 (b : Var MulModSub2.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSub2.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, MulModSub2.circuit, MulModSub2.elaborated]
  exact affineW_varFromOffset _ _


def divOrZeroCost : Count := ⟨999, 1008⟩

theorem costIs_divOrZero (input : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (DivOrZero.main input) divOrZeroCost := by
  obtain ⟨num, den⟩ := input
  rw [show divOrZeroCost
        = ⟨11, 11⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 0⟩ + (⟨252, 256⟩ + (⟨260, 265⟩ +
            (⟨464, 468⟩ + Count.zero)))))) from by decide]
  unfold DivOrZero.main
  refine CostIs.bind (costIs_sub_isZeroFe _) fun z => ?_
  refine CostIs.bind (costIs_sub_mux _) fun denSafe => ?_
  refine CostIs.bind (costIs_sub_mux _) fun numSafe => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModTarget _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divOrZero (input : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW input.num) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZero.main input) := by
  obtain ⟨num, den⟩ := input
  unfold DivOrZero.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFe _ hden) fun nz => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nd => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 1).affineProvable
  · exact hden.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nn => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 0).affineProvable
  · exact hnum.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize secpParams _ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan secpParams _ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact affineW_pConst
  refine IsR1CSCirc.bind (isR1CS_sub_mulModTarget _ ?_ ?_ ?_ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact (affineProvable_sub_mux _ nd).affineW
  · exact affineW_pConst
  · exact degree_pConst
  · exact (affineProvable_sub_mux _ nn).affineW
  exact IsR1CSCirc.pure _

theorem costIs_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZero.circuit b) divOrZeroCost :=
  CostIs.subcircuit (fun n => costIs_divOrZero b n)

theorem isR1CS_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW b.num) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZero.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZero b hnum hden n)

theorem affineW_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZero.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivOrZero.circuit, DivOrZero.elaborated]
  exact affineW_varFromOffset _ _


def divOrZero3Cost : Count := ⟨999, 1008⟩

theorem costIs_divOrZero3 (input : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (DivOrZero3.main input) divOrZero3Cost := by
  obtain ⟨num, den⟩ := input
  rw [show divOrZero3Cost
        = ⟨11, 11⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 0⟩ + (⟨252, 256⟩ + (⟨260, 265⟩ +
            (⟨464, 468⟩ + Count.zero)))))) from by decide]
  unfold DivOrZero3.main
  refine CostIs.bind (costIs_sub_isZeroFe _) fun z => ?_
  refine CostIs.bind (costIs_sub_mux _) fun denSafe => ?_
  refine CostIs.bind (costIs_sub_mux _) fun numSafe => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModTarget3 _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divOrZero3 (input : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW input.num) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZero3.main input) := by
  obtain ⟨num, den⟩ := input
  unfold DivOrZero3.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFe _ hden) fun nz => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nd => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 1).affineProvable
  · exact hden.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nn => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 0).affineProvable
  · exact hnum.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize secpParams _ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan secpParams _ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact affineW_pConst
  refine IsR1CSCirc.bind (isR1CS_sub_mulModTarget3 _ _ _ ?_ ?_ ?_ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact (affineProvable_sub_mux _ nd).affineW
  · exact affineW_pConst
  · exact degree_pConst
  · exact (affineProvable_sub_mux _ nn).affineW
  exact IsR1CSCirc.pure _

theorem costIs_sub_divOrZero3 (b : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZero3.circuit b) divOrZero3Cost :=
  CostIs.subcircuit (fun n => costIs_divOrZero3 b n)

theorem isR1CS_sub_divOrZero3 (b : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW b.num) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZero3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZero3 b hnum hden n)

theorem affineW_sub_divOrZero3 (b : Var DivOrZero.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZero3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivOrZero3.circuit, DivOrZero3.elaborated]
  exact affineW_varFromOffset _ _


theorem costIs_eqFe (x : Var EqFe.Inputs (F circomPrime)) :
    CostIs (EqFe.main x) ⟨3, 4⟩ := by
  rw [show (⟨3, 4⟩ : Count)
        = ⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + Count.zero)))))
      from by decide]
  unfold EqFe.main
  refine CostIs.bind (CostIs.witnessField _) fun v => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun uInv => ?_
  refine CostIs.bind (costIs_assignEqField _) fun z => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_eqFe (x : Var EqFe.Inputs (F circomPrime))
    (ha : AffineW x.a) (hb : AffineW x.b) :
    IsR1CSCirc (EqFe.main x) := by
  have hlo : Affine (EqFe.packLoExpr x.a x.b) :=
    Affine.add (Affine.sub (ha 0 (by decide)) (hb 0 (by decide)))
      (Affine.fconst_mul _ (Affine.sub (ha 1 (by decide)) (hb 1 (by decide))))
  have hhi : Affine (EqFe.packHiExpr x.a x.b) :=
    Affine.add (Affine.sub (ha 2 (by decide)) (hb 2 (by decide)))
      (Affine.fconst_mul _ (Affine.sub (ha 3 (by decide)) (hb 3 (by decide))))
  unfold EqFe.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nv => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (Affine.var _) (Affine.sub (Affine.var _) hhi))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun ni => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_one_sub_mul (Affine.var w)
      (Affine.add hlo (Affine.var _)) (Affine.var _)) fun nz => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul (Affine.var _) hlo)) fun _ => ?_
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul (Affine.var _) hhi)) fun _ =>
    IsR1CSCirc.pure _

theorem costIs_sub_eqFe (x : Var EqFe.Inputs (F circomPrime)) :
    CostIs (subcircuit EqFe.circuit x) ⟨3, 4⟩ :=
  CostIs.subcircuit (fun n => costIs_eqFe x n)

theorem isR1CS_sub_eqFe (x : Var EqFe.Inputs (F circomPrime))
    (ha : AffineW x.a) (hb : AffineW x.b) :
    IsR1CSCirc (subcircuit EqFe.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_eqFe x ha hb n)

theorem affine_sub_eqFe (x : Var EqFe.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit EqFe.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, EqFe.circuit, EqFe.elaborated]
  exact Affine.var _


theorem costIs_isZeroFe2 (x : Var Emu (F circomPrime)) :
    CostIs (IsZeroFe2.main x) ⟨5, 5⟩ := by
  rw [show (⟨5, 5⟩ : Count)
        = ⟨2, 2⟩ + (⟨2, 2⟩ + (⟨1, 1⟩ + Count.zero)) from by decide]
  unfold IsZeroFe2.main
  refine CostIs.bind (costIs_sub_isZeroField _) fun z0 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z1 => ?_
  exact CostIs.bind (costIs_assignEqFieldM _) fun z => CostIs.pure _

theorem isR1CS_isZeroFe2 (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (IsZeroFe2.main x) := by
  unfold IsZeroFe2.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 0 (by decide))) fun n0 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 1 (by decide))) fun n1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroField _ n0)
      (affine_sub_isZeroField _ n1)) fun n2 => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_isZeroFe2 (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit IsZeroFe2.circuit x) ⟨5, 5⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroFe2 x n)

theorem isR1CS_sub_isZeroFe2 (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit IsZeroFe2.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroFe2 x hx n)

theorem affine_sub_isZeroFe2 (x : Var Emu (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit IsZeroFe2.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, IsZeroFe2.circuit, IsZeroFe2.elaborated]
  exact Affine.var _


theorem costIs_isZeroFeSum (x : Var Emu (F circomPrime)) :
    CostIs (IsZeroFeSum.main x) ⟨2, 2⟩ := by
  rw [show (⟨2, 2⟩ : Count) = ⟨2, 2⟩ + Count.zero from by decide]
  unfold IsZeroFeSum.main
  exact CostIs.bind (costIs_sub_isZeroField _) fun z => CostIs.pure _

theorem isR1CS_isZeroFeSum (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (IsZeroFeSum.main x) := by
  unfold IsZeroFeSum.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ ?_) fun n0 => ?_
  · exact Affine.add (Affine.add (Affine.add (hx 0 (by decide)) (hx 1 (by decide)))
      (hx 2 (by decide))) (hx 3 (by decide))
  exact IsR1CSCirc.pure _

theorem costIs_sub_isZeroFeSum (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit IsZeroFeSum.circuit x) ⟨2, 2⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroFeSum x n)

theorem isR1CS_sub_isZeroFeSum (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit IsZeroFeSum.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroFeSum x hx n)

theorem affine_sub_isZeroFeSum (x : Var Emu (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit IsZeroFeSum.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, IsZeroFeSum.circuit, IsZeroFeSum.elaborated]
  exact Affine.var _


def mulModTargetWCount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    (⟨m * (B - 1), m * B⟩ + (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩)))))))))

theorem costIs_mulModTargetW (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m))
    (input : Var (MulModTarget.Inputs m) (F circomPrime)) :
    CostIs (MulModTargetW.main P gf posOf G V VR hgv c input)
      (mulModTargetWCount m P.B V.Wf G) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetW.main mulModTargetWCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh0 => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh1 => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh2 => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pab => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pxx => ?_
  exact costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _

theorem costIs_sub_mulModTargetW (c : Vector (F circomPrime) 8) (hB3 : 3 ≤ secpParams.B)
    (hp8 : 2 ^ (2 * secpParams.B) * (4 * numLimbs + 1) * 8 < circomPrime)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (assertion
        (MulModTargetW.circuit secpParams gfMulD posOfMulD 5 vW vrW hgvW
          hNfW hNfrW c hB3 hp8) b)
      (mulModTargetWCount numLimbs secpParams.B vW.Wf 5) :=
  CostIs.assertion
    (fun n => costIs_mulModTargetW secpParams gfMulD posOfMulD 5 vW vrW hgvW c b n)

theorem isR1CS_mulModTargetW (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m))
    (input : Var (MulModTarget.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModTargetW.main P gf posOf G V VR hgv c input) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetW.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh0 => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh1 => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh2 => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh0)
      (Affine.sub (affine_provableWitness_field _ nqh0) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh1)
      (Affine.sub (affine_provableWitness_field _ nqh1) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh2)
      (Affine.sub (affine_provableWitness_field _ nqh2) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPab => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ht ht) fun nPxx => ?_
  refine isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_
  · -- `lVecW Pab c [i]`: interp output below `2m−1` plus a constant
    intro i hi
    simp only [MulModTargetW.lVecW, Vector.getElem_mapFinRange i hi]
    refine Affine.add ?_ (Affine.const _)
    split
    · rename_i hlt
      exact affineW_interpolatedMul_output input.a input.b _ i hlt
    · exact Affine.zero
  · -- `sVecTD (sVecX q n Pxx) qh n [i]`: conv + scaled interp below `2m−1`
    -- plus the affine 3-bit flank `qh·n[i−m]`
    intro i hi
    simp only [MulModTargetD.sVecTD, Vector.getElem_mapFinRange i hi]
    refine Affine.add ?_ ?_
    · split
      · rename_i hlt
        simp only [MulModTargetW.sVecX, Vector.getElem_mapFinRange i hlt]
        exact Affine.add
          (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hlt)
          (Affine.fconst_mul _
            (affineW_interpolatedMul_output input.target input.target _ i hlt))
      · exact Affine.zero
    · split
      · rename_i hm
        exact Affine.mul_deg0
          (Affine.add (Affine.add (affine_provableWitness_field _ nqh0)
              (Affine.fconst_mul _ (affine_provableWitness_field _ nqh1)))
            (Affine.fconst_mul _ (affine_provableWitness_field _ nqh2)))
          (hnd (i - m) hm.2)
      · exact Affine.zero

theorem isR1CS_sub_mulModTargetW (c : Vector (F circomPrime) 8) (hB3 : 3 ≤ secpParams.B)
    (hp8 : 2 ^ (2 * secpParams.B) * (4 * numLimbs + 1) * 8 < circomPrime)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0)
    (ht : AffineW b.target) :
    IsR1CSCirc
      (assertion
        (MulModTargetW.circuit secpParams gfMulD posOfMulD 5 vW vrW hgvW
          hNfW hNfrW c hB3 hp8) b) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_mulModTargetW secpParams gfMulD posOfMulD 5 vW vrW hgvW
      c b ha hb hn hnd ht n)


def mulModTargetTCount (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    (⟨m * (B - 1), m * B⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩))))))))

theorem costIs_mulModTargetT (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m))
    (input : Var (MulModTargetT.Inputs m) (F circomPrime)) :
    CostIs (MulModTargetT.main P gf posOf G V VR hgv c input)
      (mulModTargetTCount m P.B V.Wf G) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetT.main mulModTargetTCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh0 => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh1 => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh2 => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pab => ?_
  exact costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _


theorem isR1CS_mulModTargetT (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m))
    (input : Var (MulModTargetT.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModTargetT.main P gf posOf G V VR hgv c input) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetT.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh0 => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh1 => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh2 => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh0)
      (Affine.sub (affine_provableWitness_field _ nqh0) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh1)
      (Affine.sub (affine_provableWitness_field _ nqh1) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nqh2)
      (Affine.sub (affine_provableWitness_field _ nqh2) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPab => ?_
  refine isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_
  · -- `lVecW Pab c [i]`: interp output below `2m−1` plus a constant
    intro i hi
    simp only [MulModTargetW.lVecW, Vector.getElem_mapFinRange i hi]
    refine Affine.add ?_ (Affine.const _)
    split
    · rename_i hlt
      exact affineW_interpolatedMul_output input.a input.b _ i hlt
    · exact Affine.zero
  · -- `sVecTD (sVecT q n input.target) qh n [i]`: conv + raw target below `2m−1`
    -- plus the affine 3-bit flank `qh·n[i−m]`
    intro i hi
    simp only [MulModTargetD.sVecTD, Vector.getElem_mapFinRange i hi]
    refine Affine.add ?_ ?_
    · split
      · rename_i hlt
        simp only [MulModTargetT.sVecT, Vector.getElem_mapFinRange i hlt]
        exact Affine.add
          (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hlt)
          (ht i hlt)
      · exact Affine.zero
    · split
      · rename_i hm
        exact Affine.mul_deg0
          (Affine.add (Affine.add (affine_provableWitness_field _ nqh0)
              (Affine.fconst_mul _ (affine_provableWitness_field _ nqh1)))
            (Affine.fconst_mul _ (affine_provableWitness_field _ nqh2)))
          (hnd (i - m) hm.2)
      · exact Affine.zero



-- The widened fused-slope target certificate `MulModTargetT3.circuit3` shares its
-- `.main` (definitionally `MulModTargetT.main … vW3 vrW hgvW3 threeP2Limbs`) with the
-- generic `MulModTargetT.main`, so its cost/R1CS facts fork the plain ones with the
-- widened parameters plugged in. `vW3.Wf = vW.Wf = wfW`, so the count is unchanged.
theorem costIs_sub_mulModTargetT3
    (b : Var (MulModTargetT.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (assertion
        (MulModTargetT3.circuit3 secpParams gfMulD posOfMulD 5 vW3 vrW hgvW3
          hNfW3 hNfrW threeP2Limbs (by decide) (by decide)) b)
      (mulModTargetTCount numLimbs secpParams.B vW3.Wf 5) :=
  CostIs.assertion
    (fun n => costIs_mulModTargetT secpParams gfMulD posOfMulD 5 vW3 vrW hgvW3 threeP2Limbs b n)

theorem isR1CS_sub_mulModTargetT3
    (b : Var (MulModTargetT.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0)
    (ht : AffineW b.target) :
    IsR1CSCirc
      (assertion
        (MulModTargetT3.circuit3 secpParams gfMulD posOfMulD 5 vW3 vrW hgvW3
          hNfW3 hNfrW threeP2Limbs (by decide) (by decide)) b) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_mulModTargetT secpParams gfMulD posOfMulD 5 vW3 vrW hgvW3
      threeP2Limbs b ha hb hn hnd ht n)


/-- Cost of the folded polynomial-target certificate: one quotient wire, a
72-bit range check, the seven interpolated product coefficients, and a single
101-bit carry. -/
def mulModFoldTCount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFoldT - 1, qBitsFoldT⟩ + (⟨numLimbs, numLimbs⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFoldTL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFoldTL.Wf (3 - 2) 0 + 1⟩))

theorem costIs_mulModFoldT (input : Var MulModFoldT.Inputs (F circomPrime)) :
    CostIs (MulModFoldT.main input) mulModFoldTCount := by
  unfold MulModFoldT.main mulModFoldTCount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFoldT (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_crtMul _ _) fun Pc => ?_
  exact costIs_assertion_groupedEqXV 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT
    (by norm_num) _

theorem costIs_sub_mulModFoldT (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128)
    (b : Var MulModFoldT.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFoldT.circuit Ca Cb Nt Nt5 hcap hcapT hNt hNt5) b) mulModFoldTCount :=
  CostIs.assertion (fun n => costIs_mulModFoldT b n)

theorem affineW_foldLhsT (Pc : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (h : AffineW Pc) : AffineW (MulModFoldT.foldLhsT Pc) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 4 (by decide)))) (Affine.const _)
  · exact Affine.add (Affine.add (h 1 (by decide))
      (Affine.fconst_mul _ (h 5 (by decide)))) (Affine.const _)
  · exact Affine.add (Affine.add (h 2 (by decide))
      (Affine.fconst_mul _ (h 6 (by decide)))) (Affine.const _)
  · exact Affine.add (h 3 (by decide)) (Affine.const _)

theorem affineW_foldLhsC (d : Vector (Expression (F circomPrime)) numLimbs)
    (h : AffineW d) : AffineW (MulModFoldT.foldLhsC d) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;>
    exact Affine.add (h _ (by decide)) (Affine.const _)

theorem affineW_foldRhsT (q : Expression (F circomPrime)) (hq : Affine q)
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (ht : AffineW T) :
    AffineW (MulModFoldT.foldRhsT q T) := by
  intro i hi
  have hi4 : i < 4 := hi
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact Affine.add (Affine.mul_deg0 hq (degree_const _))
      (Affine.add (ht 0 (by decide)) (Affine.fconst_mul _ (ht 4 (by decide))))
  · exact Affine.add (Affine.mul_deg0 hq (degree_const _))
      (Affine.add (ht 1 (by decide)) (Affine.fconst_mul _ (ht 5 (by decide))))
  · exact Affine.add (Affine.mul_deg0 hq (degree_const _))
      (Affine.add (ht 2 (by decide)) (Affine.fconst_mul _ (ht 6 (by decide))))
  · exact Affine.add (Affine.mul_deg0 hq (degree_const _)) (ht 3 (by decide))

theorem isR1CS_mulModFoldT (input : Var MulModFoldT.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFoldT.main input) := by
  unfold MulModFoldT.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFoldT (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_crtMul _ _ ha hb) fun nPc => ?_
  exact isR1CS_assertion_groupedEqXV 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT
    (by norm_num) _
    (affineW_foldLhsC _ (affineW_crtMul_output input.a input.b _))
    (affineW_foldRhsT _ (Affine.var _) _ ht)

theorem isR1CS_sub_mulModFoldT (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128)
    (b : Var MulModFoldT.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (ht : AffineW b.target) :
    IsR1CSCirc (assertion (MulModFoldT.circuit Ca Cb Nt Nt5 hcap hcapT hNt hNt5) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFoldT b ha hb ht n)


/-! ## Quotient-inverted `MulModFoldT`

Same reclaim as for the base-`2^32` folds: the folded quotient is recovered as
an affine expression once the CRT product digits are allocated, so it is not
witnessed, and the native row of the grouped equality is implied and dropped. -/

def mulModFoldTInvCount : Count :=
  ⟨numLimbs, numLimbs⟩ + (⟨qBitsFoldT - 1, qBitsFoldT⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFoldTL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFoldTL.Wf (3 - 2) 0⟩)

def mulModFoldTInvCost : Count := ⟨171, 173⟩

theorem mulModFoldTInvCount_eq : mulModFoldTInvCount = mulModFoldTInvCost := by
  simp only [mulModFoldTInvCount, mulModFoldTInvCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFoldTL, wfFoldT, numLimbs]
  rfl

theorem costIs_mulModFoldTInv' (input : Var MulModFoldT.Inputs (F circomPrime)) :
    CostIs (MulModFoldT.mainInv input) mulModFoldTInvCount := by
  unfold MulModFoldT.mainInv mulModFoldTInvCount
  refine CostIs.bind (costIs_crtMul _ _) fun d => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFoldT (by decide) (by decide) _) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT
    (by norm_num) _

theorem costIs_mulModFoldTInv (input : Var MulModFoldT.Inputs (F circomPrime)) :
    CostIs (MulModFoldT.mainInv input) mulModFoldTInvCost :=
  mulModFoldTInvCount_eq ▸ costIs_mulModFoldTInv' input

theorem costIs_sub_mulModFoldTInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128)
    (b : Var MulModFoldT.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFoldT.circuitInv Ca Cb Nt Nt5 hcap hcapT hNt hNt5) b)
      mulModFoldTInvCost :=
  CostIs.assertion (fun n => costIs_mulModFoldTInv b n)

theorem affine_lhsPolyInvT (d : Vector (Expression (F circomPrime)) numLimbs)
    (hd : AffineW d) : Affine (MulModFoldT.lhsPolyInv d) := by
  unfold MulModFoldT.lhsPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldLhsC d hd)

theorem affine_targetPolyInvT (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1))
    (ht : AffineW T) : Affine (MulModFoldT.targetPolyInv T) := by
  unfold MulModFoldT.targetPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldRhsT 0 Affine.zero T ht)

theorem affine_qInvT (d : Vector (Expression (F circomPrime)) numLimbs) (hd : AffineW d)
    (T : Vector (Expression (F circomPrime)) (2 * numLimbs - 1)) (ht : AffineW T) :
    Affine (MulModFoldT.qInv d T) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPolyInvT d hd) (affine_targetPolyInvT T ht))

theorem isR1CS_mulModFoldTInv (input : Var MulModFoldT.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFoldT.mainInv input) := by
  unfold MulModFoldT.mainInv
  refine IsR1CSCirc.bind_out (isR1CS_crtMul _ _ ha hb) fun nd => ?_
  have hd : AffineW ((CrtMul.crtMul input.a input.b nd).1) :=
    affineW_crtMul_output input.a input.b nd
  have hq := affine_qInvT _ hd _ ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFoldT (by decide) (by decide) _ hq) fun _ => ?_
  exact isR1CS_assertion_groupedEqXVNoTop 64 gfFold posOfFold 3 vFoldTL vFoldTR hgvFoldT
    (by norm_num) _
    (affineW_foldLhsC _ hd)
    (affineW_foldRhsT _ hq _ ht)

theorem isR1CS_sub_mulModFoldTInv (Ca Cb Nt Nt5 : ℕ)
    (hcap : numLimbs * (Ca * Cb) ≤ 12 * 2 ^ 128)
    (hcapT : Nt ≤ 12 * 2 ^ 128) (hNt : Nt ≤ 12 * 2 ^ 128) (hNt5 : Nt5 ≤ 6 * 2 ^ 128)
    (b : Var MulModFoldT.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (ht : AffineW b.target) :
    IsR1CSCirc (assertion (MulModFoldT.circuitInv Ca Cb Nt Nt5 hcap hcapT hNt hNt5) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFoldTInv b ha hb ht n)


def divOrZeroF3Cost : Count := ⟨443, 445⟩

theorem costIs_divOrZeroF3 (input : Var DivOrZeroF3.Inputs (F circomPrime)) :
    CostIs (DivOrZeroF3.main input) divOrZeroF3Cost := by
  obtain ⟨sel, x, dyU, den⟩ := input
  rw [show divOrZeroF3Cost = ⟨2, 2⟩ + (⟨7, 7⟩ + (⟨7, 7⟩ +
      (⟨4, 0⟩ + (⟨252, 256⟩ +
        (mulModFoldTInvCost + Count.zero))))) from by decide]
  unfold DivOrZeroF3.main
  refine CostIs.bind (costIs_sub_isZeroFeSum _) fun z => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pxx => ?_
  refine CostIs.bind (costIs_sub_mux _) fun T => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divOrZeroF3 (input : Var DivOrZeroF3.Inputs (F circomPrime))
    (hsel : Affine input.sel) (hx : AffineW input.x)
    (hdyU : AffineW input.dyU) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZeroF3.main input) := by
  obtain ⟨sel, x, dyU, den⟩ := input
  unfold DivOrZeroF3.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFeSum _ hden) fun nz => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ?_ ?_) fun nPxx => ?_
  · exact hx
  · exact hx
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nT => ?_
  · exact hsel
  · refine AffineW.affineProvable ?_
    intro i hi
    rw [Vector.getElem_mapFinRange]
    exact Affine.fconst_mul _ (affineW_interpolatedMul_output _ _ _ i hi)
  · refine AffineW.affineProvable ?_
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · rename_i hlt
      exact hdyU i hlt
    · exact Affine.zero
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams _ (affineW_provableWitness_bigInt _ nl)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _ ?_ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact DivOrZeroF3.affineW_denSafeVec hden (affine_sub_isZeroFeSum _ nz)
  · exact (affineProvable_sub_mux _ nT).affineW
  exact IsR1CSCirc.pure _

theorem costIs_sub_divOrZeroF3 (b : Var DivOrZeroF3.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZeroF3.circuit b) divOrZeroF3Cost :=
  CostIs.subcircuit (fun n => costIs_divOrZeroF3 b n)

theorem isR1CS_sub_divOrZeroF3 (b : Var DivOrZeroF3.Inputs (F circomPrime))
    (hsel : Affine b.sel) (hx : AffineW b.x) (hdyU : AffineW b.dyU) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZeroF3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZeroF3 b hsel hx hdyU hden n)

theorem affineW_sub_divOrZeroF3 (b : Var DivOrZeroF3.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZeroF3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivOrZeroF3.circuit, DivOrZeroF3.elaborated]
  exact affineW_varFromOffset _ _



/-! ## 32-bit-limb gadgets (`Split32`, `MulModFold32`, `MulModSub2F32`, `DivOrZeroS32`) -/

/-! ## `Split32` -/

def split32Cost : Count := ⟨252, 256⟩

theorem costIs_split32 (x : Var Emu (F circomPrime)) :
    CostIs (Split32.main x) split32Cost := by
  rw [show split32Cost =
      ⟨1, 0⟩ + (⟨32 - 1, 32⟩ + (⟨32 - 1, 32⟩ +
      (⟨1, 0⟩ + (⟨32 - 1, 32⟩ + (⟨32 - 1, 32⟩ +
      (⟨1, 0⟩ + (⟨32 - 1, 32⟩ + (⟨32 - 1, 32⟩ +
      (⟨1, 0⟩ + (⟨32 - 1, 32⟩ + (⟨32 - 1, 32⟩ + Count.zero))))))))))) from by decide]
  unfold Split32.main
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessField _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 32 (by decide) (by decide) _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_split32 (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit Split32.circuit x) split32Cost :=
  CostIs.subcircuit fun n => costIs_split32 x n

theorem affine_hiExpr (x : Var Emu (F circomPrime)) (i : ℕ) (hi : i < numLimbs)
    (lo : Expression (F circomPrime)) (hx : Affine (x[i]'hi)) (hlo : Affine lo) :
    Affine (Split32.hiExpr x i hi lo) := by
  unfold Split32.hiExpr
  exact Affine.fconst_mul _ (Affine.sub hx hlo)

theorem isR1CS_split32 (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Split32.main x) := by
  unfold Split32.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun l0 => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _ (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _
      (affine_hiExpr x 0 (by decide) _ (hx 0 (by decide)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun l1 => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _ (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _
      (affine_hiExpr x 1 (by decide) _ (hx 1 (by decide)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun l2 => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _ (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _
      (affine_hiExpr x 2 (by decide) _ (hx 2 (by decide)) (Affine.var _))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun l3 => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _ (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck 32 (by decide) (by decide) _
      (affine_hiExpr x 3 (by decide) _ (hx 3 (by decide)) (Affine.var _))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_split32 (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit Split32.circuit x) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_split32 x hx n

/-- The eight 32-bit limbs handed back by `Split32` are affine in the input. -/
theorem affineW_split32_main_output (x : Var Emu (F circomPrime)) (hx : AffineW x) (n : ℕ) :
    AffineW ((Split32.main x).output n) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [Split32.main, circuit_norm]
  interval_cases i
  · exact Affine.var _
  · exact affine_hiExpr x 0 (by decide) _ (hx 0 (by decide)) (Affine.var _)
  · exact Affine.var _
  · exact affine_hiExpr x 1 (by decide) _ (hx 1 (by decide)) (Affine.var _)
  · exact Affine.var _
  · exact affine_hiExpr x 2 (by decide) _ (hx 2 (by decide)) (Affine.var _)
  · exact Affine.var _
  · exact affine_hiExpr x 3 (by decide) _ (hx 3 (by decide)) (Affine.var _)

theorem affineW_split32_output (x : Var Emu (F circomPrime)) (hx : AffineW x) (n : ℕ) :
    AffineW ((subcircuit Split32.circuit x).output n) := by
  have h : (subcircuit Split32.circuit x).output n = (Split32.main x).output n := by
    simp only [subcircuit, circuit_norm]
    exact (Split32.elaborated.output_eq x n).symm
  rw [h]
  exact affineW_split32_main_output x hx n

/-! ## `MulModFold32` -/

def mulModFold32Count : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold32 - 1, qBitsFold32⟩ + (⟨2 * 8 - 1, 2 * 8 - 1⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32L.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32L.Wf (3 - 2) 0 + 1⟩))

def mulModFold32Cost : Count := ⟨97, 99⟩

theorem mulModFold32Count_eq : mulModFold32Count = mulModFold32Cost := by
  simp only [mulModFold32Count, mulModFold32Cost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32L, wfFold32]
  rfl

theorem costIs_mulModFold32' (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (MulModFold32.main input) mulModFold32Count := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32.main mulModFold32Count
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck qBitsFold32 (by decide) (by decide) q)
    fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul a b) fun Pc => ?_
  exact costIs_assertion_groupedEqXV (L := 8) 32 gfFold32 posOfFold32 3 vFold32L vFold32R
    hgvFold32 (by norm_num) _

theorem costIs_mulModFold32 (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (MulModFold32.main input) mulModFold32Cost :=
  mulModFold32Count_eq ▸ costIs_mulModFold32' input

theorem costIs_assertion_mulModFold32 (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 69)
    (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32.circuit Ca Cb hcap) input) mulModFold32Cost :=
  CostIs.assertion (fun n => costIs_mulModFold32 input n)

theorem affineW_foldLhs32 (Pc : Vector (Expression (F circomPrime)) 15)
    (h : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    AffineW (MulModFold32.foldLhs32 Pc) := by
  intro i hi
  have hi8 : i < 8 := hi
  have hmid : ∀ (j k l : ℕ) (hj : j < 15) (hk : k < 15) (hl : l < 15) (c : ℕ),
      Affine ((Pc[j]'hj) + MulModFold32.c977E * (Pc[k]'hk) + (Pc[l]'hl)
        + MulModFold32.offE c) := by
    intro j k l hj hk hl c
    exact Affine.add (Affine.add (Affine.add (h j hj)
      (Affine.fconst_mul _ (h k hk))) (h l hl)) (Affine.const _)
  simp only [MulModFold32.foldLhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 8 (by decide)))) (Affine.const _)
  · exact hmid 1 9 8 (by decide) (by decide) (by decide) 1
  · exact hmid 2 10 9 (by decide) (by decide) (by decide) 2
  · exact hmid 3 11 10 (by decide) (by decide) (by decide) 3
  · exact hmid 4 12 11 (by decide) (by decide) (by decide) 4
  · exact hmid 5 13 12 (by decide) (by decide) (by decide) 5
  · exact hmid 6 14 13 (by decide) (by decide) (by decide) 6
  · exact Affine.add (Affine.add (h 7 (by decide)) (h 14 (by decide))) (Affine.const _)

theorem affineW_foldRhs32 (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Affine q) (ht : AffineW t) :
    AffineW (MulModFold32.foldRhs32 q t) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32.foldRhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 0 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 1 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 2 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 3 (by decide))
  · exact Affine.mul_fconst _ hq

theorem isR1CS_mulModFold32 (input : Var MulModFold32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32.main input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun q => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32 (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul a b ha hb) fun Pc => ?_
  refine isR1CS_assertion_groupedEqXV (L := 8) 32 gfFold32 posOfFold32 3 vFold32L vFold32R
    hgvFold32 (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32 _ (fun i hi => affineW_interpolatedMul_output a b Pc i hi)
  · exact affineW_foldRhs32 _ t (Affine.var _) ht

theorem isR1CS_assertion_mulModFold32 (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 69)
    (input : Var MulModFold32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32.circuit Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32 input ha hb ht n)

/-! ## Quotient-inverted `MulModFold32` -/

def mulModFold32InvCount : Count :=
  ⟨2 * 8 - 1, 2 * 8 - 1⟩ + (⟨qBitsFold32 - 1, qBitsFold32⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32L.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32L.Wf (3 - 2) 0⟩)

def mulModFold32InvCost : Count := ⟨96, 98⟩

theorem mulModFold32InvCount_eq : mulModFold32InvCount = mulModFold32InvCost := by
  simp only [mulModFold32InvCount, mulModFold32InvCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32L, wfFold32]
  rfl

theorem costIs_mulModFold32Inv' (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (MulModFold32.mainInv input) mulModFold32InvCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32.mainInv mulModFold32InvCount
  refine CostIs.bind (costIs_interpolatedMul a b) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold32 (by decide) (by decide)
      (MulModFold32.qInv Pc t)) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32 posOfFold32 3
    vFold32L vFold32R hgvFold32 (by norm_num) _

theorem costIs_mulModFold32Inv (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (MulModFold32.mainInv input) mulModFold32InvCost :=
  mulModFold32InvCount_eq ▸ costIs_mulModFold32Inv' input

theorem costIs_assertion_mulModFold32Inv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 69)
    (input : Var MulModFold32.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32.circuitInv Ca Cb hcap) input) mulModFold32InvCost :=
  CostIs.assertion (fun n => costIs_mulModFold32Inv input n)

theorem affine_targetPolyInv32 (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32.targetPolyInv t) := by
  unfold MulModFold32.targetPolyInv
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  simp only [MulModFold32.targetVecInv, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  interval_cases i
  · exact ht 0 (by decide)
  · exact Affine.zero
  · exact ht 1 (by decide)
  · exact Affine.zero
  · exact ht 2 (by decide)
  · exact Affine.zero
  · exact ht 3 (by decide)
  · exact Affine.zero

theorem affine_lhsPolyInv32 (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    Affine (MulModFold32.lhsPolyInv Pc) := by
  unfold MulModFold32.lhsPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldLhs32 Pc hPc)

theorem affine_qInv32 (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi))
    (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32.qInv Pc t) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPolyInv32 Pc hPc)
    (affine_targetPolyInv32 t ht))

theorem isR1CS_mulModFold32Inv (input : Var MulModFold32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32.mainInv input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32.mainInv
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul a b ha hb) fun nPc => ?_
  have hPc : AffineW ((MulMod.interpolatedMul a b).output nPc) :=
    affineW_interpolatedMul_output a b nPc
  have hq := affine_qInv32 ((MulMod.interpolatedMul a b).output nPc) hPc t ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32 (by decide) (by decide) _ hq)
    fun _ => ?_
  refine isR1CS_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32 posOfFold32 3
    vFold32L vFold32R hgvFold32 (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32 _ hPc
  · exact affineW_foldRhs32 _ t hq ht

theorem isR1CS_assertion_mulModFold32Inv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 69)
    (input : Var MulModFold32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32.circuitInv Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32Inv input ha hb ht n)

/-! ## `MulModFold32T` -/

def mulModFold32TCount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold32T - 1, qBitsFold32T⟩ + (⟨2 * 8 - 1, 2 * 8 - 1⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32TL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32TL.Wf (3 - 2) 0 + 1⟩))

def mulModFold32TCost : Count := ⟨93, 95⟩

theorem mulModFold32TCount_eq : mulModFold32TCount = mulModFold32TCost := by
  simp only [mulModFold32TCount, mulModFold32TCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32TL, wfFold32T]
  rfl

theorem costIs_mulModFold32T' (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (MulModFold32T.main input) mulModFold32TCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32T.main mulModFold32TCount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) q)
    fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul a b) fun Pc => ?_
  exact costIs_assertion_groupedEqXV (L := 8) 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
    hgvFold32T (by norm_num) _

theorem costIs_mulModFold32T (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (MulModFold32T.main input) mulModFold32TCost :=
  mulModFold32TCount_eq ▸ costIs_mulModFold32T' input

theorem costIs_assertion_mulModFold32T (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32T.circuit Ca Cb hcap) input) mulModFold32TCost :=
  CostIs.assertion (fun n => costIs_mulModFold32T input n)

theorem affineW_foldLhs32T (Pc : Vector (Expression (F circomPrime)) 15)
    (h : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    AffineW (MulModFold32T.foldLhs32 Pc) := by
  intro i hi
  have hi8 : i < 8 := hi
  have hmid : ∀ (j k l : ℕ) (hj : j < 15) (hk : k < 15) (hl : l < 15) (c : ℕ),
      Affine ((Pc[j]'hj) + MulModFold32T.c977E * (Pc[k]'hk) + (Pc[l]'hl)
        + MulModFold32T.offE c) := by
    intro j k l hj hk hl c
    exact Affine.add (Affine.add (Affine.add (h j hj)
      (Affine.fconst_mul _ (h k hk))) (h l hl)) (Affine.const _)
  simp only [MulModFold32T.foldLhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 8 (by decide)))) (Affine.const _)
  · exact hmid 1 9 8 (by decide) (by decide) (by decide) 1
  · exact hmid 2 10 9 (by decide) (by decide) (by decide) 2
  · exact hmid 3 11 10 (by decide) (by decide) (by decide) 3
  · exact hmid 4 12 11 (by decide) (by decide) (by decide) 4
  · exact hmid 5 13 12 (by decide) (by decide) (by decide) 5
  · exact hmid 6 14 13 (by decide) (by decide) (by decide) 6
  · exact Affine.add (Affine.add (h 7 (by decide)) (h 14 (by decide))) (Affine.const _)

theorem affineW_foldRhs32T (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Affine q) (ht : AffineW t) :
    AffineW (MulModFold32T.foldRhs32 q t) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32T.foldRhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 0 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 1 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 2 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 3 (by decide))
  · exact Affine.mul_fconst _ hq

theorem isR1CS_mulModFold32T (input : Var MulModFold32T.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32T.main input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32T.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun q => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul a b ha hb) fun Pc => ?_
  refine isR1CS_assertion_groupedEqXV (L := 8) 32 gfFold32T posOfFold32T 3 vFold32TL vFold32TR
    hgvFold32T (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32T _ (fun i hi => affineW_interpolatedMul_output a b Pc i hi)
  · exact affineW_foldRhs32T _ t (Affine.var _) ht

theorem isR1CS_assertion_mulModFold32T (Ca Cb : ℕ) (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32T.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32T.circuit Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32T input ha hb ht n)

/-! ## Quotient-inverted `MulModFold32T` -/

def mulModFold32TInvCount : Count :=
  ⟨2 * 8 - 1, 2 * 8 - 1⟩ + (⟨qBitsFold32T - 1, qBitsFold32T⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32TL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32TL.Wf (3 - 2) 0⟩)

def mulModFold32TInvCost : Count := ⟨92, 94⟩

theorem mulModFold32TInvCount_eq : mulModFold32TInvCount = mulModFold32TInvCost := by
  simp only [mulModFold32TInvCount, mulModFold32TInvCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32TL, wfFold32T]
  rfl

theorem costIs_mulModFold32TInv' (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (MulModFold32T.mainInv input) mulModFold32TInvCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32T.mainInv mulModFold32TInvCount
  refine CostIs.bind (costIs_interpolatedMul a b) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide)
      (MulModFold32T.qInv Pc t)) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32T posOfFold32T 3
    vFold32TL vFold32TR hgvFold32T (by norm_num) _

theorem costIs_mulModFold32TInv (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (MulModFold32T.mainInv input) mulModFold32TInvCost :=
  mulModFold32TInvCount_eq ▸ costIs_mulModFold32TInv' input

theorem costIs_assertion_mulModFold32TInv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32T.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32T.circuitInv Ca Cb hcap) input) mulModFold32TInvCost :=
  CostIs.assertion (fun n => costIs_mulModFold32TInv input n)

theorem affine_targetPolyInv (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32T.targetPolyInv t) := by
  unfold MulModFold32T.targetPolyInv
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  simp only [MulModFold32T.targetVecInv, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  interval_cases i
  · exact ht 0 (by decide)
  · exact Affine.zero
  · exact ht 1 (by decide)
  · exact Affine.zero
  · exact ht 2 (by decide)
  · exact Affine.zero
  · exact ht 3 (by decide)
  · exact Affine.zero

theorem affine_lhsPolyInv (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    Affine (MulModFold32T.lhsPolyInv Pc) := by
  unfold MulModFold32T.lhsPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldLhs32T Pc hPc)

theorem affine_qInv (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi))
    (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32T.qInv Pc t) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPolyInv Pc hPc) (affine_targetPolyInv t ht))

theorem isR1CS_mulModFold32TInv (input : Var MulModFold32T.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32T.mainInv input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32T.mainInv
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul a b ha hb) fun nPc => ?_
  have hPc : AffineW ((MulMod.interpolatedMul a b).output nPc) :=
    affineW_interpolatedMul_output a b nPc
  have hq := affine_qInv ((MulMod.interpolatedMul a b).output nPc) hPc t ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32T (by decide) (by decide) _ hq)
    fun _ => ?_
  refine isR1CS_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32T posOfFold32T 3
    vFold32TL vFold32TR hgvFold32T (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32T _ hPc
  · exact affineW_foldRhs32T _ t hq ht

theorem isR1CS_assertion_mulModFold32TInv (Ca Cb : ℕ)
    (hcap : 8 * (Ca * Cb) ≤ 2 ^ 67)
    (input : Var MulModFold32T.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32T.circuitInv Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32TInv input ha hb ht n)

/-! ## `MulModSub2F32` -/


/-! ## `MulModSub2F32` -/

def mulModSub2F32Cost : Count := ⟨356, 359⟩

theorem costIs_mulModSub2F32 (input : Var MulModSub2F32.Inputs (F circomPrime)) :
    CostIs (MulModSub2F32.main input) mulModSub2F32Cost := by
  obtain ⟨a, b, s1, s2⟩ := input
  rw [show mulModSub2F32Cost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (mulModFold32TInvCost + Count.zero)) from by decide]
  unfold MulModSub2F32.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32TInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModSub2F32 (input : Var MulModSub2F32.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSub2F32.circuit input) mulModSub2F32Cost :=
  CostIs.subcircuit fun n => costIs_mulModSub2F32 input n

theorem isR1CS_mulModSub2F32 (input : Var MulModSub2F32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (MulModSub2F32.main input) := by
  obtain ⟨a, b, s1, s2⟩ := input
  unfold MulModSub2F32.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_mulModFold32TInv _ _ _ _ ha hb ?_)
    fun _ => IsR1CSCirc.pure _
  intro i hi
  rw [Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ (hs1 i hi)) (hs2 i hi)
  exact affineW_provableWitness_bigInt _ nr i hi

theorem isR1CS_sub_mulModSub2F32 (input : Var MulModSub2F32.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (subcircuit MulModSub2F32.circuit input) :=
  IsR1CSCirc.subcircuit fun n => isR1CS_mulModSub2F32 input ha hb hs1 hs2 n

theorem affineW_sub_mulModSub2F32 (input : Var MulModSub2F32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSub2F32.circuit input).output n) := by
  simp only [circuit_norm, subcircuit, MulModSub2F32.circuit, MulModSub2F32.elaborated]
  exact affineW_varFromOffset _ _


/-- A compile-time constant in the 32-bit limb view is affine. -/
theorem affineW_emu32Const (v : ℕ) :
    AffineW (Limbs32.emu32Const v : Var (BigInt 8) (F circomPrime)) := by
  intro i hi
  unfold Limbs32.emu32Const
  rw [Vector.getElem_ofFn]
  exact Affine.const _

/-- The four 64-bit limbs recombined from eight affine 32-bit ones are affine. -/
theorem affineW_emuOf32 (v : Var (BigInt 8) (F circomPrime)) (hv : AffineW v) :
    AffineW (Limbs32.emuOf32 v) := by
  intro i hi
  have hi4 : i < 4 := hi
  rw [Limbs32.emuOf32, Vector.getElem_ofFn]
  simp only [Fin.val_mk]
  exact Affine.add (hv _ (by omega)) (Affine.fconst_mul _ (hv _ (by omega)))

def divOrZeroS32Cost : Count := ⟨442, 444⟩

theorem costIs_divOrZeroS32 (input : Var DivOrZeroS32.Inputs (F circomPrime)) :
    CostIs (DivOrZeroS32.main input) divOrZeroS32Cost := by
  obtain ⟨sel, x, dyU, den⟩ := input
  rw [show divOrZeroS32Cost = ⟨1, 0⟩ + (⟨0, 1⟩ + (⟨7, 7⟩ + (⟨7, 7⟩ +
      (⟨8, 0⟩ + (⟨248, 256⟩ +
        (mulModFoldTInvCost + Count.zero)))))) from by decide]
  unfold DivOrZeroS32.main
  refine CostIs.bind (CostIs.witnessField _) fun z => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pxx => ?_
  refine CostIs.bind (costIs_sub_mux _) fun T => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams32 _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_divOrZeroS32 (b : Var DivOrZeroS32.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZeroS32.circuit b) divOrZeroS32Cost :=
  CostIs.subcircuit (fun n => costIs_divOrZeroS32 b n)

theorem isR1CS_divOrZeroS32 (input : Var DivOrZeroS32.Inputs (F circomPrime))
    (hsel : Affine input.sel) (hx : AffineW input.x)
    (hdyU : AffineW input.dyU) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZeroS32.main input) := by
  obtain ⟨sel, x, dyU, den⟩ := input
  unfold DivOrZeroS32.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nz => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · exact isR1CSRow_mul (Affine.var _)
      ((((hden 0 (by decide)).add (hden 1 (by decide))).add (hden 2 (by decide))).add
        (hden 3 (by decide)))
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ?_ ?_) fun nPxx => ?_
  · exact hx
  · exact hx
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nT => ?_
  · exact hsel
  · refine AffineW.affineProvable ?_
    intro i hi
    rw [Vector.getElem_mapFinRange]
    exact Affine.fconst_mul _ (affineW_interpolatedMul_output _ _ _ i hi)
  · refine AffineW.affineProvable ?_
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · rename_i hlt
      exact hdyU i hlt
    · exact Affine.zero
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams32 _ (affineW_provableWitness_bigInt _ nl)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_sub_mulModFoldTInv _ _ _ _ _ _ _ _ _ ?_ ?_ ?_) fun _ => ?_
  · exact affineW_emuOf32 _ (affineW_provableWitness_bigInt _ nl)
  · exact DivOrZeroF3.affineW_denSafeVec hden (affine_witnessField_output _ nz)
  · exact (affineProvable_sub_mux _ nT).affineW
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_divOrZeroS32 (b : Var DivOrZeroS32.Inputs (F circomPrime))
    (hsel : Affine b.sel) (hx : AffineW b.x) (hdyU : AffineW b.dyU) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZeroS32.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZeroS32 b hsel hx hdyU hden n)

theorem affineW_sub_divOrZeroS32 (b : Var DivOrZeroS32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZeroS32.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivOrZeroS32.circuit, DivOrZeroS32.elaborated]
  exact affineW_varFromOffset _ _


def divOrZeroWCost : Count := ⟨751, 756⟩

theorem costIs_divOrZeroW (input : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (DivOrZeroW.main input) divOrZeroWCost := by
  obtain ⟨x, den⟩ := input
  rw [show divOrZeroWCost
        = ⟨2, 2⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 0⟩ + (⟨260, 265⟩ +
            (⟨477, 481⟩ + Count.zero))))) from by decide]
  unfold DivOrZeroW.main
  refine CostIs.bind (costIs_sub_isZeroFeSum _) fun z => ?_
  refine CostIs.bind (costIs_sub_mux _) fun denSafe => ?_
  refine CostIs.bind (costIs_sub_mux _) fun xSafe => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModTargetW _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divOrZeroW (input : Var DivOrZero.Inputs (F circomPrime))
    (hx : AffineW input.num) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZeroW.main input) := by
  obtain ⟨x, den⟩ := input
  unfold DivOrZeroW.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFeSum _ hden) fun nz => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nd => ?_
  · exact affine_sub_isZeroFeSum _ nz
  · exact (affineW_emuConst 1).affineProvable
  · exact hden.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nx => ?_
  · exact affine_sub_isZeroFeSum _ nz
  · exact (affineW_emuConst 0).affineProvable
  · exact hx.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nl)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_sub_mulModTargetW _ _ _ _ ?_ ?_ ?_ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact (affineProvable_sub_mux _ nd).affineW
  · exact affineW_pConst
  · exact degree_pConst
  · exact (affineProvable_sub_mux _ nx).affineW
  exact IsR1CSCirc.pure _

theorem costIs_sub_divOrZeroW (b : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZeroW.circuit b) divOrZeroWCost :=
  CostIs.subcircuit (fun n => costIs_divOrZeroW b n)

theorem isR1CS_sub_divOrZeroW (b : Var DivOrZero.Inputs (F circomPrime))
    (hx : AffineW b.num) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZeroW.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZeroW b hx hden n)

theorem affineW_sub_divOrZeroW (b : Var DivOrZero.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZeroW.circuit b).output n).lam := by
  simp only [circuit_norm, subcircuit, DivOrZeroW.circuit, DivOrZeroW.elaborated]
  exact affineW_varFromOffset _ _

theorem affine_sub_divOrZeroW_isZero (b : Var DivOrZero.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit DivOrZeroW.circuit b).output n).isZero := by
  simp only [circuit_norm, subcircuit, DivOrZeroW.circuit, DivOrZeroW.elaborated]
  exact Affine.var _


def toBytesCost : Count := ⟨256, 260⟩

theorem costIs_toBytes (x : Var Emu (F circomPrime)) :
    CostIs (ToBytes.main x) toBytesCost := by
  rw [show toBytesCost
        = ⟨32, 0⟩ + (⟨32 * (8 - 1), 32 * 8⟩ + (⟨4 * 0, 4 * 1⟩ + Count.zero)) from by decide]
  unfold ToBytes.main
  refine CostIs.bind (CostIs.provableWitness _) fun bytes => ?_
  refine CostIs.bind
    (CostIs.forEach fun a n => costIs_assertion_implicitRangeCheck 8 (by decide) (by decide) a n)
    fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_toBytes (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ToBytes.main x) := by
  unfold ToBytes.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nb => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine isR1CS_assertion_implicitRangeCheck 8 (by decide) (by decide) _ ?_ k
    exact (affineProvable_provableWitness _ nb).affineW i.val i.isLt
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun k j => ?_
  refine IsR1CSCirc.assertZero ?_ j
  rw [Vector.getElem_ofFn]
  refine isR1CSRow_of_affine (Affine.sub ?_ (hx _ (by exact k.isLt)))
  refine affine_finFoldl' _ _ Affine.zero fun acc t hacc => ?_
  exact Affine.add hacc
    (Affine.mul_deg0 ((affineProvable_provableWitness _ nb).affineW _ (by
      have hk := k.isLt; have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega)) (degree_const _))

theorem costIs_sub_toBytes (b : Var Emu (F circomPrime)) :
    CostIs (subcircuit ToBytes.circuit b) toBytesCost :=
  CostIs.subcircuit (fun n => costIs_toBytes b n)

theorem isR1CS_sub_toBytes (b : Var Emu (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit ToBytes.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_toBytes b hb n)

theorem affineW_sub_toBytes (b : Var Emu (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ToBytes.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, ToBytes.circuit, ToBytes.elaborated]
  exact affineW_varFromOffset _ _


def AffineFP (v : Var FlaggedPoint (F circomPrime)) : Prop :=
  AffineW v.x ∧ AffineW v.y ∧ Affine v.isInf

def AffineTableV (tx ty : Vector (Emu (Expression (F circomPrime))) 16)
    (tinf : Vector (Expression (F circomPrime)) 16) : Prop :=
  (∀ (i : ℕ) (h : i < 16), AffineW (tx[i]'h)) ∧
  (∀ (i : ℕ) (h : i < 16), AffineW (ty[i]'h)) ∧
  (∀ (i : ℕ) (h : i < 16), Affine (tinf[i]'h))

theorem AffineFP.of_affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineProvable v) : AffineFP v := by
  have hflat : AffineW
      (v.x ++ (v.y ++ #v[v.isInf]) :
        fields (numLimbs + (numLimbs + 1)) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i (by exact hi)
  refine ⟨AffineW.left_of_append hflat,
    AffineW.left_of_append (AffineW.right_of_append hflat), ?_⟩
  have h1 := AffineW.right_of_append (AffineW.right_of_append hflat) 0 (by decide)
  simpa using h1

theorem AffineW.append {m n : ℕ}
    {a : fields m (Expression (F circomPrime))} {b : fields n (Expression (F circomPrime))}
    (ha : AffineW a) (hb : AffineW b) :
    AffineW (a ++ b : fields (m + n) (Expression (F circomPrime))) := by
  intro i hi
  rw [Vector.getElem_append]
  split
  · exact ha _ _
  · exact hb _ _

theorem affineW_singleton {e : Expression (F circomPrime)} (he : Affine e) :
    AffineW (#v[e] : fields 1 (Expression (F circomPrime))) := by
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  simpa using he

theorem AffineFP.affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineFP v) : AffineProvable v := by
  obtain ⟨hx, hy, hi⟩ := h
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

theorem affineFP_infConst : AffineFP (infConst : Var FlaggedPoint (F circomPrime)) :=
  ⟨affineW_emuConst 0, affineW_emuConst 0, Affine.const 1⟩

theorem affineProvable_infConst :
    AffineProvable (infConst : Var FlaggedPoint (F circomPrime)) :=
  affineFP_infConst.affineProvable


def oppYCost : Count := ⟨6, 6⟩

theorem costIs_oppY (input : Var OppY.Inputs (F circomPrime)) :
    CostIs (OppY.main input) oppYCost := by
  rw [show oppYCost = ⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 0⟩ + (⟨1, 1⟩ +
      (⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + Count.zero))))))) from by decide]
  unfold OppY.main
  refine CostIs.bind (costIs_assignEqField _) fun lo2 => ?_
  refine CostIs.bind (costIs_assignEqField _) fun w => ?_
  refine CostIs.bind (CostIs.witnessField _) fun t => ?_
  refine CostIs.bind (costIs_assignEqField _) fun v => ?_
  refine CostIs.bind (CostIs.witnessField _) fun uInv => ?_
  refine CostIs.bind (costIs_assignEqField _) fun z => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_oppY (input : Var OppY.Inputs (F circomPrime)) :
    CostIs (subcircuit OppY.circuit input) oppYCost :=
  CostIs.subcircuit (fun n => costIs_oppY input n)

private theorem affine_oppY_lowExpr (a b : Var Emu (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) : Affine (OppY.lowExpr a b) := by
  unfold OppY.lowExpr
  exact Affine.add (Affine.add (ha 0 (by decide)) (hb 0 (by decide)))
    (Affine.fconst_mul _ (Affine.add (ha 1 (by decide)) (hb 1 (by decide))))

private theorem affine_oppY_highExpr (a b : Var Emu (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) : Affine (OppY.highExpr a b) := by
  unfold OppY.highExpr
  exact Affine.add (Affine.add (ha 2 (by decide)) (hb 2 (by decide)))
    (Affine.fconst_mul _ (Affine.add (ha 3 (by decide)) (hb 3 (by decide))))

theorem isR1CS_oppY (input : Var OppY.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (OppY.main input) := by
  obtain ⟨a, b⟩ := input
  have hloA : Affine (OppY.lowExpr a b) := affine_oppY_lowExpr a b ha hb
  have hhiA : Affine (OppY.highExpr a b) := affine_oppY_highExpr a b ha hb
  unfold OppY.main
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) hloA hloA) fun nlo2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_mul (Affine.var w)
      (Affine.sub (affine_assignEq_output _ nlo2)
        (Affine.fconst_mul _ hloA))
      (Affine.sub hloA (Affine.const _))) fun nw => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nt => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (Affine.var _)
      (Affine.sub (Affine.sub hhiA
          (Affine.fconst_mul _ (affine_assignEq_output _ nlo2)))
        (Affine.fconst_mul _ hloA))) fun nv => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun ni => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_one_sub_mul (Affine.var w)
      (Affine.add (affine_assignEq_output _ nw) (Affine.var _)) (Affine.var _)) fun nz => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (Affine.var _) (affine_assignEq_output _ nw))) fun _ => ?_
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul (Affine.var _)
    (Affine.sub (Affine.sub hhiA
        (Affine.fconst_mul _ (affine_assignEq_output _ nlo2)))
      (Affine.fconst_mul _ hloA)))) fun _ =>
    IsR1CSCirc.pure _

theorem isR1CS_sub_oppY (input : Var OppY.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (subcircuit OppY.circuit input) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_oppY input ha hb n)

theorem affine_sub_oppY (input : Var OppY.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit OppY.circuit input).output n) := by
  simp only [circuit_norm, subcircuit, OppY.circuit, OppY.elaborated]
  exact Affine.var _


/-! ## `CancelLow` (two-row cancellation detector) -/

def cancelLowCost : Count := ⟨2, 2⟩

theorem costIs_cancelLow (input : Var CancelLow.Inputs (F circomPrime)) :
    CostIs (CancelLow.main input) cancelLowCost := by
  rw [show cancelLowCost = ⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + Count.zero)) from by decide]
  unfold CancelLow.main
  refine CostIs.bind (CostIs.witnessField _) fun t => ?_
  refine CostIs.bind (costIs_assignEqField _) fun c => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_cancelLow (input : Var CancelLow.Inputs (F circomPrime)) :
    CostIs (subcircuit CancelLow.circuit input) cancelLowCost :=
  CostIs.subcircuit (fun n => costIs_cancelLow input n)

theorem isR1CS_cancelLow (input : Var CancelLow.Inputs (F circomPrime))
    (hsx : Affine input.sameX) (hy1 : AffineW input.y1) (hy2 : AffineW input.y2) :
    IsR1CSCirc (CancelLow.main input) := by
  obtain ⟨sameX, y1, y2⟩ := input
  have hd : Affine (y1[0] - y2[0] : Expression (F circomPrime)) :=
    Affine.sub (hy1 0 (by decide)) (hy2 0 (by decide))
  unfold CancelLow.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nt => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) hd (Affine.var _)) fun nc => ?_
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul hd (Affine.sub hsx (affine_assignEq_output _ nc)))) fun _ =>
    IsR1CSCirc.pure _

theorem isR1CS_sub_cancelLow (input : Var CancelLow.Inputs (F circomPrime))
    (hsx : Affine input.sameX) (hy1 : AffineW input.y1) (hy2 : AffineW input.y2) :
    IsR1CSCirc (subcircuit CancelLow.circuit input) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_cancelLow input hsx hy1 hy2 n)

theorem affine_sub_cancelLow (input : Var CancelLow.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit CancelLow.circuit input).output n) := by
  simp only [circuit_norm, subcircuit, CancelLow.circuit, CancelLow.elaborated]
  exact Affine.var _


/-! ## `MulModTargetD3` (triply-unreduced multiplicand) -/

/-- Count of `MulModTargetD3.main`: the `MulModTargetD` pieces with a two-bit
top quotient — one extra cell (`u`) and one extra pin row. -/
def mulModTargetD3Count (m B : ℕ) (Wf : ℕ → ℕ) (G : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨1, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ +
    (⟨m * (B - 1), m * B⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
      ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
        GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩))))))

theorem costIs_mulModTargetD3 (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m - 1))
    (input : Var (MulModTarget.Inputs m) (F circomPrime)) :
    CostIs (MulModTargetD3.main P gf posOf G V VR hgv c input)
      (mulModTargetD3Count m P.B V.Wf G) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetD3.main mulModTargetD3Count
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun qh => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun u => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  exact costIs_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _

theorem costIs_sub_mulModTargetD3 (c : Vector (F circomPrime) 7) (hB2 : 3 ≤ secpParams.B)
    (hp16 : 2 ^ (2 * secpParams.B) * (numLimbs + 1) * 16 < circomPrime)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime)) :
    CostIs
      (assertion
        (MulModTargetD3.circuit secpParams gfMulD3 posOfMulD3 5 vMulD3 vrMulD3 hgvMulD3
          hNfMulD3 hNfrMulD3 c hB2 hp16) b)
      (mulModTargetD3Count numLimbs secpParams.B vMulD3.Wf 5) :=
  CostIs.assertion
    (fun n => costIs_mulModTargetD3 secpParams gfMulD3 posOfMulD3 5 vMulD3 vrMulD3 hgvMulD3 c b n)

theorem isR1CS_mulModTargetD3 (P : BigIntParams circomPrime m)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime (2 * m) P.B gf posOf G V VR) [NeZero m]
    (c : Vector (F circomPrime) (2 * m - 1))
    (input : Var (MulModTarget.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hnd : ∀ j (hj : j < m), degree input.modulus[j] = 0)
    (ht : AffineW input.target) :
    IsR1CSCirc (MulModTargetD3.main P gf posOf G V VR hgv c input) := by
  letI : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩
  unfold MulModTargetD3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nqh => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nu => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_sub_mul (affine_provableWitness_field _ nu)
      (affine_provableWitness_field _ nqh)
      (Affine.sub (affine_provableWitness_field _ nqh) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nu)
      (Affine.sub (affine_provableWitness_field _ nqh) (Affine.const 2)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_
  · intro i hi
    simp only [MulModTargetD3.padD, Vector.getElem_mapFinRange i hi]
    split
    · rename_i hlt
      simp only [MulMod.lVecC, Vector.getElem_mapFinRange i hlt]
      exact Affine.add (affineW_interpolatedMul_output input.a input.b _ i hlt) (Affine.const _)
    · exact Affine.zero
  · intro i hi
    simp only [MulModTargetD3.sVecTD, Vector.getElem_mapFinRange i hi]
    refine Affine.add ?_ ?_
    · split
      · rename_i hlt
        simp only [MulMod.sVecT, Vector.getElem_mapFinRange i hlt]
        split
        · rename_i hm
          exact Affine.add
            (affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hlt)
            (ht i (by assumption))
        · exact affineW_bigIntMulNoReduce _ _ (affineW_provableWitness_bigInt _ nq) hnd i hlt
      · exact Affine.zero
    · split
      · rename_i hm
        exact Affine.mul_deg0 (affine_provableWitness_field _ nqh) (hnd (i - m) hm.2)
      · exact Affine.zero

theorem isR1CS_sub_mulModTargetD3 (c : Vector (F circomPrime) 7) (hB2 : 3 ≤ secpParams.B)
    (hp16 : 2 ^ (2 * secpParams.B) * (numLimbs + 1) * 16 < circomPrime)
    (b : Var (MulModTarget.Inputs numLimbs) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus)
    (hnd : ∀ j (hj : j < numLimbs), degree b.modulus[j] = 0)
    (ht : AffineW b.target) :
    IsR1CSCirc
      (assertion
        (MulModTargetD3.circuit secpParams gfMulD3 posOfMulD3 5 vMulD3 vrMulD3 hgvMulD3
          hNfMulD3 hNfrMulD3 c hB2 hp16) b) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_mulModTargetD3 secpParams gfMulD3 posOfMulD3 5 vMulD3 vrMulD3 hgvMulD3
      c b ha hb hn hnd ht n)

/-! ## `MulModFold32M` (mixed base-`2^32` fold: 32-bit `a`, re-read 64-bit `b`) -/

def mulModFold32MCount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold32M - 1, qBitsFold32M⟩ + (⟨14, 14⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32ML.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32ML.Wf (3 - 2) 0 + 1⟩))

def mulModFold32MCost : Count := ⟨159, 161⟩

theorem mulModFold32MCount_eq : mulModFold32MCount = mulModFold32MCost := by
  simp only [mulModFold32MCount, mulModFold32MCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32ML, wfFold32M]
  rfl

theorem costIs_mulModFold32M' (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (MulModFold32M.main input) mulModFold32MCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32M.main mulModFold32MCount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck qBitsFold32M (by decide) (by decide) q)
    fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul14 a b) fun Pc => ?_
  exact costIs_assertion_groupedEqXV (L := 8) 32 gfFold32M posOfFold32M 3 vFold32ML vFold32MR
    hgvFold32M (by norm_num) _

theorem costIs_mulModFold32M (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (MulModFold32M.main input) mulModFold32MCost :=
  mulModFold32MCount_eq ▸ costIs_mulModFold32M' input

theorem costIs_assertion_mulModFold32M (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 99)
    (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32M.circuit Ca Cb hcap) input) mulModFold32MCost :=
  CostIs.assertion (fun n => costIs_mulModFold32M input n)

theorem affineW_foldLhs32M (Pc : Vector (Expression (F circomPrime)) 15)
    (h : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    AffineW (MulModFold32M.foldLhs32 Pc) := by
  intro i hi
  have hi8 : i < 8 := hi
  have hmid : ∀ (j k l : ℕ) (hj : j < 15) (hk : k < 15) (hl : l < 15) (c : ℕ),
      Affine ((Pc[j]'hj) + MulModFold32M.c977E * (Pc[k]'hk) + (Pc[l]'hl)
        + MulModFold32M.offE c) := by
    intro j k l hj hk hl c
    exact Affine.add (Affine.add (Affine.add (h j hj)
      (Affine.fconst_mul _ (h k hk))) (h l hl)) (Affine.const _)
  simp only [MulModFold32M.foldLhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 8 (by decide)))) (Affine.const _)
  · exact hmid 1 9 8 (by decide) (by decide) (by decide) 1
  · exact hmid 2 10 9 (by decide) (by decide) (by decide) 2
  · exact hmid 3 11 10 (by decide) (by decide) (by decide) 3
  · exact hmid 4 12 11 (by decide) (by decide) (by decide) 4
  · exact hmid 5 13 12 (by decide) (by decide) (by decide) 5
  · exact hmid 6 14 13 (by decide) (by decide) (by decide) 6
  · exact Affine.add (Affine.add (h 7 (by decide)) (h 14 (by decide))) (Affine.const _)

theorem affineW_foldRhs32M (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Affine q) (ht : AffineW t) :
    AffineW (MulModFold32M.foldRhs32 q t) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32M.foldRhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 0 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 1 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 2 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 3 (by decide))
  · exact Affine.mul_fconst _ hq

theorem affineW_expand32 (v : Var Emu (F circomPrime)) (hv : AffineW v) :
    AffineW (MulModFold32M.expand32 v) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32M.expand32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact hv 0 (by decide)
  · exact Affine.const _
  · exact hv 1 (by decide)
  · exact Affine.const _
  · exact hv 2 (by decide)
  · exact Affine.const _
  · exact hv 3 (by decide)
  · exact Affine.const _

theorem isR1CS_mulModFold32M (input : Var MulModFold32M.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32M.main input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32M.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun q => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32M (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul14 a b ha hb) fun Pc => ?_
  refine isR1CS_assertion_groupedEqXV (L := 8) 32 gfFold32M posOfFold32M 3 vFold32ML vFold32MR
    hgvFold32M (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32M _ (fun i hi => affineW_interpolatedMul14_output a b Pc i hi)
  · exact affineW_foldRhs32M _ t (Affine.var _) ht

theorem isR1CS_assertion_mulModFold32M (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 99)
    (input : Var MulModFold32M.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32M.circuit Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32M input ha hb ht n)

/-! ## Quotient-inverted `MulModFold32M`

Same reclaim as for `MulModFold32`: the folded quotient is recovered as an
affine expression once the sparse interpolated product is allocated, so it is
not witnessed, and the native row of the grouped equality is implied and
dropped. -/

def mulModFold32MInvCount : Count :=
  ⟨14, 14⟩ + (⟨qBitsFold32M - 1, qBitsFold32M⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32ML.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32ML.Wf (3 - 2) 0⟩)

def mulModFold32MInvCost : Count := ⟨158, 160⟩

theorem mulModFold32MInvCount_eq : mulModFold32MInvCount = mulModFold32MInvCost := by
  simp only [mulModFold32MInvCount, mulModFold32MInvCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32ML, wfFold32M]
  rfl

theorem costIs_mulModFold32MInv' (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (MulModFold32M.mainInv input) mulModFold32MInvCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32M.mainInv mulModFold32MInvCount
  refine CostIs.bind (costIs_interpolatedMul14 a b) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold32M (by decide) (by decide)
      (MulModFold32M.qInv Pc t)) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32M posOfFold32M 3
    vFold32ML vFold32MR hgvFold32M (by norm_num) _

theorem costIs_mulModFold32MInv (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (MulModFold32M.mainInv input) mulModFold32MInvCost :=
  mulModFold32MInvCount_eq ▸ costIs_mulModFold32MInv' input

theorem costIs_assertion_mulModFold32MInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 99)
    (input : Var MulModFold32M.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32M.circuitInv Ca Cb hcap) input) mulModFold32MInvCost :=
  CostIs.assertion (fun n => costIs_mulModFold32MInv input n)

theorem affine_targetPolyInv32M (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32M.targetPolyInv t) := by
  unfold MulModFold32M.targetPolyInv
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  simp only [MulModFold32M.targetVecInv, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  interval_cases i
  · exact ht 0 (by decide)
  · exact Affine.zero
  · exact ht 1 (by decide)
  · exact Affine.zero
  · exact ht 2 (by decide)
  · exact Affine.zero
  · exact ht 3 (by decide)
  · exact Affine.zero

theorem affine_lhsPolyInv32M (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    Affine (MulModFold32M.lhsPolyInv Pc) := by
  unfold MulModFold32M.lhsPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldLhs32M Pc hPc)

theorem affine_qInv32M (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi))
    (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32M.qInv Pc t) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPolyInv32M Pc hPc) (affine_targetPolyInv32M t ht))

theorem isR1CS_mulModFold32MInv (input : Var MulModFold32M.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32M.mainInv input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32M.mainInv
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul14 a b ha hb) fun nPc => ?_
  have hPc : AffineW ((MulMod.interpolatedMul14 a b).output nPc) :=
    affineW_interpolatedMul14_output a b nPc
  have hq := affine_qInv32M ((MulMod.interpolatedMul14 a b).output nPc) hPc t ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32M (by decide) (by decide) _ hq)
    fun _ => ?_
  refine isR1CS_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32M posOfFold32M 3
    vFold32ML vFold32MR hgvFold32M (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32M _ hPc
  · exact affineW_foldRhs32M _ t hq ht

theorem isR1CS_assertion_mulModFold32MInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 99)
    (input : Var MulModFold32M.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32M.circuitInv Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32MInv input ha hb ht n)


/-! ## `MulModFold32N` (mixed base-`2^32` fold: 32-bit `a`, re-read 64-bit `b`) -/

def mulModFold32NCount : Count :=
  ⟨1, 0⟩ + (⟨qBitsFold32N - 1, qBitsFold32N⟩ + (⟨14, 14⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32NL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32NL.Wf (3 - 2) 0 + 1⟩))

def mulModFold32NCost : Count := ⟨157, 159⟩

theorem mulModFold32NCount_eq : mulModFold32NCount = mulModFold32NCost := by
  simp only [mulModFold32NCount, mulModFold32NCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32NL, wfFold32N]
  rfl

theorem costIs_mulModFold32N' (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (MulModFold32N.main input) mulModFold32NCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32N.main mulModFold32NCount
  refine CostIs.bind (CostIs.witnessField _) fun q => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck qBitsFold32N (by decide) (by decide) q)
    fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul14 a b) fun Pc => ?_
  exact costIs_assertion_groupedEqXV (L := 8) 32 gfFold32N posOfFold32N 3 vFold32NL vFold32NR
    hgvFold32N (by norm_num) _

theorem costIs_mulModFold32N (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (MulModFold32N.main input) mulModFold32NCost :=
  mulModFold32NCount_eq ▸ costIs_mulModFold32N' input

theorem costIs_assertion_mulModFold32N (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 98)
    (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32N.circuit Ca Cb hcap) input) mulModFold32NCost :=
  CostIs.assertion (fun n => costIs_mulModFold32N input n)

theorem affineW_foldLhs32N (Pc : Vector (Expression (F circomPrime)) 15)
    (h : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    AffineW (MulModFold32N.foldLhs32 Pc) := by
  intro i hi
  have hi8 : i < 8 := hi
  have hmid : ∀ (j k l : ℕ) (hj : j < 15) (hk : k < 15) (hl : l < 15) (c : ℕ),
      Affine ((Pc[j]'hj) + MulModFold32N.c977E * (Pc[k]'hk) + (Pc[l]'hl)
        + MulModFold32N.offE c) := by
    intro j k l hj hk hl c
    exact Affine.add (Affine.add (Affine.add (h j hj)
      (Affine.fconst_mul _ (h k hk))) (h l hl)) (Affine.const _)
  simp only [MulModFold32N.foldLhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.add (h 0 (by decide))
      (Affine.fconst_mul _ (h 8 (by decide)))) (Affine.const _)
  · exact hmid 1 9 8 (by decide) (by decide) (by decide) 1
  · exact hmid 2 10 9 (by decide) (by decide) (by decide) 2
  · exact hmid 3 11 10 (by decide) (by decide) (by decide) 3
  · exact hmid 4 12 11 (by decide) (by decide) (by decide) 4
  · exact hmid 5 13 12 (by decide) (by decide) (by decide) 5
  · exact hmid 6 14 13 (by decide) (by decide) (by decide) 6
  · exact Affine.add (Affine.add (h 7 (by decide)) (h 14 (by decide))) (Affine.const _)

theorem affineW_foldRhs32N (q : Expression (F circomPrime)) (t : Var Emu (F circomPrime))
    (hq : Affine q) (ht : AffineW t) :
    AffineW (MulModFold32N.foldRhs32 q t) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32N.foldRhs32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 0 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 1 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 2 (by decide))
  · exact Affine.mul_fconst _ hq
  · exact Affine.add (Affine.mul_fconst _ hq) (ht 3 (by decide))
  · exact Affine.mul_fconst _ hq

theorem affineW_expand32N (v : Var Emu (F circomPrime)) (hv : AffineW v) :
    AffineW (MulModFold32N.expand32 v) := by
  intro i hi
  have hi8 : i < 8 := hi
  simp only [MulModFold32N.expand32, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  interval_cases i
  · exact hv 0 (by decide)
  · exact Affine.const _
  · exact hv 1 (by decide)
  · exact Affine.const _
  · exact hv 2 (by decide)
  · exact Affine.const _
  · exact hv 3 (by decide)
  · exact Affine.const _

theorem isR1CS_mulModFold32N (input : Var MulModFold32N.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32N.main input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32N.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun q => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32N (by decide) (by decide) _
      (Affine.var _)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul14 a b ha hb) fun Pc => ?_
  refine isR1CS_assertion_groupedEqXV (L := 8) 32 gfFold32N posOfFold32N 3 vFold32NL vFold32NR
    hgvFold32N (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32N _ (fun i hi => affineW_interpolatedMul14_output a b Pc i hi)
  · exact affineW_foldRhs32N _ t (Affine.var _) ht

theorem isR1CS_assertion_mulModFold32N (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 98)
    (input : Var MulModFold32N.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32N.circuit Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32N input ha hb ht n)

/-! ## Quotient-inverted `MulModFold32N`

Same reclaim as for `MulModFold32`: the folded quotient is recovered as an
affine expression once the sparse interpolated product is allocated, so it is
not witnessed, and the native row of the grouped equality is implied and
dropped. -/

def mulModFold32NInvCount : Count :=
  ⟨14, 14⟩ + (⟨qBitsFold32N - 1, qBitsFold32N⟩ +
    ⟨GroupedEqXV.widthAllocFrom vFold32NL.Wf (3 - 2) 0,
     GroupedEqXV.widthConsFrom vFold32NL.Wf (3 - 2) 0⟩)

def mulModFold32NInvCost : Count := ⟨156, 158⟩

theorem mulModFold32NInvCount_eq : mulModFold32NInvCount = mulModFold32NInvCost := by
  simp only [mulModFold32NInvCount, mulModFold32NInvCost, GroupedEqXV.widthAllocFrom,
    GroupedEqXV.widthConsFrom, vFold32NL, wfFold32N]
  rfl

theorem costIs_mulModFold32NInv' (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (MulModFold32N.mainInv input) mulModFold32NInvCount := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32N.mainInv mulModFold32NInvCount
  refine CostIs.bind (costIs_interpolatedMul14 a b) fun Pc => ?_
  refine CostIs.bind
    (costIs_assertion_implicitRangeCheck qBitsFold32N (by decide) (by decide)
      (MulModFold32N.qInv Pc t)) fun _ => ?_
  exact costIs_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32N posOfFold32N 3
    vFold32NL vFold32NR hgvFold32N (by norm_num) _

theorem costIs_mulModFold32NInv (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (MulModFold32N.mainInv input) mulModFold32NInvCost :=
  mulModFold32NInvCount_eq ▸ costIs_mulModFold32NInv' input

theorem costIs_assertion_mulModFold32NInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 98)
    (input : Var MulModFold32N.Inputs (F circomPrime)) :
    CostIs (assertion (MulModFold32N.circuitInv Ca Cb hcap) input) mulModFold32NInvCost :=
  CostIs.assertion (fun n => costIs_mulModFold32NInv input n)

theorem affine_targetPolyInv32N (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32N.targetPolyInv t) := by
  unfold MulModFold32N.targetPolyInv
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  simp only [MulModFold32N.targetVecInv, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  interval_cases i
  · exact ht 0 (by decide)
  · exact Affine.zero
  · exact ht 1 (by decide)
  · exact Affine.zero
  · exact ht 2 (by decide)
  · exact Affine.zero
  · exact ht 3 (by decide)
  · exact Affine.zero

theorem affine_lhsPolyInv32N (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi)) :
    Affine (MulModFold32N.lhsPolyInv Pc) := by
  unfold MulModFold32N.lhsPolyInv
  exact affine_polyEvalExpr _ _ (affineW_foldLhs32N Pc hPc)

theorem affine_qInv32N (Pc : Vector (Expression (F circomPrime)) 15)
    (hPc : ∀ (i : ℕ) (hi : i < 15), Affine (Pc[i]'hi))
    (t : Var Emu (F circomPrime)) (ht : AffineW t) :
    Affine (MulModFold32N.qInv Pc t) :=
  Affine.fconst_mul _ (Affine.sub (affine_lhsPolyInv32N Pc hPc) (affine_targetPolyInv32N t ht))

theorem isR1CS_mulModFold32NInv (input : Var MulModFold32N.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (MulModFold32N.mainInv input) := by
  obtain ⟨a, b, t⟩ := input
  unfold MulModFold32N.mainInv
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul14 a b ha hb) fun nPc => ?_
  have hPc : AffineW ((MulMod.interpolatedMul14 a b).output nPc) :=
    affineW_interpolatedMul14_output a b nPc
  have hq := affine_qInv32N ((MulMod.interpolatedMul14 a b).output nPc) hPc t ht
  refine IsR1CSCirc.bind
    (isR1CS_assertion_implicitRangeCheck qBitsFold32N (by decide) (by decide) _ hq)
    fun _ => ?_
  refine isR1CS_assertion_groupedEqXVNoTop (L := 8) 32 gfFold32N posOfFold32N 3
    vFold32NL vFold32NR hgvFold32N (by norm_num) _ ?_ ?_
  · exact affineW_foldLhs32N _ hPc
  · exact affineW_foldRhs32N _ t hq ht

theorem isR1CS_assertion_mulModFold32NInv (Ca Cb : ℕ) (hcap : 4 * (Ca * Cb) ≤ 3 * 2 ^ 98)
    (input : Var MulModFold32N.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (ht : AffineW input.target) :
    IsR1CSCirc (assertion (MulModFold32N.circuitInv Ca Cb hcap) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModFold32NInv input ha hb ht n)

/-! ## `MulModSub2W32M` (multiply-subtract, widened 32-bit `a`, unreduced `b`) -/

def mulModSub2W32MCost : Count := ⟨422, 425⟩

theorem costIs_mulModSub2W32M (input : Var MulModSub2W32M.Inputs (F circomPrime)) :
    CostIs (MulModSub2W32M.main input) mulModSub2W32MCost := by
  obtain ⟨a, b, s1, s2⟩ := input
  rw [show mulModSub2W32MCost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (mulModFold32MInvCost + Count.zero)) from by decide]
  unfold MulModSub2W32M.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32MInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModSub2W32M (b : Var MulModSub2W32M.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSub2W32M.circuit b) mulModSub2W32MCost :=
  CostIs.subcircuit (fun n => costIs_mulModSub2W32M b n)

theorem isR1CS_mulModSub2W32M (input : Var MulModSub2W32M.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (MulModSub2W32M.main input) := by
  obtain ⟨a, b, s1, s2⟩ := input
  unfold MulModSub2W32M.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_mulModFold32MInv _ _ _ _ ha
    (affineW_expand32 _ hb) ?_) fun _ => IsR1CSCirc.pure _
  intro i hi
  rw [Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ (hs1 i hi)) (hs2 i hi)
  exact affineW_provableWitness_bigInt _ nr i hi

theorem isR1CS_sub_mulModSub2W32M (b : Var MulModSub2W32M.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b)
    (hs1 : AffineW b.s1) (hs2 : AffineW b.s2) :
    IsR1CSCirc (subcircuit MulModSub2W32M.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModSub2W32M b ha hb hs1 hs2 n)

/-- The output of a `MulModSub2W32M` subcircuit is the freshly witnessed `r`,
affine. -/
theorem affineW_sub_mulModSub2W32M (b : Var MulModSub2W32M.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSub2W32M.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, MulModSub2W32M.circuit, MulModSub2W32M.elaborated]
  exact affineW_varFromOffset _ _

/-! ## `MulModSub2W32N` (multiply-subtract, plain 32-bit `a`, unreduced `b`) -/

def mulModSub2W32NCost : Count := ⟨420, 423⟩

theorem costIs_mulModSub2W32N (input : Var MulModSub2W32N.Inputs (F circomPrime)) :
    CostIs (MulModSub2W32N.main input) mulModSub2W32NCost := by
  obtain ⟨a, b, s1, s2⟩ := input
  rw [show mulModSub2W32NCost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (mulModFold32NInvCost + Count.zero)) from by decide]
  unfold MulModSub2W32N.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32NInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModSub2W32N (b : Var MulModSub2W32N.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSub2W32N.circuit b) mulModSub2W32NCost :=
  CostIs.subcircuit (fun n => costIs_mulModSub2W32N b n)

theorem isR1CS_mulModSub2W32N (input : Var MulModSub2W32N.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (MulModSub2W32N.main input) := by
  obtain ⟨a, b, s1, s2⟩ := input
  unfold MulModSub2W32N.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_mulModFold32NInv _ _ _ _ ha
    (affineW_expand32N _ hb) ?_) fun _ => IsR1CSCirc.pure _
  intro i hi
  rw [Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ (hs1 i hi)) (hs2 i hi)
  exact affineW_provableWitness_bigInt _ nr i hi

theorem isR1CS_sub_mulModSub2W32N (b : Var MulModSub2W32N.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b)
    (hs1 : AffineW b.s1) (hs2 : AffineW b.s2) :
    IsR1CSCirc (subcircuit MulModSub2W32N.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModSub2W32N b ha hb hs1 hs2 n)

/-- The output of a `MulModSub2W32N` subcircuit is the freshly witnessed `r`,
affine. -/
theorem affineW_sub_mulModSub2W32N (b : Var MulModSub2W32N.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSub2W32N.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, MulModSub2W32N.circuit, MulModSub2W32N.elaborated]
  exact affineW_varFromOffset _ _

/-! ## `MulModSub2D3` (fused multiply-subtract, triply-unreduced multiplicand) -/

def mulModSub2D3Cost : Count := ⟨434, 437⟩

theorem costIs_mulModSub2D3 (input : Var MulModSub2D3.Inputs (F circomPrime)) :
    CostIs (MulModSub2D3.main input) mulModSub2D3Cost := by
  obtain ⟨a, b, s1, s2⟩ := input
  rw [show mulModSub2D3Cost
        = ⟨4, 0⟩ + (⟨260, 265⟩ + (mulModFoldCount + Count.zero)) from by decide]
  unfold MulModSub2D3.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_validP _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModFold _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_mulModSub2D3 (input : Var MulModSub2D3.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b)
    (hs1 : AffineW input.s1) (hs2 : AffineW input.s2) :
    IsR1CSCirc (MulModSub2D3.main input) := by
  obtain ⟨a, b, s1, s2⟩ := input
  unfold MulModSub2D3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_validP _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_sub_mulModFold _ _ _ _ ha hb ?_)
    fun _ => IsR1CSCirc.pure _
  intro i hi
  rw [Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ (hs1 i hi)) (hs2 i hi)
  exact affineW_provableWitness_bigInt _ nr i hi

theorem costIs_sub_mulModSub2D3 (b : Var MulModSub2D3.Inputs (F circomPrime)) :
    CostIs (subcircuit MulModSub2D3.circuit b) mulModSub2D3Cost :=
  CostIs.subcircuit (fun n => costIs_mulModSub2D3 b n)

theorem isR1CS_sub_mulModSub2D3 (b : Var MulModSub2D3.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b)
    (hs1 : AffineW b.s1) (hs2 : AffineW b.s2) :
    IsR1CSCirc (subcircuit MulModSub2D3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModSub2D3 b ha hb hs1 hs2 n)

/-- The output of a `MulModSub2D3` subcircuit is the freshly witnessed `r`,
affine. -/
theorem affineW_sub_mulModSub2D3 (b : Var MulModSub2D3.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit MulModSub2D3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, MulModSub2D3.circuit, MulModSub2D3.elaborated]
  exact affineW_varFromOffset _ _

/-! ## `PhiPairAdd` support (finite chord addition for `P + phi(P)`) -/

def divUncheckedD3Cost : Count := ⟨412, 414⟩

theorem costIs_divUncheckedD3 (input : Var DivUncheckedD3.Inputs (F circomPrime)) :
    CostIs (DivUncheckedD3.main input) divUncheckedD3Cost := by
  obtain ⟨num, den⟩ := input
  rw [show divUncheckedD3Cost
        = ⟨8, 0⟩ + (⟨248, 256⟩ + (mulModFold32NInvCost + Count.zero)) from by decide]
  unfold DivUncheckedD3.main
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams32 _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_mulModFold32NInv _ _ _ _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divUncheckedD3 (input : Var DivUncheckedD3.Inputs (F circomPrime))
    (hnum : AffineW input.num) (hden : AffineW input.den) :
    IsR1CSCirc (DivUncheckedD3.main input) := by
  obtain ⟨num, den⟩ := input
  unfold DivUncheckedD3.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nlam => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams32 _ (affineW_provableWitness_bigInt _ nlam)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_mulModFold32NInv _ _ _ _
    (affineW_varFromOffset _ _)
    (affineW_expand32N _ hden) hnum)
    fun _ => IsR1CSCirc.pure _

theorem costIs_sub_divUncheckedD3 (b : Var DivUncheckedD3.Inputs (F circomPrime)) :
    CostIs (subcircuit DivUncheckedD3.circuit b) divUncheckedD3Cost :=
  CostIs.subcircuit (fun n => costIs_divUncheckedD3 b n)

theorem isR1CS_sub_divUncheckedD3 (b : Var DivUncheckedD3.Inputs (F circomPrime))
    (hnum : AffineW b.num) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivUncheckedD3.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divUncheckedD3 b hnum hden n)

theorem affineW_sub_divUncheckedD3 (b : Var DivUncheckedD3.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivUncheckedD3.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivUncheckedD3.circuit, DivUncheckedD3.elaborated]
  exact affineW_varFromOffset _ _

def phiPairAddCost : Count := ⟨1188, 1196⟩

theorem costIs_phiPairAdd (input : Var PhiPairAdd.Inputs (F circomPrime)) :
    CostIs (PhiPairAdd.main input) phiPairAddCost := by
  obtain ⟨P, Q⟩ := input
  rw [show phiPairAddCost =
      divUncheckedD3Cost + (mulModSub2F32Cost + (mulModSub2W32NCost + Count.zero))
    from by decide]
  unfold PhiPairAdd.main
  refine CostIs.bind (costIs_sub_divUncheckedD3 _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModSub2F32 _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulModSub2W32N _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_phiPairAdd (input : Var PhiPairAdd.Inputs (F circomPrime))
    (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    IsR1CSCirc (PhiPairAdd.main input) := by
  obtain ⟨P, Q⟩ := input
  obtain ⟨hPx, hPy, hPi⟩ := hP
  obtain ⟨hQx, hQy, hQi⟩ := hQ
  unfold PhiPairAdd.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_divUncheckedD3 _
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hQy i hi)
        (Affine.sub (Affine.const _) (hPy i hi)))
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hQx i hi)
        (Affine.sub (Affine.const _) (hPx i hi)))) fun nlam => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2F32 _
    (affineW_sub_divUncheckedD3 _ nlam)
    (affineW_sub_divUncheckedD3 _ nlam) hPx hQx) fun nx3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2W32N _
    (affineW_sub_divUncheckedD3 _ nlam)
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hPx i hi)
        (Affine.sub (Affine.const _) (affineW_sub_mulModSub2F32 _ nx3 i hi)))
    hPy (affineW_emuConst _)) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_phiPairAdd (b : Var PhiPairAdd.Inputs (F circomPrime)) :
    CostIs (subcircuit PhiPairAdd.circuit b) phiPairAddCost :=
  CostIs.subcircuit (fun n => costIs_phiPairAdd b n)

theorem isR1CS_sub_phiPairAdd (b : Var PhiPairAdd.Inputs (F circomPrime))
    (hP : AffineFP b.P) (hQ : AffineFP b.Q) :
    IsR1CSCirc (subcircuit PhiPairAdd.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_phiPairAdd b hP hQ n)

set_option maxRecDepth 4000 in
theorem affineFP_sub_phiPairAdd (b : Var PhiPairAdd.Inputs (F circomPrime)) (n : ℕ)
    (hP : AffineFP b.P) :
    AffineFP ((subcircuit PhiPairAdd.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [circuit_norm, subcircuit, PhiPairAdd.circuit, PhiPairAdd.elaborated]
    exact affineW_mapRange_var _
  · simp only [circuit_norm, subcircuit, PhiPairAdd.circuit, PhiPairAdd.elaborated]
    exact affineW_mapRange_var _
  · simp only [circuit_norm, subcircuit, PhiPairAdd.circuit, PhiPairAdd.elaborated]
    exact hP.2.2

def completeAddCost : Count := ⟨1235, 1244⟩

theorem costIs_completeAdd (input : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (CompleteAdd.main input) completeAddCost := by
  obtain ⟨P, Q⟩ := input
  rw [show completeAddCost
        = ⟨3, 4⟩ + (⟨2, 2⟩ +
            (⟨4, 4⟩ + (divOrZeroS32Cost + (⟨356, 359⟩ +
            (mulModSub2W32NCost +
            (⟨4, 4⟩ + (⟨4, 4⟩ + Count.zero))))))) from by decide]
  unfold CompleteAdd.main
  refine CostIs.bind (costIs_sub_eqFe _) fun sameX => ?_
  refine CostIs.bind (costIs_sub_cancelLow _) fun cancel => ?_
  refine CostIs.bind (costIs_sub_mux _) fun den => ?_
  refine CostIs.bind (costIs_sub_divOrZeroS32 _) fun lam => ?_
  refine CostIs.bind (costIs_sub_mulModSub2F32 _) fun x3 => ?_
  refine CostIs.bind (costIs_sub_mulModSub2W32N _) fun y3 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun outX => ?_
  refine CostIs.bind (costIs_sub_mux _) fun outY => ?_
  exact CostIs.pure _

theorem isR1CS_completeAdd (input : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    IsR1CSCirc (CompleteAdd.main input) := by
  obtain ⟨P, Q⟩ := input
  obtain ⟨hPx, hPy, hPi⟩ := hP
  obtain ⟨hQx, hQy, hQi⟩ := hQ
  unfold CompleteAdd.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_eqFe _ hQx hPx) fun nsx => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_cancelLow _ (affine_sub_eqFe _ nsx) hPy hQy)
    fun ncl => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ (affine_sub_eqFe _ nsx)
    (AffineW.affineProvable (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hPy i hi) (hPy i hi)))
    (AffineW.affineProvable (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hQx i hi)
        (Affine.sub (Affine.const _) (hPx i hi))))) fun nden => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_divOrZeroS32 _
    (affine_sub_eqFe _ nsx)
    hPx
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hQy i hi)
        (Affine.sub (Affine.const _) (hPy i hi)))
    (affineProvable_sub_mux _ nden).affineW) fun nlam => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2F32 _
    (affineW_sub_divOrZeroS32 _ nlam) (affineW_sub_divOrZeroS32 _ nlam) hPx hQx) fun nx3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2W32N _
    (affineW_sub_divOrZeroS32 _ nlam)
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hPx i hi)
        (Affine.sub (Affine.const _) (affineW_sub_mulModSub2F32 _ nx3 i hi))) hPy
    (affineW_emuConst _)) fun ny3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _
    (Affine.add hQi (affine_sub_cancelLow _ ncl))
    (AffineW.affineProvable (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.sub (hPx i hi) (hQx i hi)))
    (AffineW.affineProvable (affineW_sub_mulModSub2F32 _ nx3))) fun noutX => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hQi
    (AffineW.affineProvable hPy)
    (AffineW.affineProvable (affineW_sub_mulModSub2W32N _ ny3))) fun noutY => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (subcircuit CompleteAdd.circuit b) completeAddCost :=
  CostIs.subcircuit (fun n => costIs_completeAdd b n)

theorem isR1CS_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP b.P) (hQ : AffineFP b.Q) :
    IsR1CSCirc (subcircuit CompleteAdd.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_completeAdd b hP hQ n)

set_option maxRecDepth 4000 in
theorem affineFP_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime)) (n : ℕ) :
    AffineFP ((subcircuit CompleteAdd.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, CompleteAdd.circuit, CompleteAdd.elaborated]
  · exact affineW_mapRange_var _
  · exact affineW_mapRange_var _
  · exact Affine.var _


def doubleCost : Count := ⟨1619, 1630⟩

theorem costIs_double (input : Var Double.Inputs (F circomPrime)) :
    CostIs (Double.main input) doubleCost := by
  obtain ⟨P⟩ := input
  rw [show doubleCost
        = ⟨751, 756⟩ + (⟨434, 437⟩ +
            (⟨434, 437⟩ + Count.zero)) from by decide]
  unfold Double.main
  refine CostIs.bind (costIs_sub_divOrZeroW _) fun div => ?_
  refine CostIs.bind (costIs_sub_mulModSub2 _) fun x3 => ?_
  refine CostIs.bind (costIs_sub_mulModSub2D3 _) fun y3 => ?_
  exact CostIs.pure _

theorem isR1CS_double (input : Var Double.Inputs (F circomPrime))
    (hP : AffineFP input.P) :
    IsR1CSCirc (Double.main input) := by
  obtain ⟨P⟩ := input
  obtain ⟨hPx, hPy, -⟩ := hP
  unfold Double.main
  have htDenAff : AffineW (Vector.ofFn fun k : Fin numLimbs =>
      P.y[k.val]'k.isLt + P.y[k.val]'k.isLt) := by
    intro i hi
    rw [Vector.getElem_ofFn]
    exact Affine.add (hPy i hi) (hPy i hi)
  refine IsR1CSCirc.bind_out (isR1CS_sub_divOrZeroW _ hPx htDenAff) fun ndiv => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2 _
    (affineW_sub_divOrZeroW
      { num := P.x, den := Vector.ofFn fun k : Fin numLimbs =>
          P.y[k.val]'k.isLt + P.y[k.val]'k.isLt } ndiv)
    (affineW_sub_divOrZeroW
      { num := P.x, den := Vector.ofFn fun k : Fin numLimbs =>
          P.y[k.val]'k.isLt + P.y[k.val]'k.isLt } ndiv) hPx hPx) fun nx3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModSub2D3 _
    (affineW_sub_divOrZeroW
      { num := P.x, den := Vector.ofFn fun k : Fin numLimbs =>
          P.y[k.val]'k.isLt + P.y[k.val]'k.isLt } ndiv)
    (fun i hi => by
      rw [Vector.getElem_ofFn]
      exact Affine.add (hPx i hi)
        (Affine.sub (Affine.const _) (affineW_sub_mulModSub2 _ nx3 i hi))) hPy
    (affineW_emuConst _)) fun ny3 => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_double (b : Var Double.Inputs (F circomPrime)) :
    CostIs (subcircuit Double.circuit b) doubleCost :=
  CostIs.subcircuit (fun n => costIs_double b n)

theorem isR1CS_sub_double (b : Var Double.Inputs (F circomPrime))
    (hP : AffineFP b.P) :
    IsR1CSCirc (subcircuit Double.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_double b hP n)

set_option maxRecDepth 4000 in
theorem affineFP_sub_double (b : Var Double.Inputs (F circomPrime))
    (hisInf : Affine b.P.isInf) (n : ℕ) :
    AffineFP ((subcircuit Double.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, Double.circuit, Double.elaborated]
  · exact affineW_mapRange_var _
  · exact affineW_mapRange_var _
  · exact hisInf


theorem affineW_ofFn_var {m : ℕ} (f : Fin m → ℕ) :
    AffineW (Vector.ofFn (fun i => Expression.var ⟨f i⟩) : Var (fields m) (F circomPrime)) := by
  intro j hj
  rw [Vector.getElem_ofFn]
  exact Affine.var _


open Challenge.Instances.Secp256k1ScalarMul in
theorem affineInput_components (input : Var Interface.Input (F circomPrime))
    (hinput : AffineProvable input) :
    AffineW input.bits ∧ AffineW input.px ∧ AffineW input.py := by
  have hflat : AffineW
      (input.bits ++ (input.px ++ (input.py ++ (#v[] : Vector (Expression (F circomPrime)) 0))) :
        fields (Interface.scalarBits + (Interface.coordBytes + (Interface.coordBytes + 0)))
          (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hinput i (by exact hi)
  exact ⟨AffineW.left_of_append hflat,
    AffineW.left_of_append (AffineW.right_of_append hflat),
    AffineW.left_of_append (AffineW.right_of_append (AffineW.right_of_append hflat))⟩

open Challenge.Instances.Secp256k1ScalarMul in
theorem affineProvable_interfaceOutput {v : Var Interface.Output (F circomPrime)}
    (hx : AffineW v.x) (hy : AffineW v.y) (hi : Affine v.isInf) :
    AffineProvable v := by
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

end Cost
end Solution.Secp256k1ScalarMul
