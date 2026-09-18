import Solution.Secp256k1ScalarMul.Lazy_Interval

/-!
# The seven sparse products of one chain step

All products use patchgravity's 12-product CRT multiply and 9-product square
(d59c8bf7).  Their outputs are free affine recombinations of the product
cells, so every downstream quantity (`xS`, `x'`, the certificate contents,
`y'`) is affine and costs nothing further.
-/

namespace Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products

open SmallSquare Sparse32 SparseX Challenge.CostR1CS Cost

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

structure Inputs (F : Type) where
  a : fields 8 F
  b : fields 8 F
  x : fields 8 F
  y : fields 8 F
  tx : Emu F
  ty : Emu F
deriving ProvableStruct

structure Outputs (F : Type) where
  pa : fields 8 F    -- a (T.x − x)
  pu : fields 8 F    -- a (y + T.y)
  qxt : fields 8 F   -- x² + x T.x + T.x², fused in the native field
  sa : fields 8 F    -- a²
  pab : fields 8 F   -- (a + b)(x − xS)
  sb : fields 8 F    -- b²
  pb : fields 8 F    -- b (x − x')
deriving ProvableStruct

/-! ### Vector helpers (values and expressions) -/

def vsub (u v : fields 8 Field) : fields 8 Field := Vector.ofFn fun k => u[k.val] - v[k.val]
def vadd (u v : fields 8 Field) : fields 8 Field := Vector.ofFn fun k => u[k.val] + v[k.val]
def vsubE (u v : Var (fields 8) Field) : Var (fields 8) Field :=
  Vector.ofFn fun k => u[k.val] - v[k.val]
def vaddE (u v : Var (fields 8) Field) : Var (fields 8) Field :=
  Vector.ofFn fun k => u[k.val] + v[k.val]

def mulVec (u v : fields 8 Field) : fields 8 Field :=
  Vector.ofFn fun k => sparseMul (fun i => u[i.val]) (fun i => v[i.val]) k
def sqVec (u : fields 8 Field) : fields 8 Field :=
  Vector.ofFn fun k => sparseSquare (fun i => u[i.val]) k

lemma eval_vsubE (env : Environment Field) (u v : Var (fields 8) Field) :
    eval env (vsubE u v) = vsub (eval env u) (eval env v) := by
  apply Vector.ext
  intro k hk
  simp only [vsubE, vsub, circuit_norm, Vector.getElem_ofFn, Vector.getElem_map,
    Expression.eval, neg_one_mul, sub_eq_add_neg]

lemma eval_vaddE (env : Environment Field) (u v : Var (fields 8) Field) :
    eval env (vaddE u v) = vadd (eval env u) (eval env v) := by
  apply Vector.ext
  intro k hk
  simp only [vaddE, vadd, circuit_norm, Vector.getElem_ofFn, Vector.getElem_map,
    Expression.eval]

lemma map_vsubE (env : Environment Field) (u v : Var (fields 8) Field) :
    Vector.map (Expression.eval env) (vsubE u v) =
      vsub (Vector.map (Expression.eval env) u) (Vector.map (Expression.eval env) v) := by
  simpa only [circuit_norm] using eval_vsubE env u v

lemma map_vaddE (env : Environment Field) (u v : Var (fields 8) Field) :
    Vector.map (Expression.eval env) (vaddE u v) =
      vadd (Vector.map (Expression.eval env) u) (Vector.map (Expression.eval env) v) := by
  simpa only [circuit_norm] using eval_vaddE env u v

lemma map_embedExpr (env : Environment Field) (x : Var Emu Field) :
    Vector.map (Expression.eval env) (embedExpr x) = embedVec (Vector.map (Expression.eval env) x) := by
  simpa only [circuit_norm] using eval_embedExpr env x

lemma affine_vsubE (u v : Var (fields 8) Field) (hu : AffineW u) (hv : AffineW v) :
    AffineW (vsubE u v) := by
  intro k hk
  rw [vsubE, Vector.getElem_ofFn]
  exact Affine.sub (hu k hk) (hv k hk)

lemma affine_vaddE (u v : Var (fields 8) Field) (hu : AffineW u) (hv : AffineW v) :
    AffineW (vaddE u v) := by
  intro k hk
  rw [vaddE, Vector.getElem_ofFn]
  exact Affine.add (hu k hk) (hv k hk)

/-! ### Native quadratic fusion

`x² + x·T.x + T.x²` factors over the native field as `(x − ω T.x)(x − ω² T.x)`
for a primitive cube root of unity `ω` (an idea from GPT-6 Astra's submission
914a9c15).  One CRT multiply of two free affine blends replaces a square, a
multiply and a square.  The fusion is exact in the coefficient vector, so all
integer envelopes downstream are unchanged. -/

def omegaNative : Field := 4407920970296243842393367215006156084916469457145843978461

theorem omega_root : omegaNative ^ 2 + omegaNative + 1 = 0 := by decide

def blend (c : Field) (x t : fields 8 Field) : fields 8 Field :=
  Vector.ofFn fun k => x[k.val] - c * t[k.val]

def blendE (c : Field) (x t : Var (fields 8) Field) : Var (fields 8) Field :=
  Vector.ofFn fun k => x[k.val] - (Expression.const c) * t[k.val]

lemma map_blendE (env : Environment Field) (c : Field) (x t : Var (fields 8) Field) :
    Vector.map (Expression.eval env) (blendE c x t) =
      blend c (Vector.map (Expression.eval env) x) (Vector.map (Expression.eval env) t) := by
  apply Vector.ext
  intro k hk
  simp only [blendE, blend, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval,
    neg_one_mul, sub_eq_add_neg]

lemma affine_blendE (c : Field) (x t : Var (fields 8) Field)
    (hx : AffineW x) (ht : AffineW t) : AffineW (blendE c x t) := by
  intro k hk
  rw [blendE, Vector.getElem_ofFn]
  exact Affine.sub (hx k hk) (Affine.fconst_mul c (ht k hk))

private lemma sparse_comm (x t : Words Field) (k : Fin 8) :
    sparseMul t x k = sparseMul x t k := by
  unfold sparseMul
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hr : redCoeff j i k = redCoeff i j k := by simp only [redCoeff, Nat.add_comm]
  rw [hr, mul_comm (t j) (x i)]

private lemma sparse_expand (x t : Words Field) (c d : Field) (k : Fin 8) :
    sparseMul (fun i => x i - c * t i) (fun i => x i - d * t i) k =
      sparseMul x x k - d * sparseMul x t k - c * sparseMul t x k +
      (c * d) * sparseMul t t k := by
  unfold sparseMul
  simp_rw [show ∀ i j : Fin 8,
    (redCoeff i j k : Field) * ((x i - c * t i) * (x j - d * t j)) =
      (redCoeff i j k : Field) * (x i * x j) -
      d * ((redCoeff i j k : Field) * (x i * t j)) -
      c * ((redCoeff i j k : Field) * (t i * x j)) +
      (c * d) * ((redCoeff i j k : Field) * (t i * t j)) by intros; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem fusedQuadratic_identity (x t : fields 8 Field) :
    mulVec (blend omegaNative x t) (blend (omegaNative ^ 2) x t) =
      vadd (vadd (sqVec x) (mulVec x t)) (sqVec t) := by
  have hc : omegaNative * omegaNative ^ 2 = 1 := by
    linear_combination (omegaNative - 1) * omega_root
  apply Vector.ext
  intro k hk
  simp only [mulVec, sqVec, vadd, blend, Vector.getElem_ofFn, sparseSquare]
  rw [sparse_expand, sparse_comm (fun i => x[i.val]) (fun i => t[i.val]), hc]
  linear_combination -(sparseMul (fun i => x[i.val]) (fun i => t[i.val]) ⟨k, hk⟩) * omega_root

/-! ### Circuit -/

def xSExpr (i : Var Inputs Field) (sa : Var (fields 8) Field) : Var (fields 8) Field :=
  vsubE (vsubE sa i.x) (embedExpr i.tx)
def xPExpr (i : Var Inputs Field) (sa sb : Var (fields 8) Field) : Var (fields 8) Field :=
  vaddE (vsubE sb sa) (embedExpr i.tx)

def xSVal (i : Inputs Field) (sa : fields 8 Field) : fields 8 Field :=
  vsub (vsub sa i.x) (embedVec i.tx)
def xPVal (i : Inputs Field) (sa sb : fields 8 Field) : fields 8 Field :=
  vadd (vsub sb sa) (embedVec i.tx)

def main (i : Var Inputs Field) : Circuit Field (Var Outputs Field) := do
  let pa ← subcircuit Sparse32Mul.circuit ⟨i.a, vsubE (embedExpr i.tx) i.x⟩
  let pu ← subcircuit Sparse32Mul.circuit ⟨i.a, vaddE i.y (embedExpr i.ty)⟩
  let qxt ← subcircuit Sparse32Mul.circuit
    ⟨blendE omegaNative i.x (embedExpr i.tx), blendE (omegaNative ^ 2) i.x (embedExpr i.tx)⟩
  let sa ← subcircuit Sparse32Square.circuit i.a
  let pab ← subcircuit Sparse32Mul.circuit ⟨vaddE i.a i.b, vsubE i.x (xSExpr i sa)⟩
  let sb ← subcircuit Sparse32Square.circuit i.b
  let pb ← subcircuit Sparse32Mul.circuit ⟨i.b, vsubE i.x (xPExpr i sa sb)⟩
  return { pa, pu, qxt, sa, pab, sb, pb }

instance elaborated : ElaboratedCircuit Field Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (i : Inputs Field) (o : Outputs Field) : Prop :=
  o.pa = mulVec i.a (vsub (embedVec i.tx) i.x) ∧
  o.pu = mulVec i.a (vadd i.y (embedVec i.ty)) ∧
  o.qxt = vadd (vadd (sqVec i.x) (mulVec i.x (embedVec i.tx))) (sqVec (embedVec i.tx)) ∧
  o.sa = sqVec i.a ∧
  o.pab = mulVec (vadd i.a i.b) (vsub i.x (xSVal i o.sa)) ∧
  o.sb = sqVec i.b ∧
  o.pb = mulVec i.b (vsub i.x (xPVal i o.sa o.sb))

lemma mulSpec (u v : fields 8 Field) (z : fields 8 Field) :
    Sparse32Mul.Spec ⟨u, v⟩ z ↔ z = mulVec u v := Iff.rfl

lemma sqSpec (u : fields 8 Field) (z : fields 8 Field) :
    Sparse32Square.Spec u z ↔ z = sqVec u := Iff.rfl

attribute [local irreducible] Sparse32Mul.outputExpr Sparse32Square.outputExpr

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start_core
  subst h_input
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.Assumptions,
    Sparse32Square.circuit, Sparse32Square.Assumptions, circuit_norm] at h_holds ⊢
  obtain ⟨h1, h2, h3, h6, h7, h8, h9⟩ := h_holds
  simp only [xSExpr, xPExpr, map_vsubE, map_vaddE, map_blendE, map_embedExpr] at h1 h2 h3 h6 h7 h8 h9
  simp only [Spec, xSVal, xPVal, circuit_norm]
  exact ⟨(mulSpec _ _ _).mp h1, (mulSpec _ _ _).mp h2,
    ((mulSpec _ _ _).mp h3).trans (fusedQuadratic_identity _ _),
    (sqSpec _ _).mp h6, (mulSpec _ _ _).mp h7, (sqSpec _ _).mp h8,
    (mulSpec _ _ _).mp h9⟩

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start_core
  simp only [main, Sparse32Mul.circuit, Sparse32Mul.Assumptions,
    Sparse32Square.circuit, Sparse32Square.Assumptions, circuit_norm]

def circuit : FormalCircuit Field Inputs Outputs where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

def cost : Count := ⟨78, 78⟩

theorem costIs_main (i : Var Inputs Field) : CostIs (main i) cost := by
  rw [show cost = ⟨12, 12⟩ + (⟨12, 12⟩ + (⟨12, 12⟩ + (⟨9, 9⟩ +
    (⟨12, 12⟩ + (⟨9, 9⟩ + (⟨12, 12⟩ + Count.zero)))))) by decide]
  unfold main
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (i : Var Inputs Field) : CostIs (subcircuit circuit i) cost :=
  CostIs.subcircuit (fun n => costIs_main i n)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
