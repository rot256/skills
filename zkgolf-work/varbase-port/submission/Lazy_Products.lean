import Solution.Secp256k1ScalarMul.Lazy_Interval

/-!
# The nine sparse products of one chain step

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
  sx : fields 8 F    -- x²
  pxt : fields 8 F   -- x T.x
  st : fields 8 F    -- T.x²
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
  let sx ← subcircuit Sparse32Square.circuit i.x
  let pxt ← subcircuit Sparse32Mul.circuit ⟨i.x, embedExpr i.tx⟩
  let st ← subcircuit Sparse32Square.circuit (embedExpr i.tx)
  let sa ← subcircuit Sparse32Square.circuit i.a
  let pab ← subcircuit Sparse32Mul.circuit ⟨vaddE i.a i.b, vsubE i.x (xSExpr i sa)⟩
  let sb ← subcircuit Sparse32Square.circuit i.b
  let pb ← subcircuit Sparse32Mul.circuit ⟨i.b, vsubE i.x (xPExpr i sa sb)⟩
  return { pa, pu, sx, pxt, st, sa, pab, sb, pb }

instance elaborated : ElaboratedCircuit Field Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs Field) : Prop := True

def Spec (i : Inputs Field) (o : Outputs Field) : Prop :=
  o.pa = mulVec i.a (vsub (embedVec i.tx) i.x) ∧
  o.pu = mulVec i.a (vadd i.y (embedVec i.ty)) ∧
  o.sx = sqVec i.x ∧
  o.pxt = mulVec i.x (embedVec i.tx) ∧
  o.st = sqVec (embedVec i.tx) ∧
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
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h_holds
  simp only [xSExpr, xPExpr, map_vsubE, map_vaddE, map_embedExpr] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp only [Spec, xSVal, xPVal, circuit_norm]
  exact ⟨(mulSpec _ _ _).mp h1, (mulSpec _ _ _).mp h2, (sqSpec _ _).mp h3, (mulSpec _ _ _).mp h4,
    (sqSpec _ _).mp h5, (sqSpec _ _).mp h6, (mulSpec _ _ _).mp h7, (sqSpec _ _).mp h8,
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

def cost : Count := ⟨96, 96⟩

theorem costIs_main (i : Var Inputs Field) : CostIs (main i) cost := by
  rw [show cost = ⟨12, 12⟩ + (⟨12, 12⟩ + (⟨9, 9⟩ + (⟨12, 12⟩ + (⟨9, 9⟩ + (⟨9, 9⟩ +
    (⟨12, 12⟩ + (⟨9, 9⟩ + (⟨12, 12⟩ + Count.zero)))))))) by decide]
  unfold main
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Square.costIs_call _) fun _ => ?_
  refine CostIs.bind (Sparse32Mul.costIs_call _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_call (i : Var Inputs Field) : CostIs (subcircuit circuit i) cost :=
  CostIs.subcircuit (fun n => costIs_main i n)

end Solution.Secp256k1ScalarMulFixedBase.LazyVar.Products
