import Solution.Secp256k1ScalarMul.Bridge
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

namespace Solution.Secp256k1ScalarMul.JacobianCert

open Specs.ShortWeierstrass Specs.Secp256k1
open WeierstrassCurve
open scoped WeierstrassCurve.Jacobian

abbrev J := Bridge.W.toJacobian
abbrev Raw := Fin 3 → Fp

def zeroRaw : Raw := ![1, 1, 0]

def betaNat : ℕ :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

def gRaw : Raw := ![G.x, G.y, 1]
def hRaw : Raw := ![(betaNat : Fp) * G.x, -G.y, 1]

def H : Point Fp := { x := (betaNat : Fp) * G.x, y := -G.y }
def PhiG : Point Fp := { x := (betaNat : Fp) * G.x, y := G.y }

set_option maxRecDepth 100000 in
lemma G_onCurve : OnCurve curve G := by
  rw [onCurve_iff]
  decide

set_option maxRecDepth 100000 in
lemma H_onCurve : OnCurve curve H := by
  rw [onCurve_iff]
  decide

set_option maxRecDepth 100000 in
lemma PhiG_onCurve : OnCurve curve PhiG := by
  rw [onCurve_iff]
  decide

lemma g_nonsingular : J.Nonsingular gRaw := by
  change J.Nonsingular ![G.x, G.y, 1]
  rw [Jacobian.nonsingular_some]
  exact (Bridge.W.equation_iff_nonsingular_of_Δ_ne_zero Bridge.W_Δ_ne_zero).mp
    (Bridge.equation_of_onCurve G_onCurve)

lemma h_nonsingular : J.Nonsingular hRaw := by
  change J.Nonsingular ![H.x, H.y, 1]
  rw [Jacobian.nonsingular_some]
  exact (Bridge.W.equation_iff_nonsingular_of_Δ_ne_zero Bridge.W_Δ_ne_zero).mp
    (Bridge.equation_of_onCurve H_onCurve)

def a : ℕ := 0x3086d221a7d46bcde86c90e49284eb15
def bAbs : ℕ := 0xe4437ed6010e88286f547fa90abfe4c3

def rawDistinct (P Q : Raw) : Prop :=
  P 0 * Q 2 ^ 2 ≠ Q 0 * P 2 ^ 2 ∨
  P 1 * Q 2 ^ 3 ≠ Q 1 * P 2 ^ 3

def rawDistinctB (P Q : Raw) : Bool :=
  decide (P 0 * Q 2 ^ 2 ≠ Q 0 * P 2 ^ 2) ||
  decide (P 1 * Q 2 ^ 3 ≠ Q 1 * P 2 ^ 3)

lemma not_equiv_of_rawDistinct {P Q : Raw} (h : rawDistinct P Q) : ¬ P ≈ Q := by
  rcases h with hx | hy
  · exact Jacobian.not_equiv_of_X_ne hx
  · exact Jacobian.not_equiv_of_Y_ne hy

def dblRaw (P : Raw) : Raw :=
  let U := -(3 * P 0 ^ 2)
  let D := 2 * P 1
  let X₃ := U ^ 2 - 2 * P 0 * D ^ 2
  let negY₃ := -U * (X₃ - P 0 * D ^ 2) + P 1 * D ^ 3
  ![X₃, -negY₃, P 2 * D]

def addRaw (P Q : Raw) : Raw :=
  let X₁ := P 0
  let Y₁ := P 1
  let Z₁ := P 2
  let X₂ := Q 0
  let Y₂ := Q 1
  let Z₂ := Q 2
  let X₃ := X₁ * X₂ ^ 2 * Z₁ ^ 2 - 2 * Y₁ * Y₂ * Z₁ * Z₂
    + X₁ ^ 2 * X₂ * Z₂ ^ 2 + 14 * Z₁ ^ 4 * Z₂ ^ 4
  let negY₃ := -Y₁ * X₂ ^ 3 * Z₁ ^ 3 + 2 * Y₁ * Y₂ ^ 2 * Z₁ ^ 3
    - 3 * X₁ ^ 2 * X₂ * Y₂ * Z₁ ^ 2 * Z₂
    + 3 * X₁ * Y₁ * X₂ ^ 2 * Z₁ * Z₂ ^ 2 + X₁ ^ 3 * Y₂ * Z₂ ^ 3
    - 2 * Y₁ ^ 2 * Y₂ * Z₂ ^ 3 - 14 * Y₂ * Z₁ ^ 6 * Z₂ ^ 3
    + 14 * Y₁ * Z₁ ^ 3 * Z₂ ^ 6
  let Z₃ := X₁ * Z₂ ^ 2 - X₂ * Z₁ ^ 2
  ![X₃, -negY₃, Z₃]

lemma dblRaw_eq (P : Raw) : dblRaw P = J.dblXYZ P := by
  funext i
  fin_cases i <;>
    simp [dblRaw, J, Bridge.W, Jacobian.dblXYZ, Jacobian.dblX,
      Jacobian.dblY, Jacobian.negDblY, Jacobian.dblZ, Jacobian.dblU_eq,
      Jacobian.negY]
  all_goals ring_nf
  all_goals simp

lemma addRaw_eq (P Q : Raw) : addRaw P Q = J.addXYZ P Q := by
  funext i
  fin_cases i <;>
    simp [addRaw, J, Bridge.W, Jacobian.addXYZ, Jacobian.addX,
      Jacobian.addY, Jacobian.negAddY, Jacobian.addZ, Jacobian.negY]
  all_goals ring_nf
  all_goals simp

noncomputable def affine (P : Raw) : Bridge.W.Point :=
  Jacobian.Point.toAffine J P

lemma affine_gRaw_eq : affine gRaw = Bridge.mkPoint G G_onCurve := by
  change Jacobian.Point.toAffine J ![G.x, G.y, 1] = Bridge.mkPoint G G_onCurve
  rw [Jacobian.Point.toAffine_some g_nonsingular]
  rfl

lemma affine_hRaw_eq : affine hRaw = Bridge.mkPoint H H_onCurve := by
  change Jacobian.Point.toAffine J ![H.x, H.y, 1] = Bridge.mkPoint H H_onCurve
  have hn : J.Nonsingular ![H.x, H.y, 1] := by
    simpa [H, hRaw] using h_nonsingular
  rw [Jacobian.Point.toAffine_some hn]
  rfl

lemma mkPoint_H_eq_neg_PhiG :
    Bridge.mkPoint H H_onCurve = -Bridge.mkPoint PhiG PhiG_onCurve := by
  change WeierstrassCurve.Affine.Point.some _ =
    -WeierstrassCurve.Affine.Point.some _
  rw [WeierstrassCurve.Affine.Point.neg_some]

lemma dblRaw_valid {P : Raw} (hP : J.Nonsingular P) :
    J.Nonsingular (dblRaw P) ∧ affine (dblRaw P) = affine P + affine P := by
  rw [dblRaw_eq, ← Jacobian.add_self P]
  exact ⟨Jacobian.nonsingular_add hP hP, Jacobian.Point.toAffine_add hP hP⟩

lemma addRaw_valid {P Q : Raw} (hP : J.Nonsingular P) (hQ : J.Nonsingular Q)
    (hd : rawDistinct P Q) :
    J.Nonsingular (addRaw P Q) ∧ affine (addRaw P Q) = affine P + affine Q := by
  have hne : ¬ P ≈ Q := not_equiv_of_rawDistinct hd
  rw [addRaw_eq, ← Jacobian.add_of_not_equiv hne]
  exact ⟨Jacobian.nonsingular_add hP hQ, Jacobian.Point.toAffine_add hP hQ⟩

def addBit (P Q : Raw) (bit : Bool) : Raw :=
  if bit then addRaw P Q else P

def step (i : ℕ) (P : Raw) : Raw :=
  let D := dblRaw P
  let A := addBit D gRaw (a.testBit (127 - i))
  addBit A hRaw (bAbs.testBit (127 - i))

def trace : ℕ → Raw
  | 0 => zeroRaw
  | i + 1 => step i (trace i)

def run (P : Raw) (i : ℕ) : ℕ → Raw
  | 0 => P
  | n + 1 => run (step i P) (i + 1) n

def stepSafe (i : ℕ) (P : Raw) : Prop :=
  let D := dblRaw P
  let A := addBit D gRaw (a.testBit (127 - i))
  (a.testBit (127 - i) = true → rawDistinct D gRaw) ∧
  (bAbs.testBit (127 - i) = true → rawDistinct A hRaw)

def stepSafeB (i : ℕ) (P : Raw) : Bool :=
  let D := dblRaw P
  let A := addBit D gRaw (a.testBit (127 - i))
  (!a.testBit (127 - i) || rawDistinctB D gRaw) &&
  (!bAbs.testBit (127 - i) || rawDistinctB A hRaw)

lemma stepSafe_of_bool {i : ℕ} {P : Raw} (h : stepSafeB i P = true) :
    stepSafe i P := by
  cases ha : a.testBit (127 - i) <;>
    cases hb : bAbs.testBit (127 - i) <;>
    simp [stepSafeB, stepSafe, ha, hb, rawDistinctB, rawDistinct] at h ⊢ <;>
    assumption

lemma addBit_valid {P Q : Raw} (bit : Bool) (hP : J.Nonsingular P)
    (hQ : J.Nonsingular Q) (hsafe : bit = true → rawDistinct P Q) :
    J.Nonsingular (addBit P Q bit) ∧
      affine (addBit P Q bit) = affine P + if bit then affine Q else 0 := by
  cases bit with
  | false => simp [addBit, hP]
  | true => simpa [addBit] using addRaw_valid hP hQ (hsafe rfl)

noncomputable def groupStep (i : ℕ) (P : Bridge.W.Point) : Bridge.W.Point :=
  (P + P + if a.testBit (127 - i) then affine gRaw else 0) +
    if bAbs.testBit (127 - i) then affine hRaw else 0

lemma step_valid {i : ℕ} {P : Raw} (hP : J.Nonsingular P)
    (hsafe : stepSafeB i P = true) :
    J.Nonsingular (step i P) ∧ affine (step i P) = groupStep i (affine P) := by
  obtain ⟨hsafeG, hsafeH⟩ := stepSafe_of_bool hsafe
  obtain ⟨hD, eD⟩ := dblRaw_valid hP
  obtain ⟨hA, eA⟩ := addBit_valid (a.testBit (127 - i)) hD g_nonsingular hsafeG
  obtain ⟨hB, eB⟩ := addBit_valid (bAbs.testBit (127 - i)) hA h_nonsingular hsafeH
  refine ⟨hB, ?_⟩
  change affine (addBit (addBit (dblRaw P) gRaw (a.testBit (127 - i))) hRaw
      (bAbs.testBit (127 - i))) =
    (affine P + affine P + (if a.testBit (127 - i) then affine gRaw else 0)) +
      (if bAbs.testBit (127 - i) then affine hRaw else 0)
  rw [eB, eA, eD]

def runSafeB (P : Raw) (i : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => stepSafeB i P && runSafeB (step i P) (i + 1) n

noncomputable def groupRun (P : Bridge.W.Point) (i : ℕ) : ℕ → Bridge.W.Point
  | 0 => P
  | n + 1 => groupRun (groupStep i P) (i + 1) n

lemma run_valid {P : Raw} {i n : ℕ} (hP : J.Nonsingular P)
    (hsafe : runSafeB P i n = true) :
    J.Nonsingular (run P i n) ∧ affine (run P i n) = groupRun (affine P) i n := by
  induction n generalizing P i with
  | zero =>
      refine ⟨hP, ?_⟩
      rfl
  | succ n ih =>
      have hs : stepSafeB i P = true ∧ runSafeB (step i P) (i + 1) n = true := by
        simpa [runSafeB, Bool.and_eq_true] using hsafe
      obtain ⟨hnext, enext⟩ := step_valid hP hs.1
      obtain ⟨hout, eout⟩ := ih hnext hs.2
      refine ⟨hout, ?_⟩
      simpa [run, groupRun, enext] using eout

def coeffStep (i : ℕ) (c : ℕ × ℕ) : ℕ × ℕ :=
  (2 * c.1 + if a.testBit (127 - i) then 1 else 0,
   2 * c.2 + if bAbs.testBit (127 - i) then 1 else 0)

def runCoeff (c : ℕ × ℕ) (i : ℕ) : ℕ → ℕ × ℕ
  | 0 => c
  | n + 1 => runCoeff (coeffStep i c) (i + 1) n

lemma groupStep_coeff (i : ℕ) (c : ℕ × ℕ) :
    groupStep i (c.1 • affine gRaw + c.2 • affine hRaw) =
      (coeffStep i c).1 • affine gRaw + (coeffStep i c).2 • affine hRaw := by
  cases ha : a.testBit (127 - i) <;>
    cases hb : bAbs.testBit (127 - i) <;>
    simp [groupStep, coeffStep, ha, hb, add_nsmul, mul_nsmul,
      two_nsmul, nsmul_add] <;> abel

lemma groupRun_coeff (c : ℕ × ℕ) (i n : ℕ) :
    groupRun (c.1 • affine gRaw + c.2 • affine hRaw) i n =
      (runCoeff c i n).1 • affine gRaw + (runCoeff c i n).2 • affine hRaw := by
  induction n generalizing c i with
  | zero => rfl
  | succ n ih =>
      rw [groupRun, groupStep_coeff]
      exact ih (coeffStep i c) (i + 1)

def blockCoeff : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | j + 1 => runCoeff (blockCoeff j) (8 * j) 8

lemma block_advance (j : ℕ) {P Q : Raw} (hP : J.Nonsingular P)
    (hsem : affine P = (blockCoeff j).1 • affine gRaw + (blockCoeff j).2 • affine hRaw)
    (hsafe : runSafeB P (8 * j) 8 = true) (hvalue : run P (8 * j) 8 = Q) :
    J.Nonsingular Q ∧
      affine Q = (blockCoeff (j + 1)).1 • affine gRaw +
        (blockCoeff (j + 1)).2 • affine hRaw := by
  obtain ⟨hQ, eQ⟩ := run_valid hP hsafe
  rw [hvalue] at hQ eQ
  rw [hsem, groupRun_coeff] at eQ
  exact ⟨hQ, eQ⟩

-- The concrete trace certificate is split into short chunks below to keep
-- kernel reduction shallow.

def s0 : Raw := zeroRaw
def s1 : Raw :=
  ![0x7be08c72c0329d2529830d291c59ffe7f974ae99197c2385d4acaaecb4034d88,
    0x60e70d69f927851a3a346de589ab9defabbba210e512e286e29a12b163398e73,
    0x3b45bc6fc92dbdd571e975b4fefbc72f5cc1cbdbf99381d1ca77446b01da42b0]

def s2 : Raw :=
  ![0xe84d3f367a695fd4aa75b5b608b4dccb860d3e98ca4f910b783a45f03a715693,
    0xf82701e453451bbab4664e23b279dfd79fcfe69a4f3f78d0f1fc6f785ef49181,
    0xb634270b3f3f957505c75ab5ed264b7c9e05415ca9e5460935d6c168175fe36d]

def s3 : Raw :=
  ![0xf71a673453f51c22a863109e59a85a15f526d938286f72b65e7ff67bf7758aaa,
    0x38fb40cb5d264410f59102cb7f81d7d9953f65bed81359829f937f0c8b7194f0,
    0x7ceb721c81a0e1077f3b1086a82c54a98edd352ff540039f011dd31a96fd971b]

def s4 : Raw :=
  ![0x2d5174296d035adf21fc4a763e0166c1cf0ab028d8282e41de1e8c1e4d0fceee,
    0xa4654142ad2538a49dcdd7a73b00e3abf689d92170f4593b3eafa6986149f301,
    0xe31bb21954feeab805e60950fafb78b0ebe3909f8bfeaa4b861e6ccf7f3ef04a]

def s5 : Raw :=
  ![0x648699d02a39742bb61e7ac8ef5346421c7b347024a6e9a4f2b43f75fe2c0f5f,
    0xe720dc45fee0562a1c0954a9d073e44626fb03225c284a544e005cfcc6540b92,
    0x2eb2619165551bf45233b383365708e17869c2b7aa838b64b75384b126ce877d]

def s6 : Raw :=
  ![0x161102f7df2efae190f3265439e5c3f6ff0fa03bb8e92f6d3957ea754078ad5e,
    0x56e612a6e0bbce6424134e63093cfdcdf4d3de812bf90e594d48a7039c3d2629,
    0x606da67d7faa4d39ce3f2732a3c9889480282d4f4992e915cdd23eb3b5d845b4]

def s7 : Raw :=
  ![0x4ba4f7e18afacb604cea994305f484ec7233bd2d2f02347cab3adabfff06b0f8,
    0xbe3ab0bcf82635258951552219ec0cc02f3cd24e9b6fc7b00cddac61c2e7da34,
    0xcf165a6234a99c5ab51cd43f2edf7f6d6783bb8398b6009612cb7683e9e1cc9f]

def s8 : Raw :=
  ![0x33beeec3685d33d0b33221fae5d67484629f0a817d60fac3595ac7b58147a69f,
    0xd664e881580942674375e87d576a4ced6edf26de4663c20509a1268c263ef2ab,
    0x417ec3cb97a2b8cd02df5aaa33c191b4db7f72283a091b7115b72db16b15ec5e]

def s9 : Raw :=
  ![0x8bd1e1390cc9c980498a4d981befabce3d458219171e7eee9b6c59f93868b716,
    0xabc499164c792c5a78c6a038a7f584ad07ea63e5e3d248c8b7ed85c10c927124,
    0x94053359c58f54b60bfef14a128f5c6e4567190656fa867b62f3b40344388163]

def s10 : Raw :=
  ![0x370d146119389aacd176da0d1093be96d28aa2e1bc5a38729cd1b47f47fc3c0c,
    0x6b0608298385813ff386e8fbb7a4beff876f8bd13a5818470930fc017eefe6aa,
    0xcbcc3f02a321d9454f0f6bc80ad2f975eee8a4aefa966e4c435374e7311190a1]

def s11 : Raw :=
  ![0xa8902aa64869a863c5f06d92fe9a1ab25fd467cbe99c3bafa92b7e1b9763e7c9,
    0xb9e571be4ecc088ab0365e6f895fd07fb2de81a6c5321787f2ac8da97295d24c,
    0x9798ce5787cfd076ecfe4ff60e10846b64a93edb2718fdbd52114587c3c0b841]

def s12 : Raw :=
  ![0x55cbbe3e531323dc1df2099e47d022b663da1275398d8d868988b8551fc73ad3,
    0xa1bf9919a931e2e833830acec587ea1a8cdbaff6fd64651a8df7eef00dd2c808,
    0x6e90059e3bc677b461ca0379b198a84ff574ea61eaaa9b567799b3a17467bde3]

def s13 : Raw :=
  ![0x684541362b854fc8ae1868cfa2a0012723cffaf69c84421844af1d85055d3dee,
    0x2b334371eac470ac2e59ddd2461d88ab0807ce0c12053aa52ffd6820b0d9816a,
    0xe4033c2511796f04cbd63ff8923c5fa374cdaf17bd6885fbc8ce8053320884e9]

def s14 : Raw :=
  ![0xd3827c87c01da6fc76f51e73eb8b04f2b814d987af2ac9932cacb219b535e5fb,
    0xa62a4ae6c3d7dd06ba112e380e5c3b35ad0346a2a6065826a0841f2655e6e3fd,
    0x38d26f41ccec9f33aa7d4673d65ab4b932732786000c7996426edd0f47bc0371]

def s15 : Raw :=
  ![0xcb164bfef24793d9d3162c2f822e8b30886acd67870ebcd35047189e96e02f0a,
    0xf13ab5de3bf5b99198bab7781eb713f07e91c65128e7fbf81e2e13b979f6fabc,
    0xeca109022f32136c2859d2fcc4f8be64df3ac4d4e9089efd307460afa67d9981]

def s16 : Raw :=
  ![0xb1e62418828916f8b0e6907f894a10f61697e949e7fc3c76f98fecea4cb7e112,
    0x6581801e132f7fa18903514461ea358092b8510ea3eec13d328732fb15048789,
    0]

set_option maxRecDepth 100000 in
lemma chunk0_safe : runSafeB s0 0 8 = true := by decide

set_option maxRecDepth 100000 in
lemma chunk0_value : run s0 0 8 = s1 := by
  funext j
  fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk1_safe : runSafeB s1 8 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk1_value : run s1 8 8 = s2 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk2_safe : runSafeB s2 16 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk2_value : run s2 16 8 = s3 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk3_safe : runSafeB s3 24 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk3_value : run s3 24 8 = s4 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk4_safe : runSafeB s4 32 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk4_value : run s4 32 8 = s5 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk5_safe : runSafeB s5 40 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk5_value : run s5 40 8 = s6 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk6_safe : runSafeB s6 48 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk6_value : run s6 48 8 = s7 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk7_safe : runSafeB s7 56 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk7_value : run s7 56 8 = s8 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk8_safe : runSafeB s8 64 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk8_value : run s8 64 8 = s9 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk9_safe : runSafeB s9 72 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk9_value : run s9 72 8 = s10 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk10_safe : runSafeB s10 80 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk10_value : run s10 80 8 = s11 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk11_safe : runSafeB s11 88 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk11_value : run s11 88 8 = s12 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk12_safe : runSafeB s12 96 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk12_value : run s12 96 8 = s13 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk13_safe : runSafeB s13 104 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk13_value : run s13 104 8 = s14 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk14_safe : runSafeB s14 112 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk14_value : run s14 112 8 = s15 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma chunk15_safe : runSafeB s15 120 8 = true := by decide
set_option maxRecDepth 100000 in
lemma chunk15_value : run s15 120 8 = s16 := by funext j; fin_cases j <;> decide

set_option maxRecDepth 100000 in
lemma blockCoeff_final : blockCoeff 16 = (a, bAbs) := by decide

theorem short_glv_relation :
    a • affine gRaw + bAbs • affine hRaw = 0 := by
  have h0 : J.Nonsingular s0 := by
    simpa [s0, zeroRaw] using (Jacobian.nonsingular_zero (W' := J))
  have e0 : affine s0 =
      (blockCoeff 0).1 • affine gRaw + (blockCoeff 0).2 • affine hRaw := by
    change Jacobian.Point.toAffine J ![1, 1, 0] = 0 • affine gRaw + 0 • affine hRaw
    simp [Jacobian.Point.toAffine_zero]
  obtain ⟨h1, e1⟩ := block_advance 0 h0 e0 chunk0_safe chunk0_value
  obtain ⟨h2, e2⟩ := block_advance 1 h1 e1 chunk1_safe chunk1_value
  obtain ⟨h3, e3⟩ := block_advance 2 h2 e2 chunk2_safe chunk2_value
  obtain ⟨h4, e4⟩ := block_advance 3 h3 e3 chunk3_safe chunk3_value
  obtain ⟨h5, e5⟩ := block_advance 4 h4 e4 chunk4_safe chunk4_value
  obtain ⟨h6, e6⟩ := block_advance 5 h5 e5 chunk5_safe chunk5_value
  obtain ⟨h7, e7⟩ := block_advance 6 h6 e6 chunk6_safe chunk6_value
  obtain ⟨h8, e8⟩ := block_advance 7 h7 e7 chunk7_safe chunk7_value
  obtain ⟨h9, e9⟩ := block_advance 8 h8 e8 chunk8_safe chunk8_value
  obtain ⟨h10, e10⟩ := block_advance 9 h9 e9 chunk9_safe chunk9_value
  obtain ⟨h11, e11⟩ := block_advance 10 h10 e10 chunk10_safe chunk10_value
  obtain ⟨h12, e12⟩ := block_advance 11 h11 e11 chunk11_safe chunk11_value
  obtain ⟨h13, e13⟩ := block_advance 12 h12 e12 chunk12_safe chunk12_value
  obtain ⟨h14, e14⟩ := block_advance 13 h13 e13 chunk13_safe chunk13_value
  obtain ⟨h15, e15⟩ := block_advance 14 h14 e14 chunk14_safe chunk14_value
  obtain ⟨_h16, e16⟩ := block_advance 15 h15 e15 chunk15_safe chunk15_value
  rw [blockCoeff_final] at e16
  calc
    a • affine gRaw + bAbs • affine hRaw = affine s16 := e16.symm
    _ = 0 := by
      apply Jacobian.Point.toAffine_of_Z_eq_zero
      rfl

theorem short_glv_relation_mkPoint :
    a • Bridge.mkPoint G G_onCurve +
      bAbs • (-Bridge.mkPoint PhiG PhiG_onCurve) = 0 := by
  simpa only [affine_gRaw_eq, affine_hRaw_eq, mkPoint_H_eq_neg_PhiG] using
    short_glv_relation

theorem a_smul_G_eq_b_smul_PhiG :
    a • Bridge.mkPoint G G_onCurve = bAbs • Bridge.mkPoint PhiG PhiG_onCurve := by
  have h := short_glv_relation_mkPoint
  have hb : bAbs • (-Bridge.mkPoint PhiG PhiG_onCurve) +
      bAbs • Bridge.mkPoint PhiG PhiG_onCurve = 0 := by
    rw [← nsmul_add, neg_add_cancel, nsmul_zero]
  calc
    a • Bridge.mkPoint G G_onCurve = a • Bridge.mkPoint G G_onCurve + 0 := by simp
    _ = a • Bridge.mkPoint G G_onCurve +
        (bAbs • (-Bridge.mkPoint PhiG PhiG_onCurve) +
          bAbs • Bridge.mkPoint PhiG PhiG_onCurve) := by rw [hb]
    _ = (a • Bridge.mkPoint G G_onCurve +
        bAbs • (-Bridge.mkPoint PhiG PhiG_onCurve)) +
          bAbs • Bridge.mkPoint PhiG PhiG_onCurve := by rw [add_assoc]
    _ = bAbs • Bridge.mkPoint PhiG PhiG_onCurve := by rw [h, zero_add]

end Solution.Secp256k1ScalarMul.JacobianCert
