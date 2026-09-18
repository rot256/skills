import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.GroupedEqXV
import Challenge.Specs.Secp256k1
import Challenge.Instances.Secp256k1ScalarMul.Interface



namespace Solution.Secp256k1ScalarMul


@[reducible] def circomPrime : ℕ :=
  Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime

instance : Fact (circomPrime > 2) := ⟨by decide⟩


@[reducible] def P256 : ℕ := Specs.Secp256k1.p


@[reducible] def numLimbs : ℕ := 4


@[reducible] def limbBits : ℕ := 64


@[reducible] def bytesPerLimb : ℕ := 8


@[reducible] def coordBytes : ℕ := 32


@[reducible] def Emu : TypeMap := BigInt numLimbs


def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide


def secpParams3 : BigIntParams circomPrime 3 where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide


def eqNParamsAdd : EqViaCarriesN.NParams circomPrime where
  B := limbBits
  W := 3
  C := 2 ^ 65 + 2
  OFF := 3
  hB := by decide
  hW := by decide
  hB1 := by decide
  hC1 := by decide
  hOW := by decide
  hCO := by decide
  hWp := by decide


def eqNParams3Add : EqViaCarriesN.NParams circomPrime where
  B := limbBits
  W := 4
  C := 2 ^ 66
  OFF := 5
  hB := by decide
  hW := by decide
  hB1 := by decide
  hC1 := by decide
  hOW := by decide
  hCO := by decide
  hWp := by decide




def gfMul (k : ℕ) : ℕ := if k = 0 then 1 else if k ≤ 2 then 2 else 1


def posOfMul (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 3 else k + 2


def nfMul (_ : ℕ) : ℕ := 5 * 2 ^ 128


def offMul (k : ℕ) : ℕ :=
  if k = 0 then 92233720368547758079 else 92233720368547758085

def wfMul (_ : ℕ) : ℕ := 68

def vMul : GroupedEqV.VParams where
  Nf := nfMul
  OFFf := offMul
  Wf := wfMul
  Nmax := 0
  OFFmax := 0
  Wmax := 68

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem hgvMul :
    GroupedEqXV.GVXHyps circomPrime 7 64 gfMul posOfMul 5 vMul vMul := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by norm_num, by decide, by decide, by decide⟩
  · intro k; simp only [posOfMul, gfMul]; split_ifs <;> omega
  · intro k; simp only [gfMul]; split_ifs <;> omega
  · intro k
    simp only [vMul, wfMul]
    exact ⟨by norm_num, by decide⟩
  · intro j
    simp only [vMul, nfMul]
    exact ⟨by norm_num, by norm_num⟩
  · intro k hk
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ⟨by decide, by decide⟩, by decide⟩


theorem hNfMul : ∀ j, vMul.Nf j = (numLimbs + 1) * 2 ^ (2 * secpParams.B) :=
  fun _ => rfl




def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits


def emuOfNat (v : ℕ) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs => ((limbOfNat v k.val : ℕ) : F circomPrime)


def emuConst (v : ℕ) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (((limbOfNat v k.val : ℕ) : F circomPrime) : Expression (F circomPrime))


def pConst : Var Emu (F circomPrime) := emuConst P256


def zeroConst : Var Emu (F circomPrime) := emuConst 0


def oneConst : Var Emu (F circomPrime) := emuConst 1


def threePLimbs : Vector (F circomPrime) 7 :=
  Vector.ofFn fun k : Fin 7 => ((limbOfNat (3 * P256) k.val : ℕ) : F circomPrime)


def twoPBorrowDigit (k : ℕ) : ℕ :=
  if k = 0 then 2 ^ 65 - 2 ^ 33 - 1954 else 2 ^ 65 - 2




def evalEmu (env : ProverEnvironment (F circomPrime))
    (x : Var Emu (F circomPrime)) : ℕ :=
  Limbs.fromLimbs limbBits
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

theorem evalEmu_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    evalEmu env x = evalEmu env' x := by
  have hmap :
      x.map (Expression.eval env.toEnvironment) =
        x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i : (eval env x)[i] = (eval env' x)[i] := by
      simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
    rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
    exact h_i
  simp [evalEmu, hmap]

theorem emu_map_eval_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have h_i : (eval env x)[i] = (eval env' x)[i] := by
    simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
  rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
  exact h_i

theorem eval_mem_of_map_eval_eq {m : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    {x : Vector (Expression (F circomPrime)) m}
    (h : x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment)) :
    ∀ a ∈ x, Expression.eval env.toEnvironment a = Expression.eval env'.toEnvironment a := by
  intro a ha
  simp only [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  simpa only [Vector.getElem_map] using congrArg (fun y : Vector (F circomPrime) m => y[i]) h





def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp :=
  ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)


def Fe.Valid (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits ∧ x.value limbBits < P256




structure FlaggedPoint (F : Type) where
  x : Emu F
  y : Emu F
  isInf : F
deriving ProvableStruct


def decodePoint (P : FlaggedPoint (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if P.isInf = 1 then .infinity
  else .affine { x := decodeFe P.x, y := decodeFe P.y }


def FlaggedPoint.Valid (P : FlaggedPoint (F circomPrime)) : Prop :=
  IsBool P.isInf ∧ Fe.Valid P.x ∧ Fe.Valid P.y ∧
    (P.isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
        { x := decodeFe P.x, y := decodeFe P.y })


def infConst : Var FlaggedPoint (F circomPrime) :=
  { x := zeroConst, y := zeroConst,
    isInf := ((1 : F circomPrime) : Expression (F circomPrime)) }

end Solution.Secp256k1ScalarMul
