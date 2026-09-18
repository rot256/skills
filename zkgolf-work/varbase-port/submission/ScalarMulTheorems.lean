import Solution.Secp256k1ScalarMul.ToBytes
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZero



namespace Solution.Secp256k1ScalarMul
namespace ScalarMul




structure Outputs (F : Type) where
  x : Vector F coordBytes
  y : Vector F coordBytes
  isInf : F
deriving ProvableStruct


def coordVal (v : Vector (F circomPrime) coordBytes) : ℕ :=
  Limbs.fromLimbs 8 ((v.toList.map ZMod.val).reverse)


def Outputs.Valid (out : Outputs (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out.x[i]).val < 256) ∧
  (∀ i : Fin coordBytes, (out.y[i]).val < 256) ∧
  IsBool out.isInf ∧
  coordVal out.x < P256 ∧ coordVal out.y < P256 ∧
  (out.isInf = 1 →
    (∀ i : Fin coordBytes, out.x[i] = 0) ∧ (∀ i : Fin coordBytes, out.y[i] = 0))


def decodeOutput (out : Outputs (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if out.isInf = 1 then .infinity
  else .affine
    { x := ((coordVal out.x : ℕ) : Specs.Secp256k1.Fp),
      y := ((coordVal out.y : ℕ) : Specs.Secp256k1.Fp) }



lemma toBytes_localLength (x : Var Emu (F circomPrime)) :
    ToBytes.circuit.localLength x = 256 := rfl

lemma toBytes_output (x : Var Emu (F circomPrime)) (n : ℕ) :
    ToBytes.circuit.output x n = varFromOffset (fields coordBytes) n := rfl

lemma mux_localLength (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) :
    (Mux.circuit (M := fields coordBytes)).localLength inp = 32 := rfl

lemma mux_output (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) (n : ℕ) :
    (Mux.circuit (M := fields coordBytes)).output inp n
      = varFromOffset (fields coordBytes) n := rfl


lemma toBytes_channels : ToBytes.circuit.channelsWithRequirements = [] := rfl

lemma mux_channels :
    (Mux.circuit (M := fields coordBytes)).channelsWithRequirements = [] := rfl




def accVar (i₀ : ℕ) : ℕ → Var FlaggedPoint (F circomPrime)
  | 0 => infConst
  | k + 1 => varFromOffset FlaggedPoint (i₀ + k * 4563 + 4554)


def specAcc (bits : Vector ℕ Specs.Secp256k1.scalarBits)
    (P : Specs.ShortWeierstrass.Point Specs.Secp256k1.Fp) :
    ℕ → Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp
  | 0 => .infinity
  | k + 1 =>
    if h : k < Specs.Secp256k1.scalarBits then
      Specs.ShortWeierstrass.step Specs.Secp256k1.curve P (specAcc bits P k) (bits[k]'h)
    else specAcc bits P k



lemma evalInf_valid (env : Environment (F circomPrime)) :
    FlaggedPoint.Valid
      { x := Vector.map (Expression.eval env) infConst.x,
        y := Vector.map (Expression.eval env) infConst.y,
        isInf := Expression.eval env infConst.isInf } := by
  have hx : Vector.map (Expression.eval env) infConst.x = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have hy : Vector.map (Expression.eval env) infConst.y = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have h1 : Expression.eval env infConst.isInf = 1 := rfl
  rw [hx, hy, h1]
  exact ⟨Or.inr rfl, DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos,
    DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos,
    fun h => absurd h one_ne_zero⟩


lemma decode_evalInf (env : Environment (F circomPrime)) :
    decodePoint
      { x := Vector.map (Expression.eval env) infConst.x,
        y := Vector.map (Expression.eval env) infConst.y,
        isInf := Expression.eval env infConst.isInf } = .infinity := by
  rw [decodePoint]
  exact if_pos rfl




lemma map_eval_ofFn_rev (env : Environment (F circomPrime)) (M : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun i : Fin coordBytes =>
        (var { index := M + (31 - i.val) } : Expression (F circomPrime))) =
    Vector.ofFn (fun i : Fin coordBytes =>
      (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) M))[31 - i.val]'(by
          simp only [coordBytes]; omega)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_ofFn,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange]


lemma fromLimbs_rev_ofFn (w : Vector (F circomPrime) coordBytes) :
    Limbs.fromLimbs 8
      (((Vector.ofFn fun i : Fin coordBytes =>
          w[31 - i.val]'(by simp only [coordBytes]; omega)).toList.map
        ZMod.val).reverse) =
      Limbs.fromLimbs 8 (w.toList.map ZMod.val) := by
  refine congrArg (Limbs.fromLimbs 8) ?_
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_reverse, List.getElem_map, Vector.toList_ofFn,
      List.getElem_ofFn, Vector.getElem_toList]
    simp only [List.length_map, List.length_ofFn, List.length_reverse,
      Vector.length_toList, coordBytes] at h1 h2 ⊢
    simp only [show (31 : ℕ) - (32 - 1 - j) = j from by omega]
    rfl


lemma fromLimbs_replicate_zero (B n : ℕ) :
    Limbs.fromLimbs B (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Limbs.fromLimbs, List.foldr_cons,
      show List.foldr (fun limb acc => limb + acc * 2 ^ B) 0 (List.replicate n 0)
        = Limbs.fromLimbs B (List.replicate n 0) from rfl, ih]
    simp

lemma fromLimbs_eq_zero_entry {B : ℕ} {l : List ℕ}
    (h : Limbs.fromLimbs B l = 0) (i : ℕ) (hi : i < l.length) : l[i] = 0 := by
  rw [fromLimbs_eq_sum] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (f := fun j : Fin l.length => l[j] * 2 ^ (B * j.val))
    (fun _ _ => Nat.zero_le _)).mp h ⟨i, hi⟩ (Finset.mem_univ _)
  exact (Nat.mul_eq_zero.mp hz).resolve_right (by positivity)

lemma fromLimbs_vector_eq_zero_entry {B n : ℕ} {v : Vector (F circomPrime) n}
    (h : Limbs.fromLimbs B (v.toList.map ZMod.val) = 0) (i : Fin n) : v[i] = 0 := by
  have he := fromLimbs_eq_zero_entry h i.val (by simp)
  apply ZMod.val_injective circomPrime
  simpa [List.getElem_map, Vector.getElem_toList] using he


lemma eval_zeroBytes_getElem (env : Environment (F circomPrime))
    (v : Var (fields coordBytes) (F circomPrime))
    (h : v = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime)))
    (j : ℕ) (hj : j < coordBytes) :
    (Vector.map (Expression.eval env) v)[j]'hj = 0 := by
  subst h
  simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]


lemma fromLimbs_eval_zeroBytes (env : Environment (F circomPrime))
    (v : Var (fields coordBytes) (F circomPrime))
    (h : v = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime))) :
    Limbs.fromLimbs 8
      ((Vector.map (Expression.eval env) v).toList.map ZMod.val) = 0 := by
  subst h
  rw [show (Vector.map (Expression.eval env)
        (Vector.ofFn fun _ =>
          ((0 : F circomPrime) : Expression (F circomPrime)))).toList.map ZMod.val
      = List.replicate coordBytes 0 by
    apply List.ext_getElem <;> simp [Expression.eval]]
  exact fromLimbs_replicate_zero 8 coordBytes




section OutputBoundary

variable (i₀ : ℕ) (env : Environment (F circomPrime))

set_option maxRecDepth 8192 in

lemma output_valid
    (zb : Var (fields coordBytes) (F circomPrime))
    (hzb : zb = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime)))
    (hbool : IsBool (Expression.eval env (accVar i₀ 256).isInf))
    (hfx : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 256).x))
    (hfy : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 256).y))
    (hxb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936)))[i] < 256)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 2343936))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).x))
    (hyb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936 + 288)))[i] < 256)
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 2343936 + 288))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936 + 288 + 288)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936)))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936 + 288 + 288 + 32)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 2343936 + 288))) :
    Outputs.Valid
      { x := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 2343936 + 288 + 288 + (31 - i.val) } :
              Expression (F circomPrime))),
        y := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 2343936 + 288 + 288 + 32 + (31 - i.val) } :
              Expression (F circomPrime))),
        isInf := Expression.eval env (accVar i₀ 256).isInf } := by
  rw [map_eval_ofFn_rev env (i₀ + 2343936 + 288 + 288),
    map_eval_ofFn_rev env (i₀ + 2343936 + 288 + 288 + 32), hmx, hmy]
  simp only [Outputs.Valid]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0, if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    refine ⟨?_, ?_, Or.inl rfl, ?_, ?_,
      fun h => absurd h (zero_ne_one (α := F circomPrime))⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hxb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hyb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · simp only [coordVal, fromLimbs_rev_ofFn, hxb_val]
      exact hfx.2
    · simp only [coordVal, fromLimbs_rev_ofFn, hyb_val]
      exact hfy.2
  · rw [hinf1, if_pos rfl, if_pos rfl]
    refine ⟨?_, ?_, Or.inr rfl, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
      simp
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
      simp
    · simp only [coordVal, fromLimbs_rev_ofFn, fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P256_pos
    · simp only [coordVal, fromLimbs_rev_ofFn, fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P256_pos
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
end OutputBoundary

end ScalarMul
end Solution.Secp256k1ScalarMul
