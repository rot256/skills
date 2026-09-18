import Solution.Secp256k1ScalarMul.ToBytes
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems
import Solution.Secp256k1ScalarMul.CompleteAddTheorems
import Solution.Secp256k1ScalarMul.AddMod

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

end OutputBoundary

end ScalarMul
end Solution.Secp256k1ScalarMul
