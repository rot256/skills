import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic
import Challenge.Specs.Secp256k1

namespace CheckLucas

set_option maxRecDepth 100000

def modPow (a m : ℕ) : ℕ → ℕ :=
  Nat.binaryRec' (1 % m) fun b _ _ r ↦
    if b then (r * r * a) % m else (r * r) % m

theorem cast_modPow (a m n : ℕ) :
    ((modPow a m n : ℕ) : ZMod m) = (a : ZMod m) ^ n := by
  induction n using Nat.binaryRec' with
  | zero => simp [modPow]
  | bit b n h ih =>
      rw [modPow, Nat.binaryRec'_eq b n h]
      cases b
      · simp only [Bool.false_eq_true, if_false, ZMod.natCast_mod, Nat.cast_mul]
        change ((modPow a m n : ℕ) : ZMod m) * ((modPow a m n : ℕ) : ZMod m) = _
        rw [ih]
        rw [Nat.bit_val]
        simp only [Bool.toNat_false, Nat.add_zero]
        rw [show 2 * n = n + n by omega, pow_add]
      · rw [if_pos rfl]
        simp only [ZMod.natCast_mod, Nat.cast_mul]
        change ((modPow a m n : ℕ) : ZMod m) * ((modPow a m n : ℕ) : ZMod m) *
          (a : ZMod m) = _
        rw [ih]
        rw [Nat.bit_val]
        simp only [Bool.toNat_true]
        rw [show 2 * n + 1 = n + n + 1 by omega, pow_add, pow_add, pow_one]

theorem modPow_lt (a n : ℕ) {m : ℕ} (hm : 0 < m) : modPow a m n < m := by
  induction n using Nat.binaryRec' with
  | zero => simpa [modPow] using Nat.mod_lt 1 hm
  | bit b n h ih =>
      rw [modPow, Nat.binaryRec'_eq b n h]
      split <;> exact Nat.mod_lt _ hm

theorem pow_eq_one_of_modPow_eq_one {a p e : ℕ}
    (h : modPow a p e = 1) : (a : ZMod p) ^ e = 1 := by
  rw [← cast_modPow, h]
  norm_num

theorem pow_ne_one_of_modPow_ne_one {a p e : ℕ} (hp : 1 < p)
    (h : modPow a p e ≠ 1) : (a : ZMod p) ^ e ≠ 1 := by
  intro he
  have hc : ((modPow a p e : ℕ) : ZMod p) = 1 := cast_modPow a p e |>.trans he
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (modPow_lt a e (by omega))] at hv
  have hone : ZMod.val (1 : ZMod p) = 1 := by
    simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp]
  rw [hone] at hv
  exact h hv

private theorem lucasNode (p a : ℕ) (L : List ℕ)
    (hp : 1 < p)
    (hfac : p - 1 = L.prod)
    (hL : ∀ q ∈ L, q.Prime)
    (ha : modPow a p (p - 1) = 1)
    (hne : ∀ q ∈ L, modPow a p ((p - 1) / q) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · exact pow_eq_one_of_modPow_eq_one ha
  · intro q hq hqd
    have hqd' : q ∣ L.prod := by rwa [← hfac]
    have hmem : q ∈ L :=
      mem_list_primes_of_dvd_prod hq.prime (fun r hr ↦ (hL r hr).prime) hqd'
    exact pow_ne_one_of_modPow_ne_one hp (hne q hmem)

theorem prime_4681609 : Nat.Prime 4681609 := by
  apply lucasNode 4681609 23 [2, 2, 2, 3, 97, 2011]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_44706919 : Nat.Prime 44706919 := by
  apply lucasNode 44706919 6 [2, 3, 797, 9349]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_545358713 : Nat.Prime 545358713 := by
  apply lucasNode 545358713 5 [2, 2, 2, 41, 59, 28181]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_297159362677 : Nat.Prime 297159362677 := by
  apply lucasNode 297159362677 2 [2, 2, 3, 3, 11, 461, 1627771]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_107361793816595537 : Nat.Prime 107361793816595537 := by
  apply lucasNode 107361793816595537 3 [2, 2, 2, 2, 16699, 85831, 4681609]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { exact prime_4681609 }
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 := by
  apply lucasNode 174723607534414371449 3
    [2, 2, 2, 17, 59, 4051, 120233, 44706919]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { exact prime_44706919 }
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_29047611873442575647497758179 :
    Nat.Prime 29047611873442575647497758179 := by
  apply lucasNode 29047611873442575647497758179 2
    [2, 293, 305873, 545358713, 297159362677]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals try { exact prime_545358713 }
    all_goals try { exact prime_297159362677 }
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem prime_341948486974166000522343609283189 :
    Nat.Prime 341948486974166000522343609283189 := by
  apply lucasNode 341948486974166000522343609283189 2
    [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try { exact prime_29047611873442575647497758179 }
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

open Specs.Secp256k1

theorem order_prime : Nat.Prime order := by
  rw [show order =
      115792089237316195423570985008687907852837564279074904382605163141518161494337 by
    norm_num [order]]
  apply lucasNode
    115792089237316195423570985008687907852837564279074904382605163141518161494337
    7
    [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537,
      174723607534414371449, 341948486974166000522343609283189]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals try { exact prime_107361793816595537 }
    all_goals try { exact prime_174723607534414371449 }
    all_goals try { exact prime_341948486974166000522343609283189 }
    all_goals norm_num
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals decide

end CheckLucas
