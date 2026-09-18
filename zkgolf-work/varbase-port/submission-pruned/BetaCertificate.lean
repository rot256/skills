import Solution.Secp256k1ScalarMul.Bridge
import Mathlib.Data.Nat.BinaryRec

namespace CheckFastPow

set_option maxRecDepth 100000

def modPow (a m : ℕ) : ℕ → ℕ :=
  Nat.binaryRec' (1 % m) fun b _ _ r =>
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

open Specs.Secp256k1

def betaNat : ℕ :=
  0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

theorem beta_character_ne_one : ((-7 : Fp) ^ ((p - 1) / 3)) ≠ 1 := by
  rw [show ((-7 : Fp) ^ ((p - 1) / 3)) = (betaNat : Fp) from by
    have hbase : (((p - 7 : ℕ) : Fp)) = -7 := by
      rw [Nat.cast_sub (by norm_num [p]), show (p : Fp) = 0 by simp]
      exact zero_sub _
    rw [← hbase, ← cast_modPow]
    congr 1]
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by norm_num [betaNat, p])] at this
  have hone : ZMod.val (1 : Fp) = 1 := by simp [ZMod.val_one_eq_one_mod, p]
  rw [hone] at this
  norm_num [betaNat] at this

end CheckFastPow
