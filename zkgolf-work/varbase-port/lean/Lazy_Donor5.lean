import Solution.Secp256k1ScalarMul.Lazy_Donor4


-- Adapted donor module: OrderFactsCerts
section DonorFile5_0


namespace Solution.Secp256k1ScalarMulFixedBase.OrderFactsCerts

set_option maxRecDepth 100000

def powMod (a m : Nat) : Nat → Nat → Nat
  | 0, _ => 1 % m
  | fuel + 1, e =>
    if e = 0 then 1 % m
    else
      let h := powMod a m fuel (e / 2)
      let sq := h * h % m
      if e % 2 = 1 then sq * (a % m) % m else sq

theorem powMod_correct (a m : Nat) :
    ∀ fuel e, e < 2 ^ fuel → powMod a m fuel e = a ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
      intro e he
      have : e = 0 := by simpa using he
      subst this; rfl
  | succ f ih =>
      intro e he
      rw [powMod]
      by_cases h0 : e = 0
      · subst h0; simp
      · rw [if_neg h0]
        have hlt : e / 2 < 2 ^ f := by
          have : e < 2 ^ (f + 1) := he
          omega
        have hih := ih (e / 2) hlt
        simp only [hih]
        have hsq : (a ^ (e / 2) % m) * (a ^ (e / 2) % m) % m = a ^ (2 * (e / 2)) % m := by
          rw [← Nat.mul_mod, ← pow_add, two_mul]
        by_cases hpar : e % 2 = 1
        · rw [if_pos hpar, hsq, ← Nat.mul_mod, ← pow_succ]; congr 2; omega
        · rw [if_neg hpar, hsq]; congr 2; omega

private lemma pow_eq_one_of_mod {P w e : Nat} (h : w ^ e % P = 1) :
    ((w : Nat) : ZMod P) ^ e = 1 := by
  have h1 : ((w ^ e % P : Nat) : ZMod P) = ((w : Nat) : ZMod P) ^ e := by
    rw [ZMod.natCast_mod]; push_cast; ring
  rw [h, Nat.cast_one] at h1
  exact h1.symm

private lemma pow_ne_one' {P w e : Nat} (hP1 : 1 < P) (h : w ^ e % P ≠ 1) :
    ((w : Nat) : ZMod P) ^ e ≠ 1 := by
  haveI : Fact (1 < P) := ⟨hP1⟩
  intro hcon
  apply h
  have h1 : ((w ^ e % P : Nat) : ZMod P) = ((w : Nat) : ZMod P) ^ e := by
    rw [ZMod.natCast_mod]; push_cast; ring
  rw [hcon] at h1
  have hlt : w ^ e % P < P := Nat.mod_lt _ (by omega)
  have hv := congrArg ZMod.val h1
  rwa [ZMod.val_cast_of_lt hlt, ZMod.val_one] at hv

theorem prime_s : Nat.Prime 0x4530140875 := by
  refine lucas_primality _ ((2 : Nat) : ZMod 0x4530140875) ?_ ?_
  · rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 2 0x4530140875 256 0x4530140874 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0x4530140875 : Nat) - 1 = 2 ^ 2 * (3 ^ 2 * (11 * (461 * (1627771)))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num, show (0x4530140874 : Nat) / 2 = 0x22980a043a by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x4530140875 256 0x22980a043a (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num, show (0x4530140874 : Nat) / 3 = 0x171006ad7c by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x4530140875 256 0x171006ad7c (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11)).mp h
      subst hqe
      rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num, show (0x4530140874 : Nat) / 11 = 0x64a305ddc by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x4530140875 256 0x64a305ddc (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 461 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 461)).mp h
      subst hqe
      rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num, show (0x4530140874 : Nat) / 461 = 0x266bc644 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x4530140875 256 0x266bc644 (by decide)]; decide)
    have hqe : q = 1627771 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1627771)).mp hdvd
    subst hqe
    rw [show (0x4530140875 : Nat) - 1 = 0x4530140874 by norm_num, show (0x4530140874 : Nat) / 1627771 = 0x2c91c by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x4530140875 256 0x2c91c (by decide)]; decide)

theorem prime_r : Nat.Prime 0x5ddb9f12ef6348a3e23ba5e3 := by
  refine lucas_primality _ ((2 : Nat) : ZMod 0x5ddb9f12ef6348a3e23ba5e3) ?_ ?_
  · rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x5ddb9f12ef6348a3e23ba5e2 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 2 * (293 * (305873 * (545358713 * (297159362677)))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp h
      subst hqe
      rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num, show (0x5ddb9f12ef6348a3e23ba5e2 : Nat) / 2 = 0x2eedcf8977b1a451f11dd2f1 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x2eedcf8977b1a451f11dd2f1 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 293 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 293)).mp h
      subst hqe
      rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num, show (0x5ddb9f12ef6348a3e23ba5e2 : Nat) / 293 = 0x52016aa89240078c913dba by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x52016aa89240078c913dba (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 305873 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 305873)).mp h
      subst hqe
      rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num, show (0x5ddb9f12ef6348a3e23ba5e2 : Nat) / 305873 = 0x141c21786981517cdc42 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x141c21786981517cdc42 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 545358713 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 545358713)).mp h
      subst hqe
      rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num, show (0x5ddb9f12ef6348a3e23ba5e2 : Nat) / 545358713 = 0x2e32d4d0c6a576a72 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x2e32d4d0c6a576a72 (by decide)]; decide)
    have hqe : q = 297159362677 := (Nat.prime_dvd_prime_iff_eq hq prime_s).mp hdvd
    subst hqe
    rw [show (0x5ddb9f12ef6348a3e23ba5e3 : Nat) - 1 = 0x5ddb9f12ef6348a3e23ba5e2 by norm_num, show (0x5ddb9f12ef6348a3e23ba5e2 : Nat) / 297159362677 = 0x15b47fa125e621a by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x5ddb9f12ef6348a3e23ba5e3 256 0x15b47fa125e621a (by decide)]; decide)

theorem prime_q1 : Nat.Prime 0x17d6cfb8ee30c51 := by
  refine lucas_primality _ ((3 : Nat) : ZMod 0x17d6cfb8ee30c51) ?_ ?_
  · rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 0x17d6cfb8ee30c50 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 3 0x17d6cfb8ee30c51 256 0x17d6cfb8ee30c50 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 2 ^ 4 * (16699 * (85831 * (4681609))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 0x17d6cfb8ee30c50 by norm_num, show (0x17d6cfb8ee30c50 : Nat) / 2 = 0xbeb67dc7718628 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x17d6cfb8ee30c51 256 0xbeb67dc7718628 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 16699 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 16699)).mp h
      subst hqe
      rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 0x17d6cfb8ee30c50 by norm_num, show (0x17d6cfb8ee30c50 : Nat) / 16699 = 0x5d8ec435ff0 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x17d6cfb8ee30c51 256 0x5d8ec435ff0 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 85831 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 85831)).mp h
      subst hqe
      rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 0x17d6cfb8ee30c50 by norm_num, show (0x17d6cfb8ee30c50 : Nat) / 85831 = 0x1233c87d930 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x17d6cfb8ee30c51 256 0x1233c87d930 (by decide)]; decide)
    have hqe : q = 4681609 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4681609)).mp hdvd
    subst hqe
    rw [show (0x17d6cfb8ee30c51 : Nat) - 1 = 0x17d6cfb8ee30c50 by norm_num, show (0x17d6cfb8ee30c50 : Nat) / 4681609 = 0x556e4c5d0 by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x17d6cfb8ee30c51 256 0x556e4c5d0 (by decide)]; decide)

theorem prime_q2 : Nat.Prime 0x978c6f353c3889a79 := by
  refine lucas_primality _ ((3 : Nat) : ZMod 0x978c6f353c3889a79) ?_ ?_
  · rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x978c6f353c3889a78 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0x978c6f353c3889a79 : Nat) - 1 = 2 ^ 3 * (17 * (59 * (4051 * (120233 * (44706919))))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 2 = 0x4bc6379a9e1c44d3c by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x4bc6379a9e1c44d3c (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17)).mp h
      subst hqe
      rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 17 = 0x8ea24a8c74e9eaf8 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x8ea24a8c74e9eaf8 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 59)).mp h
      subst hqe
      rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 59 = 0x2919112421afdfe8 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x2919112421afdfe8 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 4051 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4051)).mp h
      subst hqe
      rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 4051 = 0x993b6644dde8a8 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x993b6644dde8a8 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 120233 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 120233)).mp h
      subst hqe
      rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 120233 = 0x529af737261b8 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x529af737261b8 (by decide)]; decide)
    have hqe : q = 44706919 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 44706919)).mp hdvd
    subst hqe
    rw [show (0x978c6f353c3889a79 : Nat) - 1 = 0x978c6f353c3889a78 by norm_num, show (0x978c6f353c3889a78 : Nat) / 44706919 = 0x38df2e886c8 by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 3 0x978c6f353c3889a79 256 0x38df2e886c8 (by decide)]; decide)

theorem prime_q3 : Nat.Prime 0x10dbff26eab8198050172ee03275 := by
  refine lucas_primality _ ((2 : Nat) : ZMod 0x10dbff26eab8198050172ee03275) ?_ ?_
  · rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 0x10dbff26eab8198050172ee03274 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 2 0x10dbff26eab8198050172ee03275 256 0x10dbff26eab8198050172ee03274 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 2 ^ 2 * (3 ^ 3 * (109 * (29047611873442575647497758179))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 0x10dbff26eab8198050172ee03274 by norm_num, show (0x10dbff26eab8198050172ee03274 : Nat) / 2 = 0x86dff93755c0cc0280b9770193a by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x10dbff26eab8198050172ee03275 256 0x86dff93755c0cc0280b9770193a (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 0x10dbff26eab8198050172ee03274 by norm_num, show (0x10dbff26eab8198050172ee03274 : Nat) / 3 = 0x59eaa624e3d5dd57007ba4abb7c by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x10dbff26eab8198050172ee03275 256 0x59eaa624e3d5dd57007ba4abb7c (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 109 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 109)).mp h
      subst hqe
      rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 0x10dbff26eab8198050172ee03274 by norm_num, show (0x10dbff26eab8198050172ee03274 : Nat) / 109 = 0x2798a71bfcfde2a5237129fbc4 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x10dbff26eab8198050172ee03275 256 0x2798a71bfcfde2a5237129fbc4 (by decide)]; decide)
    have hqe : q = 29047611873442575647497758179 := (Nat.prime_dvd_prime_iff_eq hq prime_r).mp hdvd
    subst hqe
    rw [show (0x10dbff26eab8198050172ee03275 : Nat) - 1 = 0x10dbff26eab8198050172ee03274 by norm_num, show (0x10dbff26eab8198050172ee03274 : Nat) / 29047611873442575647497758179 = 0x2dfc by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 2 0x10dbff26eab8198050172ee03275 256 0x2dfc (by decide)]; decide)

theorem prime_n : Nat.Prime 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 := by
  refine lucas_primality _ ((7 : Nat) : ZMod 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141) ?_ ?_
  · rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num]
    exact pow_eq_one_of_mod (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 (by decide)]; decide)
  · intro q hq hdvd
    rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 2 ^ 6 * (3 * (149 * (631 * (107361793816595537 * (174723607534414371449 * (341948486974166000522343609283189)))))) by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 2 = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp h
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 3 = 0x55555555555555555555555555555554e8e4f44ce51835693ff0ca2ef01215c0 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0x55555555555555555555555555555554e8e4f44ce51835693ff0ca2ef01215c0 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 149 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 149)).mp h
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 149 = 0x1b7d6c3dda338b2af3f920a4f089731d125410d933777a02fad3955220aac40 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0x1b7d6c3dda338b2af3f920a4f089731d125410d933777a02fad3955220aac40 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 631 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 631)).mp h
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 631 = 0x67dc4c45c8033ee2622e4019f71311717cd420d26edf644dcb2f9e0ae0d8c0 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0x67dc4c45c8033ee2622e4019f71311717cd420d26edf644dcb2f9e0ae0d8c0 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 107361793816595537 := (Nat.prime_dvd_prime_iff_eq hq prime_q1).mp h
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 107361793816595537 = 0xabd18a4164f2ec2b49fc50cdb7e270542f2560a0f700ae1d40 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0xabd18a4164f2ec2b49fc50cdb7e270542f2560a0f700ae1d40 (by decide)]; decide)
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | hdvd
    · have hqe : q = 174723607534414371449 := (Nat.prime_dvd_prime_iff_eq hq prime_q2).mp h
      subst hqe
      rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 174723607534414371449 = 0x1b07134f42e597994a25928e75887fca5ee37069dcb3fb40 by norm_num]
      exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0x1b07134f42e597994a25928e75887fca5ee37069dcb3fb40 (by decide)]; decide)
    have hqe : q = 341948486974166000522343609283189 := (Nat.prime_dvd_prime_iff_eq hq prime_q3).mp hdvd
    subst hqe
    rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Nat) - 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 by norm_num, show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 : Nat) / 341948486974166000522343609283189 = 0xf2f3791ee0acbee706e9408c5f0cf13469440 by norm_num]
    exact pow_ne_one' (by norm_num) (by rw [← powMod_correct 7 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 256 0xf2f3791ee0acbee706e9408c5f0cf13469440 (by decide)]; decide)

end Solution.Secp256k1ScalarMulFixedBase.OrderFactsCerts

end DonorFile5_0

-- Adapted donor module: OrderChainReflect
section DonorFile5_1

namespace Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

set_option maxRecDepth 65536

def daStep (gx : Fp) (p : Point Fp) (t : Nat × Fp × Fp) : Point Fp :=
  let d := dstep p t.2.1
  if t.1 = 1 then cstep gx d t.2.2 else d

def daScalar (steps : List (Nat × Fp × Fp)) (a : Nat) : Nat :=
  steps.foldl (fun acc t => 2 * acc + t.1) a

def daChecks (gx gy : Fp) : Point Fp → List (Nat × Fp × Fp) → Bool
  | _, [] => true
  | p, t :: rest =>
      let d := dstep p t.2.1
      (decide (t.1 < 2) && decide (p.y ≠ -p.y) && decide (t.2.1 * (2 * p.y) = 3 * p.x ^ 2))
        && (if t.1 = 1 then
              decide (d.x ≠ gx) && decide (t.2.2 * (gx - d.x) = gy - d.y)
            else true)
        && daChecks gx gy (daStep gx p t) rest

theorem daChainOK {G : Point Fp} (hG : OnCurve curve G) :
    ∀ (steps : List (Nat × Fp × Fp)) (p : Point Fp) (a : Nat),
      zsmul (a : ℤ) (.affine G) = .affine p →
      daChecks G.x G.y p steps = true →
      zsmul ((daScalar steps a : Nat) : ℤ) (.affine G)
        = .affine (steps.foldl (daStep G.x) p) := by
  have hGI : OnCurveOrInfinity curve (.affine G) := hG
  intro steps
  induction steps with
  | nil =>
      intro p a hp _
      simpa [daScalar] using hp
  | cons t rest ih =>
      intro p a hp hchk
      obtain ⟨hpre, htail⟩ := Bool.and_eq_true _ _ |>.mp hchk
      obtain ⟨hdbl, hadd⟩ := Bool.and_eq_true _ _ |>.mp hpre
      obtain ⟨hab, hsld⟩ := Bool.and_eq_true _ _ |>.mp hdbl
      obtain ⟨hbit2, hyne⟩ := Bool.and_eq_true _ _ |>.mp hab
      have hbit : t.1 < 2 := of_decide_eq_true hbit2
      have hyne' : p.y ≠ -p.y := of_decide_eq_true hyne
      have hsld' : t.2.1 * (2 * p.y) = 3 * p.x ^ 2 := of_decide_eq_true hsld

      have hdblpt : zsmul ((2 * a : Nat) : ℤ) (.affine G) = .affine (dstep p t.2.1) := by
        rw [show ((2 * a : Nat) : ℤ) = (a : ℤ) + (a : ℤ) by push_cast; ring,
          zsmul_add hGI (a : ℤ) (a : ℤ), hp]
        exact add_tangent p.x p.y t.2.1 _ _ hyne' hsld' rfl rfl

      have hstep : zsmul ((2 * a + t.1 : Nat) : ℤ) (.affine G) = .affine (daStep G.x p t) := by
        by_cases hb : t.1 = 1
        · rw [hb]
          have hadd' : (dstep p t.2.1).x ≠ G.x ∧
              t.2.2 * (G.x - (dstep p t.2.1).x) = G.y - (dstep p t.2.1).y := by
            simpa [hb] using hadd
          obtain ⟨hxne', hslc'⟩ := hadd'
          rw [show ((2 * a + 1 : Nat) : ℤ) = (2 * a : Nat) + 1 by push_cast; ring,
            zsmul_add hGI ((2 * a : Nat) : ℤ) 1, hdblpt, zsmul_one_affine _ hG]
          simp only [daStep, hb, if_pos]
          exact add_chord (dstep p t.2.1).x (dstep p t.2.1).y G.x G.y t.2.2 _ _
            hxne' hslc' rfl rfl
        · have hb0 : t.1 = 0 := by omega
          rw [hb0]

          simp only [Nat.add_zero]
          rw [hdblpt]
          simp only [daStep, hb0]
          rfl
      have := ih (daStep G.x p t) (2 * a + t.1) hstep htail
      simpa [daScalar, List.foldl_cons] using this

end Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect

end DonorFile5_1

-- Adapted donor module: OrderFactsChain
section DonorFile5_2


namespace Solution.Secp256k1ScalarMulFixedBase.OrderFactsChain

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.OrderChainReflect
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def Gpt : Point Fp := ⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8⟩

private lemma add_vertical (x y1 y2 : Fp) (hy : y1 = -y2) :
    add curve (.affine ⟨x, y1⟩) (.affine ⟨x, y2⟩) = .infinity := by
  show (if x = x then if y1 = -y2 then GroupPoint.infinity
      else .affine (tangent curve ⟨x, y1⟩) else .affine (chord ⟨x, y1⟩ ⟨x, y2⟩))
      = .infinity
  rw [if_pos rfl, if_pos hy]

def steps : List (Nat × Fp × Fp) := [
  (1, 0xcb35b28428101a303eb9d1235992ac63f58857c2f631ee6936d3aebbeddcd1b1, 0x342119815c0f816f31f431a9fe98a6c76d11425ecaeaecf2d0ef6def197c56b0),
  (1, 0xa69c17c116bc196cf7eeea54e921c6c8a847cd1fce7830438b85c5d11d8edaa9, 0xad2b3931a9891201744bcc89bbb32e3afd8deed03753e4e36ff188142c1ae831),
  (1, 0x659311991ca04078c1465534151e770c98550f899013bf61da72261783756574, 0x25c5c9307759a75241f547426a6095a0bb85d8b106acfcd2732e68d811be1c9e),
  (1, 0xe6a376128ed85c27cc8d1715fe74624dfcd01ee0115740f5c5e017d0161af012, 0x93f65110c76f11b07c58e9c0e2a52efa148307670282ac14182494421e374bbd),
  (1, 0x5e7003bc5c5e610d341ec2329dc7b1ed2c303306520bbc0fa534e7a7bd8f5dde, 0xc9bc4235998f210bafc9977fe99b5039047652d9821ca9d0c8a80c4ce980245e),
  (1, 0x32f5769efc31029e0584dbf3e6a5e370540b625e0b45daa714b9cf24586db45e, 0x01a3155af6abf5bdee9a3650a76f935852cec622fa454097ea6c50bcd3c73657),
  (1, 0xa970ed203cf82d78993982874828630b31f923d00678c56205bae895c74eeb79, 0x2ad68424fbd3df569a0373ffd2d460262e251a2a6432f19b8d5beb1c8883b65b),
  (1, 0xfdc05316bccdef41929bb444f454112992782117d25da4d2c0db71c8b74b8788, 0x4b37c8b6ea2a57fae321e09e111fd106a0799995d565f545ff2511e711de79bc),
  (1, 0x5ec9ea081be56f477e52d9ae87c1e0b2de6c3d9e3028a9faf5471bda5259dc98, 0x75488fe6d6f5555711738503b8f0d5e0f8fb600126bb71e7f00b6042959baba7),
  (1, 0x4004a33bac0d8f62d3f6c31239916e63f09ec97157baa54f5debb8cbe42b9e41, 0x68639c1646ed2c0ec46965ba91e858fca8a3fb0eaa467ad500dcbe854902cd63),
  (1, 0x307b140cd5924759a8a7433af4177f3f84b728d90350acc9a46c58a2416283eb, 0xea99047f80666c87c4356f01bba505b8c29383d0f1efb93c599bff86c144c93e),
  (1, 0xd6b5cf9acfc8f6136cd1865243cba6195cf1d713bb80bbbbc37cd562105a2306, 0x08a7c2ea05451cac597ae5618f915c25646fda65e89e697b06aa769c6135e376),
  (1, 0x4a6afd1c53c51ff03f1ef8b699756150670e26fae5218760cb22c3800e73eb83, 0x1eaf3b101e8dcd7ff2b4f99c319be7a1f7d6b73deb2b22be1e708d6afa6a0d54),
  (1, 0x0e8e42d16ee4dd99241b885b3a36b816e6d286c8d3e9c72150028173378d6359, 0xdfba4f8fe0dcfe15c4bd430eeff98965b9130f6a63c73df6c1921c22bb1cd254),
  (1, 0xd94434077a3c1d4e96c5b3a2e081a85401a2628ae27a984e217363615d60a0fd, 0xbbcfa52543c629540020d2ce5eaee81b54727ab0be0f8642e4d5b16bf5b41d46),
  (1, 0xaab4e6c2e159f2cd6bb3f953d07b0d3cbe283c4540962262287452731b1fcc02, 0x8182b17fc6dc6d8f3d9fcddd70c5ddfb0d0472210ebe7de98a6a10baac8d1897),
  (1, 0xe11f6835001369eb75086850c070bec01046ba9c0e53c569b858592d253bcf01, 0x697c83c2ceda54b32f6c3b03618021c7f17f6e39ad989f5b4b997fe45d552885),
  (1, 0xcad98b2b7f0a886d5c6c49b457e52e12f411702c82c4781c5ece28fe320acdd2, 0xbe96787c330b96736883265ffa6917bd94e0d2be9b7bcddcd5ca67c498a239da),
  (1, 0x7bfa5d9b2231d1801424c515ce5da4a58a80657edd45be0188d1a3346b79faf4, 0x9cf4bc381a4f40e93b537c96215331c947b566574d328a7c83b9da1d007d4d04),
  (1, 0x8f7af2ee5d876514f60b94223fa655b2dfcf11f32ec2b63f985b437ba029394e, 0xa69e5d458e4c86df47ae982e052155e7447d40e517fed7a1d397be3f23dfca7d),
  (1, 0x9e8e880da673c5c35126886f5442a54fcc74f069ab5f4b17acd98f6ae0f9e7b0, 0xefbca2601db795f0b70e42e3608accd681143d91c27547f996cc4040e6ed2e8a),
  (1, 0xb3ca12947672652375ced933e50c977a4834b239bd2dd34104bbc5a03037bbf4, 0xd79f4f01dca713bb20f7e4ec31b100cb8385182754c228a43b7d047a2253ef4c),
  (1, 0xf714a25c129989ddb07bc33736ba00167e9b184172dfb22dda00c317a66fcb42, 0x0d2dc16026406ae35a0663c4ee71527665968052eb607e8e61d9c839c2c1f4c8),
  (1, 0x165af19d1a8f8251a10f075372f3abea524b343b77743970005b7145e6846846, 0x27096af8c8838142d8d79e997ec73b463efa3daa5871cee9ad4b57a474bcb05e),
  (1, 0xa1785ce327b6253c5e3f3d54cfff680aceef47a5cbc144f3baa90f875e336534, 0xed2630a67f09ce69ed21a45976bfa99c7488941eb280101f0910155fa548b8ef),
  (1, 0x78e2f3cd7964eb916b99fb98c6106d355416254b6817130351672621c022fef9, 0x517843307ee8601a66b5c07b23bfc8a5b6990dce19e27d1d0c1341d6e5db5a0a),
  (1, 0x90b7accf9b0634e7636612afbbe7b0430cfe6f106996579305ab93ca24e960e9, 0x27f195f6f4cf4b4f4247222bc5e0a63c84f8dc0044d8434e6967cd633583ac12),
  (1, 0xedc100775d0e753b864e9c138af3e85ce9babbdc55156e5f125b981bbfd6f520, 0x7a5876e995a23ca415b6401e8f1422044eb5d628b8e7f1be2f2b23b179638ce4),
  (1, 0x34448962937c0d600c1967e421707c61a59d1c4adf47d1aaf76ca775be803070, 0xec9d8b600f104ad578eea08a5a5f33d2386a46be5c8b144f525b5952a98bf573),
  (1, 0xf8840516c757d0a6c6f15a190cba025bea247396f2dbc670ddb91854bb82dc9d, 0x206dae4437a18c0b68bd3443b585779c016fcdf4c643b36a18e520f8ece00a7a),
  (1, 0xb2307fd8e73711cbd2a5acb254cd6366ea58393ed307b03dcd9b9dd2666038d2, 0x182ff63b52c5f822dc158ee256f391cc6756095669c3d4d07254f4072031e273),
  (1, 0x2573d5756ec32c905e510a4ed8efd39fd4da7ce8f4300c38b82ed0b8898024a8, 0xfff61f6a679952b10282c9d6b4964bab529faa70b621f2b31d3c88f0f7c7cc9e),
  (1, 0xd734a7e52dbb035ffdc25990fa1ccdc84e14ba899f6c60d22620b21347e3109f, 0xd4884fb8826291f77f821c16080f56a85c05dd6a22b2a11eeb48cda23c3ead0a),
  (1, 0x53dee14e1e679efe0fa5ddbb4474c4bc3b62c38fb29ad2f66b32d02cf7769e26, 0x0ca38791b0a89b2e2b2fe934b7923fa72237c623fecb30bfadd6410fd49ef94c),
  (1, 0xb863f4f981f73bb8ce379072cb8929e3d5143b31be0ba2850acd8d2a9428a15b, 0x04e236135fb12ae1dd09f7b6c4362369ab0f04edf24575a62633b681957080d9),
  (1, 0x4df58bfddc64feed703e053aeb426c49b42ef4e12cf39569dd1c47b17ace3b8f, 0x92776b0dafe4eca1bf06e30cd3425605d46299b3dd71d5ad3dce56797550eaf0),
  (1, 0xc6833c3264fd8e7192fd60e10366d4d696497985bbec4ad97f9b79462e2fea0c, 0x1bb82722844f690161c0d8bbb1cd95161b50cf17a41214fd660fafb194ccf374),
  (1, 0xf792a479fc3f4b006bc0a43c4c60e7d3f356d33e56a6f2a22ca8ac6f024f0805, 0x2cf6c4b0820a957e7aa0f16c4f1159824389a7cf44dc0729707faa7b91efac28),
  (1, 0xdbea84bdbe79d31de5ff551604ff4e4e3a888a9e1fee97a1f696ea2385bed8b0, 0x90bf7663bdc4e6d78332bfde61ad4e1cd57db66bc6d1a5ea8feb6377c0428204),
  (1, 0xb1b927bbe4f17c53994f61929fc540bfdf36fabe2c44a77620ef8cb461a05820, 0xf7c67d831900b7916f895052a0059974f3c6ef5e5d3a297603d3d3188fc69677),
  (1, 0x840bf5343809468827fe4fced31324995ba6eb48219847dd627a7244cddd884d, 0x2451e22327463a96200349fc8b71b56548c54faaf0a7bc7d15529aa8603c4d8c),
  (1, 0xe5fae193159084f8528ffa90342792029cff2f1d3e816df2ea4d6f488f751ac6, 0xb83c1c2c9af899a6371769e1c6de7227a234f115b608559be303c65fde028566),
  (1, 0x33d81c3daac368d14470db3c04b2b8970860e1c0e5ff7fe25478ceb52b6420ac, 0x850cc4d935ae0a8674ebf5ea92f38ede47e98e1f02e478e0c2a50ceb5ffab32a),
  (1, 0xdb3ab30aeeb3407905cb4cd5376fa82b0d04be013fa13ec1874252629371b024, 0x9c1e0d91dac37d1b380cc87b5daba9e4b1fe00284ee84c461e456d2926ecab8d),
  (1, 0x94143d460ac5968e69950b84ff0c31708467c65ec9d6603a108e31f07b0aed31, 0xae2892d821619350acf649d9b047175e04193dae025d3d5f529d65eb7b4b411b),
  (1, 0xd199bee5edcd80195e58a03ff11d217efa4bd55796ae4da1a5233cda3a5640ce, 0xfd3f35ae90e60e68bb9ee7415c8761319c6859e894542398558c13b02008fe19),
  (1, 0x2001b659f6aa63038ebc76e9dc176a66951d74d7673d9098eedd9634316fbe37, 0xa5f01a846dd6063ac66bfa48a879fe5b448bc9da3916cee23a43be4478306ec5),
  (1, 0x0f22d7a098199475a8e37abebfab1b57554124dbbaf249ae015721fd5bcf49cb, 0x768255742da33703d1c25c7886929f283c4319245da1ec5403e485d7040bdb84),
  (1, 0x13c8d40371df66fe1a8fd4efaa2987cba6b1351b438951b8bbd7d86a52f2654e, 0x3e05cb92b89ba11163eae1939a0c4a15b5d0166d2729e60d1712e33e378dc4d1),
  (1, 0x9ee7121ce457b0c95449a7c47a91a300d867c95108b19ef361f8ec42ef9937d0, 0x68be75e98880850d0f2b25c6f942754d24d8fd1a75562e91c00e444bdb6e526a),
  (1, 0xff9692bc153fdd34a3e639d20835531e1fa4ecab124acd020d04d3aa038f40f0, 0x6d0c6bec6b0a25b6c94a9690c4ed47b8592c145daeadd0f803f6f8963a64d19a),
  (1, 0x39967194978e4ca8f5847a20ffb23c6afe7b29b787adf79f428a7e06b701e32d, 0x070c83f08b44ba5724d92c2eb9419c939608e92ac2e21a7bcbed4fcafa973816),
  (1, 0x9b7734666085e78da3a0b58d3ed86ecbc4888ce7f4b338f9f7bc496b5ce4ae5b, 0xcd11e957919ab1baa1c2a4623f859c2a5c25cc7d659283929513e274dd6c0dac),
  (1, 0x60711e6d8febbde20bb683012ec65ca2fd2fbd4f528e7c88b2d0ebc1323a98a3, 0xbb5f81c1db4efde192811e9c18fb0247bba27044120bd6040fdaf6dcdaf3f621),
  (1, 0x844c870fd70e5e0839bbd92f8f66a7397f3b120dea4dd8f31014d4d93974eb7e, 0xe86d3d213ce0751b1459ea7bb2b2d2487bfb4bc3778cb343cee44d4271f76cd2),
  (1, 0x8dc6d60ce47cf022df5b6a2405fe27e827e8c9b4aa74bf9854429b4bf61461ef, 0x6c3c6a9bc06d13367cce6f18949a42901bbd382fcdca8d14da78a4b25e659577),
  (1, 0x569c0da55c00e50d3fa8a2fb8bfd6e2fed3f2e01b6fb2c83cdc77db61fca1085, 0x1dc48780f65d7f1baf557b0eb4cdc417e2043a29b2c779b283eb45641a8dee89),
  (1, 0x002b5339cc3c5a99cd3033aba14d2a1b84555b7b57b1e6c9c951ed8ccf0ae668, 0xf13eb2a3b5286ce78ef10cc980fc2b1e94878c327e2b87c70416377404b14dfb),
  (1, 0x15777a281223ea5514ec527f34aac11efef9ecf0191122b55c2c7d7ae7b65e35, 0x91e2d4b313989225dff1c1dea3a2e3dcea12ec3b60022f3a2a60ac30ed5aafed),
  (1, 0xca717f2ad06050149e714fa98e9cb3534a3e305d7aafcd12779e19f8cebf8a97, 0x70540af1dd215a4839af145f2dd96e72ee86038d0923faeb51d40539355040a4),
  (1, 0x94a3a867589ded60a4d4c39da744fd73fa9cd3d99386ea5d4109937093929ee6, 0x1c22d7ae5b4cc23b514b2ab9707f58bd07983e00d77b97ca6887e66e27e7cf6c),
  (1, 0x860972c9f748d4b8b7b8d51dc1dc7d837071e36594736378d26cd51d6fff0d78, 0x50f91d9961dc9f24b60a3945127d446f59cf19dc0004c74355218e2a214c7677),
  (1, 0xaec30bb522ea06530a4c825d27a8642d2e54de040019594755fd88f254189b51, 0x5c1dc63f9292de085a39bb0737a0b5366349725df6689a15831e2c1eb95cf854),
  (1, 0x6416e00254cad57f9c8f0da2900ba58381c9fa956905906b58182bb65bd19569, 0x729d9c6000029fb5f61b5f6ae1a23f77c186693585aab23bd9e18d20c0e8ee64),
  (1, 0x0b08d3b0ff2a61219c9fe4f6cc8558a0d2b164d481c18314bc8e14d9a8e2f6de, 0x615f38e01207114ff1861a43c5ebe1db8ab232c44ae354752c65e49e540e3563),
  (1, 0x527b6941229c941541a7dd9976accb0b824821e92a8f0d9cb6a73e9a160724be, 0xfcefe7d2fcbda8097a3716a7251e36efdb713cb1eee281bb5c8abdcb6230e1b1),
  (1, 0x557d86da23a0258e425f93b98d3ea3ab1b0de042fff9d114ad74066c3c184d83, 0xd162f4a771930b30b3b897386a5e94302065d4b187f4521023708bbf9b6bdc57),
  (1, 0x09c4356850d5094534e637566f6c726ba8fcb613037f678a716d442bc95fbac4, 0xfa631c4edff9cb1c88cbd69b6f188ff8701acf345655142187e3b89a7c84595f),
  (1, 0xe2562e55d3b198e3ef63f1037c61348b42c40e1f21b203f3a426e3818644fa94, 0x2252f429d4029c4a45e16765b14dea4fb90825346b92a9043423a099e9f1d93d),
  (1, 0xb70adb31dd7be77e821726a8c664cffde80c3420546fff30135fd8a43eff556b, 0x7310862502baf1b478ace1d3dc2f829b7921559049143abc8810b822c3260973),
  (1, 0x01db801d65431ec73b70b3c81d7fe4835d28296b608eacdd0ecd12e8542f0027, 0xc92a6397cfc740e02898c232eadd81aac13a16790db1e7e38c91c53bc53469e9),
  (1, 0x197507bb87eaee76c33b94b7ce541d2199ae081c53a3b08a0b8ef0037f6ec721, 0x21ab75b6cccaee67388f7e747d0e564d40bd67982c750cf4f7f07f585e0df311),
  (1, 0x2cd1272169720c1e819ae5b352bf34ff15c7b194636531ae3f73f7c0d8701b57, 0x5ce7e86a70c7072af7e4479f884e89b27ccc3863e312c79c0f6619e7c439f074),
  (1, 0xdee8a576a51dbadf2e2ef4d898ea6daa4f2109b874c74b2c3f63d0ac5a0d0d6e, 0x3b05b489c04c2187b4a9d7a1367e2b39fac23afaa3bd3c0836a3c6177dc45856),
  (1, 0x02b0b225eab80369ac2b1af015fb308feeadd38131df1858932b1961560e0a8b, 0x7ed493556a8f1396d627fe6973f99460d03b4b39175d3c741ef5d9f53cae4cec),
  (1, 0xa341a365f2dd635e68534f13ce12049c7966cbd672fa3cb3f62e1fc38906e48f, 0xc0ddacbd87b975ce779ed42524ee1d9931bf9b5ec1212b1b87b7c083db73cbd4),
  (1, 0x76970b97d9207ace885b30126597e78de86b06ef2b83939f44f623fa37173d83, 0x087ad1ee68b8526ae77432367a5daedaa6a50950e6e58a95a50eb1170a87c580),
  (1, 0x981f3aee604bcbd7b5158a7cf47e16faf24521b7ba69fc91a1ef624738016a21, 0xecad9d528192c33d844a817582166d07172809974b51248ef3b3ffe2b817b6fa),
  (1, 0xd33b8637be3c994354670f7704b974108b2d048151604b5b642ec0f8bf8a52db, 0xdb783adceedc155300f48ea5bd331cfb7bd8fdc5e96c6b11b3a15bdb46651f79),
  (1, 0xb67714fcead854f4d4c22727fc0287360fa00c21c22e80006f588dc5dfe27f80, 0x05273c94931f5b43b3fddca7e15a73472857088a92beba2c95364be6e8c20c74),
  (1, 0xe936539a7df5fc25c059320acf3a12c9979af7af882b889a707126ea0eace6bd, 0xde0c02b305b43882a8ce56d9a304fba1a06f347de0299f1822ae51c45788bb2d),
  (1, 0x0ecd54bdd5f2d838db6dee30c756c9806bd8ecc5f5dee2bdac0cdfc84e9c0e86, 0xf7060c7095b0a913f4aa3dec9d992e9575ebd4fb5e0c78bf8f4f50a739be8eb3),
  (1, 0x23b5c86e7068617c26aaede8689f6a954ec64583db3d7e0a74c0936453fbca38, 0x33f2da73028226028897cea817c0a01fcd9abd54702d315eb8cfd6966109d46e),
  (1, 0xa41b8e11f15e7cd600f561c52dea0cc66e95a8b8e5b4bfb5ce5b98705e7635b6, 0x85325ff9903d466da37c3113a60e1e00fe555bd782b6f2fd2ae9fcb44a4c9004),
  (1, 0xe918ab9d2c9cbcdace2f68930376c22eb8ffb01541170de1443a9c0b22ec86f2, 0x84f346c5c5f330740a3de736de5163cc8b858dec135c46172ebd15679c1170ca),
  (1, 0x1f920a0a5493e54f7f0aa38908d72884ee541ac299d2840ce6a42c0d22eeb0bb, 0x8abbb205208a2911dbbfa33e5e94aa15d430c510af215dbd2a48fcbb30143742),
  (1, 0x867ac1edfaebffebb462b9334be3f46f9e16e4e2546670de2b6329d78273107d, 0x718af586b76e13a633189294fea60f2a1b48e1a4ab0d9646c3190f7c66e50d8f),
  (1, 0x652448f8abd4ba18764ead490ac6b489bee735faeba7368138520e0e8452fe74, 0xbd4cc188c69c6f8e5ac86965c65cf562b502dd7b98ed9b54709f92d25c690f74),
  (1, 0x1b35aac1ea24fec1528f0f38e1da21f3ce60f896a171eb4674fd54d4e6e072c0, 0xfe2650879006eba632896291d99138a196bd7a3b6bef34f9e85aa08cfd1e1e26),
  (1, 0x4dc90360e6a2876083f187f3ffb3feee5c347841fbef83e0cba8bad9f6523d36, 0x34d1dfc055ab8a6b9105c34d474a6cba02cba5965ab0e90fc30cc9e81de00b7f),
  (1, 0xd64bedd770115aee5ba8a0577990a7dbd8b6fda15584132b6cfed17604190f26, 0x4b5528d391655423d32797139a862fc62f4cef428fab6c1aa29d56d218138709),
  (1, 0xce33c3ae098e194aaf5c5df9e30811bc0c7592e465d1c96159de36691a5a1265, 0xb27090b7629536d502acd56365f06e90c380f5d683837d9e79d8066cff72bd49),
  (1, 0xe49527104a6dfe145a93a241555af48b13236ab5200713c20c8d9fe3df8a001c, 0xb00df8f4a7a79067c177b99e526b8c8355c0f9587eddc597867feba3d31fed10),
  (1, 0xc78535653fe1f65823a9f553e51eebc39b87a6d04a1a79df452c7739d7e50d5f, 0x758008bf43633aa80818728d5b8d753efdbf3df67222d0b60521225b1c182353),
  (1, 0xdc6ff8606a89255398986e1545a4edd87789dcdce1039891aba3144eb1638d49, 0x7f874347ce8a359d84283f250be0351e9ca7ad7826ee6d80653a361f9b850af5),
  (1, 0x8a93f16e1b0223af79c6c8c93d88c46e1ef2c5474d0b3606026b8e157385187e, 0x2a194e5b6298a3c8bf25d226afe4d30f884fdfca9dbfbae3bee8adc5a62a530e),
  (1, 0x9b7992df133f447f71a83861c9083a0eb4b57a6a270fa6b14c58cd1fa7552c7e, 0xc7ce009b4be5de9735a6c2b354d00fbf3c1633770b4bc3af6e0b0ffdd596b50c),
  (1, 0xed31f40d405010f51da05f5989d408623cf8a2ddbb9066c25b0588084c3089e4, 0xaf68fc9b7387a810f0ea288b9e98befca1411c41d6725085109c5febd77a268b),
  (1, 0x19b22b3942388afc1f32d4cc42f0adbb17b2ac973a795fdc90d4f2c232879301, 0x99b092455957ccc10fb160e0e16a58a0602994993237e1522f93a364c45b6311),
  (1, 0x1d6432c2da8f757222036a50616ea28828523cd971cfb5a82f1b2341c6a59423, 0xe531526e7bb34216ef2b640e088e2bdd2aa1a6d4e95e4be0319186b6ad7c7c2e),
  (1, 0x63c1573f8516f133d55f059a7c3fde79c1f0ca62d0e008ce68d6c4301a3616e7, 0xfb5edcdf4a00eeb881d382aba0801ed39b8932e106a6ee03633ae55c156e8a72),
  (1, 0xd5334843bd6d76c5b5a5fa6a0b22caa8d0d10fc72211528034cbb8cb1054a18f, 0x62c7b4b5c40013fe5aaab64168dc5b05f7f5e551ee092560d1319b6b895faef8),
  (1, 0xbb3827fb22788337ae1df75820c10dba1d0a02a01923505ce4f2c300a9fd19d1, 0xf10134671de373ee7a98c27e438b9fdf3e2b5c4a6e06ef66193c9a3ebbdd96eb),
  (1, 0x66db9e23da9f2357bf6318722ea787cd09ff5ee3c6f23f7c86d0b1ee34bc9187, 0xdce4d2903d8debee56cdd66905fa952c5ddb8bd2418c6bcda1dc9c6a473602b0),
  (1, 0xdbd551b4f4b064658c6ae01f2bc16c90bd7b4bb15f3911fa975d488a3d23946c, 0x78cc8ecab967d37cd6b2da4cb5e9a0ab77b3c178f3e8e2de8ef8578a28f6564f),
  (1, 0xfd07cbc6b6fac24360269e3fb3ac3d310bb1e63da2474e7069b50aa45294a806, 0x9e939eadd68cea5832b8b6b77cb2a2b527b141985d88d766fb17875e3e8a2080),
  (1, 0x8cfe79c35d9c37ade49de818e690ea5a4e91ab2da9c49d78caf19deb13b78d0c, 0xe80835b2aa686d157f2a33e26e0acea88149acfcb2a29aecc27a12cf23766fad),
  (1, 0x86e69eca4123bd8ed48c0fc92b0ee76ab6b5c7918e97587652c8622fdb04255b, 0x034ff9095a7ac1a5ff9e3c459a0a8f8c5584d8c312060232c08f8daaddb0a8e3),
  (1, 0xd9b4f2cfff8d2a8578266507be4f45f9502a09fb7d44db29a657839714796ade, 0x60e22764990a0b794c7d1de3b54202824dfa35a9f84aa8477041e667d4182514),
  (1, 0x47f6f2f5e6c3aa727042bc51c1d8cde6b9da044815ca4441951e73f796463a37, 0xe463b1f3be7bcf0121351bfc988da8ee9a3c81359a1d2f522819a1e5548a2a29),
  (1, 0xade49f68d6fd6e487cf915068fbc4ec88a0ad4d0563220ac502786e1aeb704fc, 0xeda39ec07448eb34008e524710aa5e618665d873d8511ea74c867aa4b3dfcb80),
  (1, 0x354a8d416df2b76ea671bd2d2a75307b9f9fa39d760f7fbd7f5e8ddf395a08b7, 0xed5224bd4a473b716dcdfa4d54fa885a648f186aeccf5eb66f961506c33e2f78),
  (1, 0xade8d83bbae2c4b420a9ce77a4eafde582547186f02ced7e69c4f2b9dce10d82, 0x2a761a7dc5e8a55deabce2d7b0c20d12518c1d2f9114ed21f163e41cff7d39e9),
  (1, 0xd5d7222416c8d775e5be42e1edfca5f4450acba72abec0b9a8e3fb4fb3638fc8, 0x8b6a8d24ccb7d31a2286e7136b78a4b2223ea105aa37c76335a599cd42d08139),
  (1, 0x6fb28815a0ecc97bf4a050d191cffbd517fb249ef252208a553ff491df4873ca, 0xca42f919f1df91da1a791fe4b2cd9c6746ab246901643f22a4e0b23baaf9dd52),
  (1, 0xdc8ccc03200a59d75dabc5dc646054194dfa1fb9262aefbee3773e8f066b4080, 0x71bd58e350d2b45c8397e102c7bd224d01f57ed1d0d4d2fe28dd1757897fcc40),
  (1, 0x7cf785896872de292ef8d04c9a4bd6752b0283b334aeeed0926d62c60f84c63b, 0x7a305781e019ba6b148ba056630113ef1830fdaa5d0ba86fc05caa250a5dd834),
  (1, 0x5cb0c9f432b28592337cb60e8fd2e4433de1e82146b736c25e8507e2c732f8b2, 0x59b7f9fa755e393a86f41d14fe1f4355255e0c02aa59eecbe0f8d5cb2bbce45c),
  (1, 0xcc1308f867f37f966586c3aed97b75f5e0a4207c34ac1b6244031de9dc378b3c, 0x8dce13d16b53f0ed2e56d71d776aee9f30a72d0bbeab3ff635acd0f51d1fef11),
  (1, 0x28cd61f487b08fe5c086fcd582f7ef4d038b3b1eac5dc027ce3ea940a702f395, 0x19a1b2ea3e2f9d1b03efa572c8bfd71d2e19827d8139cbcf71d8e330fc463a08),
  (1, 0xf488531013396f122c6380fa9bcf529a4a1a8030f0ee0fd7f086881f3b47296c, 0xc85eaf6bfea3313244ba71523b1bb1e4897b08dd97961a63439b7ada636f1583),
  (1, 0x6fdf88045c35210fba115a99e7e1f0c22168bbd4e3696a2a7b1c88453ed23522, 0x88b56f437405dd5c8a57c4f2e77b944b210995e5c13adc843e442b389724f6b9),
  (1, 0x850f025e53a726ece94569ab7f3110ef61eebe11db48605146ce512f7b9cc1d6, 0x9780d7cb0408d9bf2c9b149e3506e18ff42307ceb5d19b896238c9c6a7fbaf6f),
  (1, 0x50c599c6c7eed04de4557b70629938a5efe449553afd480ac0f9ae995d344f65, 0x9ebf94382972af6bff3a9a57e24b68bcc508cedad241509f342b151e7db2f71b),
  (1, 0xba29075feeb1944a203f9f27aaec6440ce8936542cda770d1ac48849547da262, 0x3d1cfb1c8ece579815a1bcf52cba51fe6d41c997cff3edef46f3b1a0ce8e2d19),
  (1, 0x024af2cf595bb5989820036d1cf891744291d712a3b49a2bab3287a5931cdc57, 0x44565f3dd57f21a2781d6b23391b8fbcef09d46ca234cf171d9dc7248d06418f),
  (0, 0x15d30e1cde739d10772cc7d6bbc109f5a3e23e6a66fd3a77e98839167464fea3, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x70f9f0dccfa3e73c342b7584f48bfe7576b17844686138033787e8a7e6462e86, 0x50d5089b5a74ed3712292c35b44e806bb3cc8e35d3490c682bc028992692b755),
  (0, 0x798ae92376ef80df046f55128ac898e9dd2bbcd8795657eb9ce04d680efd3ecc, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x49a53a0c31d207a80c2079095835645344f838316e636a8aaeabd43754edf626, 0xf614d124698cbf302b12648f67e35b94ec9aae699ce2ac4ac30c2f97ae77b87b),
  (1, 0x7684c61da59f0fe2930db6a3ca287d40264e03477ef83d8f00444cce3d0a9490, 0x9abb42813cf5a6c3895e188e6f88e3fb1b0252a9522933efa0a862052b52435a),
  (1, 0x047bffd0e5dec41b22284243bd74d6439421f82331caa2ab1e3fe7f21f797d8c, 0x87ce2f8a06f747d4003311b4ab65f2b460dd06105f0ef62054a6ad6f8829c3d4),
  (0, 0x9c071dff3bf3b99e0115bb6b03cd10d03c66d5c419846605d1c9fe0c094df90a, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x0073b144be9ca33547c5024e2b48f1d0d01e8a32a4680094cb4e388a350f15cc, 0xea5c21296b269c7f78010ff702bac9e39084c3046566224647ee7ec45cd82673),
  (0, 0x5732107a973bb414651d1438e0bcfc9ef6e5f478c2867afd7e0a7c9288f79536, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x1f16a3c84b9282411b8e811a7cce72cfe968d1f1b92d684a8fb7d274a38530d9, 0x73542a52fad68cd34fc84a1c1ed2bcac6cff9ce801c0dd7cc63de1dd66c67afa),
  (0, 0xe40fffc9305a96c09e424d5085af7c67f4e7d7869677b7bd0a87aca7c96dabca, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x872d0466917c9f912f2300c1fc71036b03cc87b37254ccdb57aca31f3c2e4da9, 0x998171cbbf98c642cb1f5c2a3f60694f6779727d4546cbb4053aa70e7f6074ca),
  (0, 0x2fa2e6f886d4b979181be5adb130a17715b8c07ace29d4eb98f1cb2e7848af4c, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xe47dabbbeeb549be40deed072d89cee310e2af638303050b255a11a80e01bdfd, 0xcdaf9041f8677dd58b4c901692ddecd1fbd06cef1804c17c1715eabb687e6b17),
  (1, 0x50a221b2f178b80926755e83ed8b0e6aa965d6c9c2648bd7652d018a857abffa, 0x20b40cbe9c02da36ccf89eebbf40dc8b11816ab08dd182bd3e27829b36d2ce85),
  (1, 0x3f903a9623f3a297a25a97efae6b1f15f72d2d5190278885076b5ffb16a725b9, 0x2887892dfbe539056f57c113b65b33b535c84248680d0e7eb6796ae6a4f68e94),
  (0, 0x4def9248e6dff302f51cd7aac90def761ee0913e6e30a901726eee5d2af0bd08, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xd70ec55e56ad99e96e757647b163998380d2135314ec6ba5669654e2cb701c9a, 0x09b450142e057cc2ea1d6b61937cf4a584a2eafaa291c694b3c7bac795ef7ca9),
  (1, 0x26798f69c77aecbb9dc47679fa3a5a3b42048664b0936ed1f7d3ceaaa2aef5db, 0xc952d7109aad33a36e07a0e6bce7880afcfd78602a773b5787c582b3b65b09bb),
  (0, 0xe7d985dbf677a15ded43ff92e325f7a8728474d593951ab233daba58a0dfa191, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xcac8ee56873c714232599d2d5b3ccff13dc0eed19dc6ffe6958599909137da2e, 0x6026c28add89ad9101f0cd66ea6b5fe7cc27d7617d3c1e35937151a7e6c61230),
  (1, 0xc95db58f46986400260fb47138c8cc7e07cd67d2adb88e746a72d00c58deaebb, 0x20884e7355c4e996e10beeed18d0eb59a8ab9efe966fcbf59f6ce3634ccd7919),
  (1, 0x2a4bd615dcb92eab8749fca442567a011047d914ab262e9a230a75263a88abd2, 0x390922097e24cea7866575ce321f6a23d5bdb03a1fb0ad4ac7ba882037b8e613),
  (0, 0x88246dec0a2f5c1781c111b275131f55b126fd8e265fdde8ac3989cb1274622c, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x907e6ca0df806efa454760a45d6531e8911524be961db28481f68854ccaa76f4, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x0178d74f76eaa73bca5b6eb2002f00e70451125257f4bbb21afc676f885d66ae, 0x0597e6e102fb22978219b5924de46902f6abf9a6e5a04e65a4c56cae2bc05333),
  (1, 0x42344c89ce9fa6d61174787e0eba3437b9930069b36e38fa81717f029a015e00, 0xc83088e6b3791f3e7aa83a7d45619301350a1989d41646230416e778ab0950c4),
  (1, 0xa62fa653dd6625350083b4e38393ec4ba6d7f9d8d81c7769e8759cd0f41331af, 0x430666e4307db4c9024466cc9d9d6bb621b66e1c18c902e9d45a91b9b703b168),
  (0, 0xb7d7dfd2dd60ebc633df4932f165679c28f925b5ac1c11cae367c92589a57d92, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x75a74a2e990e1651dddec1e928034d4da24fb8884096c0933e6136f675561c39, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xac8358ff17e0d817bfeb4ef3654e06479b4046f4105d204bcdc996a0e620f8bd, 0x01af47f3c8bf1bc3299444ce6558889c8d92745da4d982d3a7efbf7fb5d46875),
  (1, 0x679cb473dc12a2918c3c3827168fd9e524ccf4f868b3fd2191d09eb1e500121a, 0x3792680c098ba165f0fefedd0b4db31ab7441fd42db2c5ad59800f83d7de3d26),
  (0, 0xdf411aa363e4786d551681a55d89e6d7ac119e4a3083e8c79c9a718d8619b3bd, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xea1b53c2aa6f71a051e448f87c88a9095ea873028a94bd4b2ee9af90bcb1eac4, 0x962cf5d9838fb9fc8dc74d7f74df049f7d85abfe39fc5339cec6714d59376a7a),
  (0, 0xede379c8816bce900ddeab2f33b9113929dfc9242b63cba9a67dc5f5be8bad6d, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x6321e085fdeb048016841b6a9ed4eabbc689e49d289e4aaab528e4ef1543312d, 0x3e1aad2501702f34893c4661ef8fd3dba7dd179e51396fc675d4b6dd99347fe4),
  (0, 0x39b0150b6e95f57baa07963f4bfa9ced1c26ecc4c51cd8aeb46e2cad878df313, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x2e0152ce0d9c1a5ddacf15a2f517b25627330c683614735674dcbed624e65ae0, 0x17f6a184c52be2960574258b00dc41b7d17945c0e4f265e240e90eef0b7b42f6),
  (1, 0x61ac483b86acef279cc960de2414b52d100d00429d1bef1596a5a1e1986ed89c, 0x462d7a741aaf1d2fdd617d6cd96e093046c39d7bf1b53ddef68827f59ed5e222),
  (1, 0x362429d6a8eb7152c8a25e4a154ab24d80b0401e5fe0a20c9a901fc4628f1cc1, 0x897c5346bbea118021d1db8ddeca17078d61494255d60d903501ab0d96dbdfc8),
  (1, 0x4a4306f1fe4fe56cf8390f421fab831d29aa38e749b6fbe2e1011e229d1c4dc0, 0xbd1ab3a4b261496084afd99fadfb56f19c896d5f05c139a72e1e1fcdbb07be70),
  (0, 0xfcf1523b82f29c2de448f6d989ac55b2df8473bf03b0568f47ba0ecb0bdd77af, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x0490c1ce453ca3fd42de1dd36b26e293a111b987c7deccac16fb161186ca125a, 0x3855482b858ff0489054da3a871a0829ec1abe06156a9c76d133a74243635ec5),
  (0, 0x2e293dde18e6e71e43395520c05773ea44bad530ab495d611458e2ef46a7707b, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xb06e1d39763a83a57fb67b677d4b44e12d71299c9b00785b1112809177da5c59, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xb4a04407ebd4b6a776a7bcf22e2391ef82fcb38caa323d9d88f6b064243137c6, 0x3744b45e624b5e48ff3377f3c07d5a48a62ed058e0e7960d23aeab1b85b0fbd3),
  (0, 0x4287ac902cd67c7e2ad5bf1085a4583c2156251d39355ae4d1eab8ae366e1da1, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xba3a1732d8f416c8d30c483abba55c6650234c26cc68ee2b4b5b9dbe94eac59a, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x37775d936f164f8a84a47a9fb920758d15245f8c54c93178d1c4b5cafe4aa748, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xa4a58801d8546d2f02a4050f921dab5916a5a5dd44176f76551f3edbafa49fab, 0x55a917ba6b5d45d33ea48131d175456e0b896ca85247cc49de12458f2b48d505),
  (0, 0x370e8f0214178e23448c3e2d2bf282e330be2f2967a412792452a0383df0b62f, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x50cf9a814a661783423db02e4a5e06e785ff9a267cc04fa814022a9de2273796, 0xbd812c5cc435aadb43c291fb04112777d6607f416d48ecca063d66c94d240d4e),
  (0, 0x15ed51763216385857d89c815309ebe43b35f69a834afdb5cb1b2cd34ffcf80a, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x9f0934630df8621d6a3c6c02ff916caccb0616bde61bfadbe8e0e5aed2afa375, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x7e719a2b2ba07ae6d322194e523da6eea7ede79a3be1ffb3fc12bdee43de1167, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x6041ba759eb9a87f0bf848fa65af818d3fcfffaa0c80943b90c7449163936b3e, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xa6a11f381b330e0eceead13193ca089f4cdce3ed7c19bb361cec09cf272e6dea, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xf46c2f33e3c1237340aa05dacbfd10f83f8c6aef5265ffc24313453af50d9f95, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xddae855b43b0804eef5626ba19b0872ade9f6db236626d5f6b712d8485de4f93, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xaa04eb321d85a9b24fb59178442a350eebd6e42eff6a4f491def6749dfde2371, 0xfd05caa0b09322293962fd72bda2746b5e446ee176ad48f275c84601549d0a70),
  (1, 0x6a8bd9dc42a657e933a8d775dabd30e245c28ab041084aea3e3b55e7ea2d42c1, 0xc4bfc90afac57bab865c528292620be06399835cf740234f93a38c08c4183d58),
  (1, 0x5662cb12d538dbfabb68ab6d4c22a1c04a1dc88f8fc4a4d327596eeaa32e1759, 0x4ea0daa54381eccfd69f5004b8e68145b23b787b79e16914301dbd648ef0140d),
  (0, 0x56f7b87bfab14a26476110ba5c5de226fba2bb55be1f980d57a59324e9450861, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xc2b84b6c7a201f0101162c4c3ee483b1fe5c431791db76941874b5ed2f7ee473, 0xa81fda848da8931d765c3e46d63d4ac5b8287b5c138d74ee6bf6b9ba2b4fc2c7),
  (1, 0x4da71139102cb68a454ec12917859e2992226a7bec363ed6234efd1d595644e6, 0xf729185a464fc7e3b694afe6c82a7b1619f198b8ee901a92472cede7ee9286ef),
  (1, 0x2c37d19c7cafccff4a1fae28df4e4a4e3d3a4fc9ae5f995d487c1f2447b64cc8, 0x50e04e127d5f199fb12b94118d5a1ac322cb3bdd23a79323113eae5d45368d76),
  (0, 0x146934b96538b882e2bac33d25141c7cb701e0a3380e3607d45278ae43bcfadd, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x2b7438e79a4f5a2430c8c84dd1f2fa7082d83b781514c1720c9f00cbed3b852f, 0xa032eb0660f3d2a6747dfec94e068b6787b6d2dd4450f2c669c86e2770df6400),
  (1, 0x4149f77950d05b8192def7b6eff59801d2a0566c9ba12cb48d1a7d1728e28953, 0xa59aa1b51f8e8da51bb8549d8fa642f24b9f7719a560ef6e35d38af4569e09db),
  (1, 0xac6752ce2f6319254eb10cb31a6bb274e610b39437e181f929be340d4c1f8c72, 0xa70d161b901af290724c7685d315050f176233c833142e9b7bdfc97473b1107f),
  (1, 0xec229f70507f0ca38f3f7af43488b62d19571c14a2449ee3b03d20f7eccced8f, 0x5373712ab93710af412c924beee6a4eb7ddf72eb877d13040c2778b10313078e),
  (1, 0x3e8fd2be29758dc10914ca0465b146ec7611762585f8ae1be6a962946c693815, 0xe247492b8e5866e6ee18fd530324052531ee190c1e06808627fab69d0c9d513c),
  (1, 0xe015f29fb3a42841b8433e747cb4e0022325624e5613671d29ede5030e5091cf, 0x634b7366c6e4bebd20c32ab165a2f4abb15ba0209b9ae7c45c2ad58ea9c77354),
  (1, 0x8a1f096fe8ba9a6ce81aaeec7537737c5b92eaa6051e1e4245c7fa742a924fb4, 0xef00db3e25dbe969ade09388984cc75fe0aa0e5fe7c00046fb16334da3cd2988),
  (1, 0x019b813c81558c2172c424ebebd74d5187c64a8870a3fa493196d20bd2985b56, 0xeac1563bcfd888de09fc7fcbe871bc562c4b70f1240a8846a900c66fbd2675ca),
  (0, 0x8474e018b6ac5b589f4749e1b38d6adc60a22c9eddd99afdd8e8d6044a4d4e98, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x8df6afc453659936eaa14ccfa4cbd75a49199a5a40838876176e6da39d169bc2, 0xff5caf8da8deb38d5833f1ef0047eaf5331a5e49802cb29843c99257ffab9b9e),
  (0, 0xd8d4c3fb404a84f9a0146faf112eb5f7b8482cd2d86a4736dfdb78f4bd319ba9, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x4026935e27333c9997ed5080700d1fe587b0a10e52f3668cb1ff2e53bef165a0, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xe91116989d2c29ba1c402a42220bb6afafd7a1d89c0f7cb6f1415f6b30d72782, 0xb9431bd34b02aced50f20c6257e46301867c5a638cdf4f97d6beaabeb0b9d37b),
  (0, 0x09b5ce7f66fb114a71e108c251df1485ab6f06b1e5babf4062feaeef8390f74b, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x39823a814982236ee6a11487982e893d758c2a2220c8b90ddb245fcf7db25e13, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x3724c9e4be4072950bfe2e6f6cc5d9a65ba15ecd671edff008bb8977b40d58e3, 0xf5f3756d498626e2c95941ce03d19247a0006ea31ba8a9c5708e9a6ed184b3a8),
  (0, 0xc693b7be868b7aafb474c7db3a3828e044558002902955a4dbc8591b409d3d1b, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x5b0807dfc13b599d28fc2aa490479cde20ec29a0f79d1fa41ba2d44364eb164d, 0xc4e0783865ffdb796c466718af80a7e0cb988f8f821b4d84e09287ee3f8f03f5),
  (1, 0x1b7ae9164f9be251eac12e6b7c1ba3e2ee99693aa9bc790e19af19181d90cd41, 0xcd2cac7dd8ccf1646e4a621d7a299a9e0f2fe2639638044e8577fa0f5d91f425),
  (1, 0x98455235999e1e64ebb7e53853d08ecc54f26431c221315dc79c2200f1b28e62, 0x352aa3669ea4a9afc9b01dbf934cf495b6147d51ebfd599bf2bc91057f6f6211),
  (1, 0x5ca4695b3a293d70d533ec2967309a049b77e935e713bf016bf8d3aa8e2e8691, 0x95fbbe8eda94faded0d0aea5cda033efc6d22a7200f904ca79fb75617324e8af),
  (0, 0x8e3fa477123b584f2d50b6f126ada57e27a8f2868ca91f8fd9ce85a1f920cf12, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x3b49c33d536bdb2e909079c762d2053f34997113063cf72adcab7d7ddec9faa9, 0x1f2ec02e6466b6d8c72f9d7f5d8ecd7033ab03d07baaaa43ce78c20480d033e3),
  (0, 0x62c33e0b9150e0608b29448fb56bcef22513931a622e8631b498ae54b22262a2, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x98706a34365fc35f0bf58006b8086053e00baca29dff996227401c8ccd9179d7, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x754e3f3b8b39783ae1d98f7bed4a33a9cb83a2dcf3dd96af1ed15030279b19e9, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x3c068fd60f94049af681c73e180ffcf374dc1a14a9af44c5f810584e384308e0, 0x8458ac5ebc5a27d0fb0bcad02e3c633a74b7b3f75d9026b0baee96d5a86e6447),
  (1, 0x43ad50f41bfa633e57f69e14ee4d5a7bbc3bf51c9146b7eb88fdb7222c3eb6f3, 0x6e7ac2b4002d16383bbb76e19c46d11e4943d406572749ca6437226f5ed5e0af),
  (0, 0x66b7745de248b97277a5615ff0bb462cf6e3c3e46ff057f7cce290d68ec3315a, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x68723255cb589f934be2b1545a295f0260eea2b5de3a4a9e94f804ebd5eb2ac4, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x75bce0217ca8b8c758150ce70761406c45bd0d802840e0d7d93d29a8a0b8b164, 0x003ef132cf7d12bdc105260187684881700060e59cdd9bfb36f8b013e06b3db0),
  (1, 0x5e17c94bd2c6d7b61037cf67c54c31856932b27be78c6d84d13c0df435b0e418, 0x11852c88e53cf13c381f4f44770421a8edeb1a2aa5ce0ab2a4bac0e9828dfd5e),
  (0, 0x69b6343cd46e3261cbfba536047eac826a6e5b069d0511ed854203a27dc2d6ad, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x1d3fe586613e4a9815c3ccdffefedf1f536fdfc332940ccc5ee0db4890ef4566, 0xe913bd3cc40444a7a62bd51a89b61dc8310e47f94c8f56737a7166af88bcf547),
  (0, 0xf839838e5ea18c0c3efc4d8a88787af906a6abca84884bcf498e6353b96e4ae4, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x2d5c87588d26f9c1cabb2ad6143c9145ca8a25067d0d0a1d1a941ac54f1e9ea8, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xc9633d6252ea9df0eda9df6c2913cead0ac51d4cd58e74f5da5e89ea5d228b0e, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xe271ab4ebd11fff0ec68a819b151c9ad16b2402b2fae6c2220fdd66672bd4063, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xd36996ae84fdc0707b26792cdfab4100a637ffa1177d4a6e9b004ce2e8e408ee, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x82f4035a2f943ba8d23b2fd98a9fa96b84620ffd6fb6ac5d80d2d89c955d0442, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xd9e9badf10498fba162eb6b719bde60c1168f5c29a9c252fc5359bc67bb0daab, 0xd58e4dbb39976789cac864c457839241a9600925ae5f118e90b5111e6ee5f145),
  (1, 0x67b0b964a2f26f16045e777230c8030b954ce902aad8a9d72f137f3ec973617f, 0x8030a1ab44fe730e18afc3f42dd9abe34c9266904e5b9faf883c32b833814b17),
  (0, 0x5bafce2495f2fa0e74c1c0d3eb547c30a3bdb10201f9724e370643cdd2e06c4d, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0xeaa21ee4d3193ebfd4ff0cd3a3850906f761b0696a90c5a245d1acae275021eb, 0x9848ac3b1358d674d92dec61ab818763f5e3f09c18e8545572f1dfaeb4154bca),
  (1, 0x4b2f02323795cceff4fae57277f199eaaf613c32c04e08d2ffa33e825dc160b1, 0x02597e05ab9ad7bab6c6042dc8b0a08020fc46a590057260d1343acbf9a9dc29),
  (0, 0x4dfeeeb6f36c1a9ca52e3abae72aff21f3f5cfc1f1763a5463cd3f9419518c9b, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x9054207d23fdd08ad96b38a135a128fb3ef816f72a9d5f1f52bdfd118ba86b4e, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x9cfcb3c3101bca8208a3879277013a90fde33d7e52688c097ada6a913a3e7f3b, 0xfab655ddb77e8b9989c2effc19e228c0c72121537ebd7ec3c6a7e4d048847d2b),
  (0, 0xafd086d090b268755bdf504137173c8ccc46493d1d4201e9916a757f7b00dc70, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xa5539e4c2a0cea6c4ede3f6173797a79cf2787f06f7e96e45e56c87a2e153893, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x18338c0dbb8c4b2cc1c0beac6fe6aba94372e897eff057934f4f1ab15a411201, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xfbd1ede4f87d76496c35e8768d3cc737302aacce3580b0b9925bbae37021f505, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xe87d436bed4bff39a438dbc5e0f2a0ab3c426665c18963a027a08bf1b5481af2, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x6ef473b5991356ad1b67f3fac06178cedf101127229b3473a62ebee5a858903e, 0xc9dec5ff3cfd2b46ca46f2e1e2462aaf8500d13eaedffa5622486431a4defc0e),
  (0, 0x98878284e0dad18c26ef85a11e64f28c050b597a75718c02f4b113be0d7f4566, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (1, 0x054872f7c6339d01480fd341fd5d2488dfd73172d95ed1155432e6e89d3398c0, 0xb652eafe317f809ebd0d0babb231eba646f4bf5b1c3e02f7e018073689be34d1),
  (0, 0xaeafae58242a90e531e26ad3754e9a553b88d37d07cae8e35fa4185aaeb6f158, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x9b3f6216667833ff2a4bbcd12ac27afe4a51a2d3b07eb0e78d312eca1f7159a1, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0xf6c614511660dd458e525fbfb354aeb10fcf1e624c2f26086ba3729f78386cc0, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x2fa523c29a33f7934f4e62b53aef395863ff174d933527da8937c26b6a5c9c60, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x60610490a84968ba2933cdf68cdfad9b184ba2853935fd774bef4e64377ba489, 0x0000000000000000000000000000000000000000000000000000000000000000),
  (0, 0x3b9e1fd3f452018f0e9c2ee69240a880ee147a50256c489c9338d92cacd255c2, 0x0000000000000000000000000000000000000000000000000000000000000000)
  ]

theorem hGon : OnCurve curve Gpt := by rw [onCurve_iff]; decide
theorem hPG : OnCurveOrInfinity curve (.affine Gpt) := hGon

theorem zsmul_order_lit :
    zsmul (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Int) (.affine Gpt) = .infinity := by
  have hchain := daChainOK hGon steps Gpt 1 (by rw [Nat.cast_one]; exact zsmul_one_affine _ hGon) (by decide)
  have hsc : ((daScalar steps 1 : Nat) : ℤ) = (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Int) - 1 := by
    rw [show daScalar steps 1 = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140 from by decide]; norm_num
  have hfold : steps.foldl (daStep Gpt.x) Gpt = (⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, 0xb7c52588d95c3b9aa25b0403f1eef75702e84bb7597aabe663b82f6f04ef2777⟩ : Point Fp) := by decide
  rw [hsc, hfold] at hchain
  rw [show (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : Int) = (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 - 1) + 1 by ring,
    zsmul_add hPG _ 1, hchain, zsmul_one_affine _ hGon]
  exact add_vertical 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 0xb7c52588d95c3b9aa25b0403f1eef75702e84bb7597aabe663b82f6f04ef2777 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 (by decide)

end Solution.Secp256k1ScalarMulFixedBase.OrderFactsChain

end DonorFile5_2

-- Adapted donor module: OrderFacts
section DonorFile5_3

namespace Solution.Secp256k1ScalarMulFixedBase.OrderFacts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw

theorem order_prime : Nat.Prime order :=
  OrderFactsCerts.prime_n

lemma hG : OnCurve curve G := by
  rw [onCurve_iff]; decide

lemma hGoc : OnCurveOrInfinity curve (.affine G) := hG

theorem zsmul_order_G : zsmul (order : ℤ) (.affine G) = .infinity := by
  have h : ((order : ℕ) : ℤ)
      = (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 : ℤ) := by
    norm_num [order]
  rw [h]
  exact OrderFactsChain.zsmul_order_lit

noncomputable section

private def g : WeierstrassCurve.Affine.Point W := toW (.affine G) hGoc

private lemma zsmul_G_eq (m : ℤ) : zsmul m (.affine G) = fromW (m • g) :=
  zsmul_eq hGoc m

private lemma g_ne_zero : g ≠ 0 := by
  intro h
  have h2 : fromW g = fromW 0 := congrArg fromW h
  rw [g, fromW_toW, fromW_zero] at h2
  exact absurd h2 (by simp)

private lemma order_nsmul_g : order • g = 0 := by
  have h1 := zsmul_order_G
  rw [zsmul_G_eq, fromW_eq_infinity_iff, natCast_zsmul] at h1
  exact h1

private lemma addOrderOf_g : addOrderOf g = order := by
  have hdvd : addOrderOf g ∣ order :=
    addOrderOf_dvd_of_nsmul_eq_zero order_nsmul_g
  rcases (Nat.Prime.eq_one_or_self_of_dvd order_prime _ hdvd) with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) g_ne_zero
  · exact h

theorem zsmul_eq_infinity_iff (m : ℤ) :
    zsmul m (.affine G) = .infinity ↔ ((order : ℕ) : ℤ) ∣ m := by
  rw [zsmul_G_eq, fromW_eq_infinity_iff, ← addOrderOf_dvd_iff_zsmul_eq_zero,
    addOrderOf_g]

theorem zsmul_ne_infinity (m : ℤ) (h0 : m ≠ 0) (hlt : |m| < ((order : ℕ) : ℤ)) :
    zsmul m (.affine G) ≠ .infinity := by
  intro hinf
  rw [zsmul_eq_infinity_iff] at hinf
  have hdvd := hinf
  have hle : ((order : ℕ) : ℤ) ≤ |m| :=
    Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr hdvd)
  omega

private lemma fromW_inj {p q : WeierstrassCurve.Affine.Point W}
    (h : fromW p = fromW q) : p = q := by
  have h2 := toW_congr (fromW_onCurve p) (fromW_onCurve q) h
  rwa [toW_fromW, toW_fromW] at h2

theorem zsmul_inj (a b : ℤ) (hne : a ≠ b) (hlt : |a - b| < ((order : ℕ) : ℤ)) :
    zsmul a (.affine G) ≠ zsmul b (.affine G) := by
  intro h
  have h1 : a • g = b • g := by
    apply fromW_inj
    rw [← zsmul_G_eq, ← zsmul_G_eq]
    exact h
  have h2 : (a - b) • g = 0 := by
    rw [sub_zsmul, h1]
    exact add_neg_cancel _
  apply zsmul_ne_infinity (a - b) (sub_ne_zero.mpr hne) hlt
  rw [zsmul_G_eq, h2]
  exact fromW_zero

theorem zsmul_ne_neg (a b : ℤ) (hne : a + b ≠ 0)
    (hlt : |a + b| < ((order : ℕ) : ℤ)) :
    zsmul a (.affine G) ≠ specNeg (zsmul b (.affine G)) := by
  have hneg : specNeg (zsmul b (.affine G)) = zsmul (-b) (.affine G) := by
    rw [zsmul_G_eq b, ← fromW_neg, ← neg_zsmul, ← zsmul_G_eq]
  rw [hneg]
  apply zsmul_inj
  · omega
  · rw [sub_neg_eq_add]; exact hlt

end

theorem x_ne_of_ne {P Q : Point Fp} (hP : OnCurve curve P) (hQ : OnCurve curve Q)
    (h1 : GroupPoint.affine P ≠ .affine Q)
    (h2 : GroupPoint.affine P ≠ specNeg (.affine Q)) :
    P.x ≠ Q.x := by
  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩
  intro hx
  dsimp at hx
  subst hx
  rw [onCurve_iff] at hP hQ
  have hy2 : (py - qy) * (py + qy) = 0 := by linear_combination hP - hQ
  rcases mul_eq_zero.mp hy2 with h | h
  · exact h1 (by rw [sub_eq_zero.mp h])
  · apply h2
    show GroupPoint.affine ⟨px, py⟩ = .affine ⟨px, -qy⟩
    rw [eq_neg_of_add_eq_zero_left h]

end Solution.Secp256k1ScalarMulFixedBase.OrderFacts

end DonorFile5_3

-- Adapted donor module: TableCerts
section DonorFile5_4

set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.TableCerts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Tables

theorem hGon : OnCurve curve Tables.Gpt := by rw [onCurve_iff]; decide

theorem dblAll : ∀ k, k ≤ Tables.dblSlopes.length →
    zsmul ((2 : ℤ) ^ k) (.affine Tables.Gpt) = .affine (dnth Tables.Gpt Tables.dblSlopes k) := by
  intro k hk
  have h := dblChainOK hGon Tables.dblSlopes Tables.Gpt 1
    (by rw [zsmul_one_affine _ hGon]) (by decide) k hk
  simpa using h


theorem tbl_28 : ∀ j : Fin 8,
    zsmul ((2 * j.val + 1) * 2 ^ (9 * 28)) (.affine (⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8⟩ : Point Fp))
      = .affine ⟨((Tables.magXNat (28 * 256 + j.val) : ℕ) : Fp),
                 ((Tables.magYNat (28 * 256 + j.val) : ℕ) : Fp)⟩ := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  intro j
  have hB : zsmul ((2 : ℤ) ^ (9 * 28)) (.affine Tables.Gpt) = .affine (Tables.basePt 28) := by
    have := dblAll (9 * 28) (by decide); simpa [Tables.basePt] using this
  have hS : zsmul ((2 : ℤ) ^ (9 * 28 + 1)) (.affine Tables.Gpt) = .affine (Tables.stepPt 28) := by
    have := dblAll (9 * 28 + 1) (by decide); simpa [Tables.stepPt] using this
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (9 * 28 + 1))
    (by rw [hS]) (Tables.wslopes 28) (Tables.basePt 28) ((2 : ℤ) ^ (9 * 28))
    (by rw [hB]) (by decide) j.val
    (by rw [show (Tables.wslopes 28).length = 7 from by decide]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (9 * 28) : ℤ)
        = (2 : ℤ) ^ (9 * 28) + (j.val : ℤ) * 2 ^ (9 * 28 + 1) by rw [pow_succ]; push_cast; ring]
  have hx : (((Tables.magXNat (28 * 256 + j.val) : ℕ)) : Fp) = (Tables.magPt 28 j.val).x := by
    rw [Tables.magXNat, show (28 * 256 + j.val) / 256 = 28 from by omega,
      show (28 * 256 + j.val) % 256 = j.val from by omega, ZMod.natCast_val, ZMod.cast_id]
  have hy : (((Tables.magYNat (28 * 256 + j.val) : ℕ)) : Fp) = (Tables.magPt 28 j.val).y := by
    rw [Tables.magYNat, show (28 * 256 + j.val) / 256 = 28 from by omega,
      show (28 * 256 + j.val) % 256 = j.val from by omega, ZMod.natCast_val, ZMod.cast_id]
  rw [hx, hy]
  show _ = GroupPoint.affine (Tables.magPt 28 j.val)
  rw [Tables.magPt]
  exact hchain


theorem posY_28 : ∀ j : Fin 8, (Tables.magPt 28 j.val).y ≠ 0 := by
  intro j
  have h := cnth_y_ne_zero (Tables.stepPt 28).x (Tables.wslopes 28) (Tables.basePt 28)
    (by decide) j.val
    (by rw [show (Tables.wslopes 28).length = 7 from by decide]; exact Nat.lt_succ_iff.mp j.isLt)
  simpa [Tables.magPt] using h.1


theorem magY_ne_zero_top : ∀ j : Fin 8, (Tables.magPt 28 j.val).y ≠ 0 := posY_28


theorem tableCertTop : ∀ j : Fin 8,
    zsmul ((2 * j.val + 1) * 2 ^ (9 * 28)) (.affine (⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8⟩ : Point Fp))
      = .affine ⟨((Tables.magXNat (28 * 256 + j.val) : ℕ) : Fp),
                 ((Tables.magYNat (28 * 256 + j.val) : ℕ) : Fp)⟩ := tbl_28

end Solution.Secp256k1ScalarMulFixedBase.TableCerts

end DonorFile5_4

-- Adapted donor module: EvenTableTop
section DonorFile5_5

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.EvenTableTop

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Tables
open Solution.Secp256k1ScalarMulFixedBase.TableCerts

-- even-parity top-window (4-bit) table constants, generated and validated by
-- scratchpad/gen_eventabletop.py: entry v = (2v - 15) * 2^252 * G - G.
def AptTop : Point Fp := ⟨0x3bc6bc6446bf520136358eb0958dc4aa9e733164dd2d62e151f946107427bacc, 0x8e305cc07176c305cdb62ee226d6c02bd71b75a5228beb4714c33fd5ead6fda6⟩
def BptTop : Point Fp := ⟨0xfaa3ff70e0fc1e589f54f34d328cfec8551058f09fcfb501c1282ee3225ba280, 0xf61613166b3bb1c10674f03eab0fd6e625f5f9551342190a62b3c841e8f6b757⟩
def sAGTop : Fp := 0xd3ab2a76d8914c4f89de357ee26c9005876e62af82a8c939f3cd6f9541834bec
def evenBaseTop : Point Fp := ⟨0xfaa3ff70e0fc1e589f54f34d328cfec8551058f09fcfb501c1282ee3225ba280, 0x09e9ece994c44e3ef98b0fc154f02919da0a06aaecbde6f59d4c37bd170944d8⟩
def evenSlopesTop : List Fp := [
  0xc1013bb5d64a425ae3b6f2739e0eb110348908228c4c7f1b2a6219a8203a2936,
  0x51d7c44c0bd8fbfc4eadd4d8ff9c3cb58b9806dbf43af279e79cc48b08aa8920,
  0x0e55572709d6a875aa2ee74dd0d7c73b14ffbd86deb714a73bc416814ba2ddf6,
  0xa269210ff4643def2700e9831bcd3a99fa68173589f6c87af6a1aeff3218fe81,
  0x71d98d785e7cb109ee4d78f34072c9a7a11d822c1d02ef6295856607c662279a,
  0x245ad015ca81be1f277a4b3d4c2aca8b2e74128b6223fda74fc3cbdd23299c44,
  0x7374fa4cd381eeaecdcfc8210afaf282047066c85454eb08fcd4dc24aa61564a,
  0xfdb461b2b8e763b3bd84f2c2aa04dd69de8b13d4bcad8fc21fad8611d4709074,
  0xe544b63fe18cba4a46f46951031866406e6364b68f5bf49ce3e32e861091ea29,
  0x47e3a349356abbafa0a7582ca5bcc0e196f4284a2861f03224c737319923cf31,
  0x37321f06198f88fd459bc43728052b570580f587a635b7fed48b38eb4f2fab6b,
  0xfb1e97d61061b7178a75a81650af7ee46643e682f7025d52dccd36dfeb17648b,
  0xf147c60dd2aed64a754d59c7a90ba763b995d562dfd83182b11865f63d8b3d13,
  0x13c4c95b77437a0301d9d8b2254e1e93863f5908ee23a9a39625d50bd8b75aba,
  0x44dd2f0abc8d68da87c56fc4e8867c646fd9906d834462ff406946f602bf133f
]

/-- The even-parity top-window table entry for window value `v`. -/
def evenPtTop (v : ℕ) : Point Fp := cnth (Tables.stepPt 28).x evenBaseTop evenSlopesTop v

def evenXNatTop (v : ℕ) : ℕ := (evenPtTop v).x.val

def evenYNatTop (v : ℕ) : ℕ := (evenPtTop v).y.val

theorem evenSlopesTop_length : evenSlopesTop.length = 15 := by decide

/-- Base certificate: `[(-15)*2^252 - 1]G = evenBaseTop`. -/
theorem evenBaseTop_cert :
    zsmul ((-15) * 2 ^ 252 - 1 : ℤ) (.affine Tables.Gpt) = .affine evenBaseTop := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  have hGI : OnCurveOrInfinity curve (.affine Tables.Gpt) := hGon
  have zneg : ∀ (n : ℤ),
      zsmul (-n) (.affine Tables.Gpt) = specNeg (zsmul n (.affine Tables.Gpt)) :=
    fun n => by rw [zsmul_eq hGI (-n), zsmul_eq hGI n, neg_zsmul, fromW_neg]
  -- A = [15*2^252]G, from tbl_28 with j = 7.
  have hA : zsmul ((2 * 7 + 1) * 2 ^ (9 * 28) : ℤ) (.affine Tables.Gpt) = .affine AptTop := by
    have h := TableCerts.tbl_28 ⟨7, by decide⟩
    refine h.trans ?_
    decide
  have h1 : zsmul (1 : ℤ) (.affine Tables.Gpt) = .affine Tables.Gpt :=
    zsmul_one_affine Tables.Gpt hGon
  -- B = A + G = [15*2^252 + 1]G, via the chord addition.
  have hB : zsmul ((2 * 7 + 1) * 2 ^ (9 * 28) + 1 : ℤ) (.affine Tables.Gpt) = .affine BptTop := by
    rw [zsmul_add hGI ((2 * 7 + 1) * 2 ^ (9 * 28)) 1, hA, h1]
    exact add_chord AptTop.x AptTop.y Tables.Gpt.x Tables.Gpt.y sAGTop BptTop.x BptTop.y
      (by decide) (by decide) (by decide) (by decide)
  -- Negate: [-(15*2^252 + 1)]G = specNeg B = evenBaseTop.
  rw [show ((-15) * 2 ^ 252 - 1 : ℤ) = -((2 * 7 + 1) * 2 ^ (9 * 28) + 1) by norm_num]
  rw [zneg, hB]
  decide

/-- Chain certificate: for every window value `v`,
`[(2v + 1 - 16)*2^252 - 1]G = evenPtTop v`. -/
theorem evenTblTop : ∀ v : Fin 16,
    zsmul (((2 * (v : ℤ) + 1 - 16) * 2 ^ 252) - 1) (.affine Tables.Gpt)
      = .affine ⟨((evenXNatTop v.val : ℕ) : Fp), ((evenYNatTop v.val : ℕ) : Fp)⟩ := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  intro v
  have hStep : zsmul ((2 : ℤ) ^ (9 * 28 + 1)) (.affine Tables.Gpt)
      = .affine (Tables.stepPt 28) := by
    have := TableCerts.dblAll (9 * 28 + 1) (by decide); simpa [Tables.stepPt] using this
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (9 * 28 + 1))
    (by rw [hStep]) evenSlopesTop evenBaseTop ((-15) * 2 ^ 252 - 1)
    evenBaseTop_cert (by decide) v.val
    (by rw [evenSlopesTop_length]; exact Nat.lt_succ_iff.mp v.isLt)
  rw [show (((2 * (v : ℤ) + 1 - 16) * 2 ^ 252) - 1)
        = ((-15) * 2 ^ 252 - 1) + (v.val : ℤ) * 2 ^ (9 * 28 + 1) by
      have hpow : (2 : ℤ) ^ (9 * 28 + 1) = 2 * 2 ^ 252 := by norm_num [pow_succ]
      rw [hpow]; push_cast; ring]
  have hx : (((evenXNatTop v.val : ℕ)) : Fp) = (evenPtTop v.val).x := by
    rw [evenXNatTop, ZMod.natCast_val, ZMod.cast_id]
  have hy : (((evenYNatTop v.val : ℕ)) : Fp) = (evenPtTop v.val).y := by
    rw [evenYNatTop, ZMod.natCast_val, ZMod.cast_id]
  rw [hx, hy]
  show _ = GroupPoint.affine (evenPtTop v.val)
  exact hchain

/-- Each entry has nonzero `y`, bounded by the field modulus. -/
theorem evenYTop_ne_zero : ∀ v : Fin 16, evenYNatTop v.val ≠ 0 ∧ evenYNatTop v.val < P256 := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  intro v
  refine ⟨?_, ?_⟩
  · have h := cnth_y_ne_zero (Tables.stepPt 28).x evenSlopesTop evenBaseTop
      (by decide) v.val (by rw [evenSlopesTop_length]; exact Nat.lt_succ_iff.mp v.isLt)
    simp only [evenYNatTop, evenPtTop]
    intro hz
    exact h.1 ((ZMod.val_eq_zero _).mp hz)
  · simp only [evenYNatTop]
    exact ZMod.val_lt _

/-- Each entry's `x` is bounded by the field modulus. -/
theorem evenXTop_lt : ∀ v : Fin 16, evenXNatTop v.val < P256 := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  intro v
  simp only [evenXNatTop]
  exact ZMod.val_lt _

end Solution.Secp256k1ScalarMulFixedBase.EvenTableTop



set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.TableReflect

abbrev Gpt := Solution.Secp256k1ScalarMulFixedBase.Tables.Gpt

def magnitudes : ℕ := 2048
def width : ℕ := 12

def basePt (i : ℕ) : Point Fp :=
  dnth Gpt Solution.Secp256k1ScalarMulFixedBase.Tables.dblSlopes (12 * i)

def stepPt (i : ℕ) : Point Fp :=
  dnth Gpt Solution.Secp256k1ScalarMulFixedBase.Tables.dblSlopes (12 * i + 1)

def magPt (win j : ℕ) : Point Fp :=
  cnth (stepPt win).x (basePt win) (TableData.slopes win) j

def magXNat (idx : ℕ) : ℕ := (magPt (idx / magnitudes) (idx % magnitudes)).x.val
def magYNat (idx : ℕ) : ℕ := (magPt (idx / magnitudes) (idx % magnitudes)).y.val

def magXConst (idx : ℕ) : Var Emu (F circomPrime) := emuConst (magXNat idx)
def magYConst (idx : ℕ) : Var Emu (F circomPrime) := emuConst (magYNat idx)

/-- The odd width-4 top table is exactly the accepted table at offset 252. -/
lemma regular_flat_div (win j : ℕ) (hj : j < magnitudes) :
    (win * magnitudes + j) / magnitudes = win := by
  simp only [magnitudes] at hj ⊢
  omega

lemma regular_flat_mod (win j : ℕ) (hj : j < magnitudes) :
    (win * magnitudes + j) % magnitudes = j := by
  simp only [magnitudes] at hj ⊢
  omega

end Solution.Secp256k1ScalarMulFixedBase.Width12.Tables



set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.TableCerts

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.GroupLaw
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.OrderFacts
open Solution.Secp256k1ScalarMulFixedBase.Width12.Tables

theorem hGon : OnCurve curve Gpt := Solution.Secp256k1ScalarMulFixedBase.TableCerts.hGon

theorem dblAll : ∀ k, k ≤ Solution.Secp256k1ScalarMulFixedBase.Tables.dblSlopes.length →
    zsmul ((2 : ℤ) ^ k) (.affine Gpt) =
      .affine (dnth Gpt Solution.Secp256k1ScalarMulFixedBase.Tables.dblSlopes k) :=
  Solution.Secp256k1ScalarMulFixedBase.TableCerts.dblAll

theorem checks_0 :
    cchecks (stepPt 0).x (stepPt 0).y (basePt 0) TableData.slopes_0 = true ∧
      allYne0 (stepPt 0).x (basePt 0) TableData.slopes_0 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_1 :
    cchecks (stepPt 1).x (stepPt 1).y (basePt 1) TableData.slopes_1 = true ∧
      allYne0 (stepPt 1).x (basePt 1) TableData.slopes_1 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_2 :
    cchecks (stepPt 2).x (stepPt 2).y (basePt 2) TableData.slopes_2 = true ∧
      allYne0 (stepPt 2).x (basePt 2) TableData.slopes_2 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_3 :
    cchecks (stepPt 3).x (stepPt 3).y (basePt 3) TableData.slopes_3 = true ∧
      allYne0 (stepPt 3).x (basePt 3) TableData.slopes_3 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_4 :
    cchecks (stepPt 4).x (stepPt 4).y (basePt 4) TableData.slopes_4 = true ∧
      allYne0 (stepPt 4).x (basePt 4) TableData.slopes_4 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_5 :
    cchecks (stepPt 5).x (stepPt 5).y (basePt 5) TableData.slopes_5 = true ∧
      allYne0 (stepPt 5).x (basePt 5) TableData.slopes_5 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_6 :
    cchecks (stepPt 6).x (stepPt 6).y (basePt 6) TableData.slopes_6 = true ∧
      allYne0 (stepPt 6).x (basePt 6) TableData.slopes_6 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem checks_7 :
    cchecks (stepPt 7).x (stepPt 7).y (basePt 7) TableData.slopes_7 = true ∧
      allYne0 (stepPt 7).x (basePt 7) TableData.slopes_7 = true :=
  cchecksY_elim _ _ _ _ (by decide)

theorem slopes_0_length : TableData.slopes_0.length = 2047 := by decide
theorem tbl_0 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 0)) (.affine Gpt) =
      .affine (magPt 0 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 0)) (.affine Gpt) = .affine (basePt 0) := by
    have h := dblAll (12 * 0) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 0 + 1)) (.affine Gpt) = .affine (stepPt 0) := by
    have h := dblAll (12 * 0 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 0 + 1))
    (by rw [hS]) TableData.slopes_0 (basePt 0) ((2 : ℤ) ^ (12 * 0))
    (by rw [hB]) checks_0.1 j.val
    (by rw [slopes_0_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 0) : ℤ) =
      (2 : ℤ) ^ (12 * 0) + (j.val : ℤ) * 2 ^ (12 * 0 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_1_length : TableData.slopes_1.length = 2047 := by decide
theorem tbl_1 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 1)) (.affine Gpt) =
      .affine (magPt 1 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 1)) (.affine Gpt) = .affine (basePt 1) := by
    have h := dblAll (12 * 1) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 1 + 1)) (.affine Gpt) = .affine (stepPt 1) := by
    have h := dblAll (12 * 1 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 1 + 1))
    (by rw [hS]) TableData.slopes_1 (basePt 1) ((2 : ℤ) ^ (12 * 1))
    (by rw [hB]) checks_1.1 j.val
    (by rw [slopes_1_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 1) : ℤ) =
      (2 : ℤ) ^ (12 * 1) + (j.val : ℤ) * 2 ^ (12 * 1 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_2_length : TableData.slopes_2.length = 2047 := by decide
theorem tbl_2 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 2)) (.affine Gpt) =
      .affine (magPt 2 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 2)) (.affine Gpt) = .affine (basePt 2) := by
    have h := dblAll (12 * 2) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 2 + 1)) (.affine Gpt) = .affine (stepPt 2) := by
    have h := dblAll (12 * 2 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 2 + 1))
    (by rw [hS]) TableData.slopes_2 (basePt 2) ((2 : ℤ) ^ (12 * 2))
    (by rw [hB]) checks_2.1 j.val
    (by rw [slopes_2_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 2) : ℤ) =
      (2 : ℤ) ^ (12 * 2) + (j.val : ℤ) * 2 ^ (12 * 2 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_3_length : TableData.slopes_3.length = 2047 := by decide
theorem tbl_3 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 3)) (.affine Gpt) =
      .affine (magPt 3 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 3)) (.affine Gpt) = .affine (basePt 3) := by
    have h := dblAll (12 * 3) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 3 + 1)) (.affine Gpt) = .affine (stepPt 3) := by
    have h := dblAll (12 * 3 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 3 + 1))
    (by rw [hS]) TableData.slopes_3 (basePt 3) ((2 : ℤ) ^ (12 * 3))
    (by rw [hB]) checks_3.1 j.val
    (by rw [slopes_3_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 3) : ℤ) =
      (2 : ℤ) ^ (12 * 3) + (j.val : ℤ) * 2 ^ (12 * 3 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_4_length : TableData.slopes_4.length = 2047 := by decide
theorem tbl_4 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 4)) (.affine Gpt) =
      .affine (magPt 4 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 4)) (.affine Gpt) = .affine (basePt 4) := by
    have h := dblAll (12 * 4) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 4 + 1)) (.affine Gpt) = .affine (stepPt 4) := by
    have h := dblAll (12 * 4 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 4 + 1))
    (by rw [hS]) TableData.slopes_4 (basePt 4) ((2 : ℤ) ^ (12 * 4))
    (by rw [hB]) checks_4.1 j.val
    (by rw [slopes_4_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 4) : ℤ) =
      (2 : ℤ) ^ (12 * 4) + (j.val : ℤ) * 2 ^ (12 * 4 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_5_length : TableData.slopes_5.length = 2047 := by decide
theorem tbl_5 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 5)) (.affine Gpt) =
      .affine (magPt 5 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 5)) (.affine Gpt) = .affine (basePt 5) := by
    have h := dblAll (12 * 5) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 5 + 1)) (.affine Gpt) = .affine (stepPt 5) := by
    have h := dblAll (12 * 5 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 5 + 1))
    (by rw [hS]) TableData.slopes_5 (basePt 5) ((2 : ℤ) ^ (12 * 5))
    (by rw [hB]) checks_5.1 j.val
    (by rw [slopes_5_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 5) : ℤ) =
      (2 : ℤ) ^ (12 * 5) + (j.val : ℤ) * 2 ^ (12 * 5 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_6_length : TableData.slopes_6.length = 2047 := by decide
theorem tbl_6 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 6)) (.affine Gpt) =
      .affine (magPt 6 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 6)) (.affine Gpt) = .affine (basePt 6) := by
    have h := dblAll (12 * 6) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 6 + 1)) (.affine Gpt) = .affine (stepPt 6) := by
    have h := dblAll (12 * 6 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 6 + 1))
    (by rw [hS]) TableData.slopes_6 (basePt 6) ((2 : ℤ) ^ (12 * 6))
    (by rw [hB]) checks_6.1 j.val
    (by rw [slopes_6_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 6) : ℤ) =
      (2 : ℤ) ^ (12 * 6) + (j.val : ℤ) * 2 ^ (12 * 6 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem slopes_7_length : TableData.slopes_7.length = 2047 := by decide
theorem tbl_7 : ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * 7)) (.affine Gpt) =
      .affine (magPt 7 j.val) := by
  intro j
  have hB : zsmul ((2 : ℤ) ^ (12 * 7)) (.affine Gpt) = .affine (basePt 7) := by
    have h := dblAll (12 * 7) (by decide); simpa [basePt] using h
  have hS : zsmul ((2 : ℤ) ^ (12 * 7 + 1)) (.affine Gpt) = .affine (stepPt 7) := by
    have h := dblAll (12 * 7 + 1) (by decide); simpa [stepPt] using h
  have hchain := chordChainOK hGon (q := (2 : ℤ) ^ (12 * 7 + 1))
    (by rw [hS]) TableData.slopes_7 (basePt 7) ((2 : ℤ) ^ (12 * 7))
    (by rw [hB]) checks_7.1 j.val
    (by rw [slopes_7_length]; exact Nat.lt_succ_iff.mp j.isLt)
  rw [show ((2 * j.val + 1) * 2 ^ (12 * 7) : ℤ) =
      (2 : ℤ) ^ (12 * 7) + (j.val : ℤ) * 2 ^ (12 * 7 + 1) by
        rw [pow_succ]; push_cast; ring]
  simpa [magPt, TableData.slopes] using hchain

theorem tableCert : ∀ win : Fin 8, ∀ j : Fin 2048,
    zsmul ((2 * j.val + 1) * 2 ^ (12 * win.val)) (.affine Gpt) =
      .affine (magPt win.val j.val) := by
  intro win
  match win with
  | ⟨0, _⟩ => exact tbl_0
  | ⟨1, _⟩ => exact tbl_1
  | ⟨2, _⟩ => exact tbl_2
  | ⟨3, _⟩ => exact tbl_3
  | ⟨4, _⟩ => exact tbl_4
  | ⟨5, _⟩ => exact tbl_5
  | ⟨6, _⟩ => exact tbl_6
  | ⟨7, _⟩ => exact tbl_7
  | ⟨n + 8, h⟩ => exact absurd h (by omega)

theorem tableOnCurve (win : Fin 8) (j : Fin 2048) :
    OnCurve curve (magPt win.val j.val) := by
  have h := zsmul_onCurveOrInfinity (P := .affine Gpt) hGon
    ((2 * j.val + 1) * 2 ^ (12 * win.val) : ℤ)
  rw [tableCert win j] at h
  exact h

theorem coordinates_lt (win : Fin 8) (j : Fin 2048) :
    magXNat (win.val * magnitudes + j.val) < P256 ∧
      magYNat (win.val * magnitudes + j.val) < P256 := by
  haveI : NeZero p := ⟨hPrime.ne_zero⟩
  exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩

theorem lookup_semantics (win : Fin 8) (j : Fin 2048) :
    (((magXNat (win.val * magnitudes + j.val) : ℕ) : Fp),
      ((magYNat (win.val * magnitudes + j.val) : ℕ) : Fp)) =
      ((magPt win.val j.val).x, (magPt win.val j.val).y) := by
  simp [magXNat, magYNat, regular_flat_div win.val j.val j.isLt,
    regular_flat_mod win.val j.val j.isLt]


end Solution.Secp256k1ScalarMulFixedBase.Width12.TableCerts



set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

namespace Solution.Secp256k1ScalarMulFixedBase.Width12.TableYNonzero

open Specs.ShortWeierstrass Specs.Secp256k1
open Solution.Secp256k1ScalarMulFixedBase.TableReflect
open Solution.Secp256k1ScalarMulFixedBase.Width12.Tables
open Solution.Secp256k1ScalarMulFixedBase.Width12.TableCerts

theorem posY_0 : ∀ j : Fin 2048, (magPt 0 j.val).y ≠ 0 ∧
    (magPt 0 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 0).x TableData.slopes_0 (basePt 0)
    checks_0.2 j.val
    (by rw [show TableData.slopes_0.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_1 : ∀ j : Fin 2048, (magPt 1 j.val).y ≠ 0 ∧
    (magPt 1 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 1).x TableData.slopes_1 (basePt 1)
    checks_1.2 j.val
    (by rw [show TableData.slopes_1.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_2 : ∀ j : Fin 2048, (magPt 2 j.val).y ≠ 0 ∧
    (magPt 2 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 2).x TableData.slopes_2 (basePt 2)
    checks_2.2 j.val
    (by rw [show TableData.slopes_2.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_3 : ∀ j : Fin 2048, (magPt 3 j.val).y ≠ 0 ∧
    (magPt 3 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 3).x TableData.slopes_3 (basePt 3)
    checks_3.2 j.val
    (by rw [show TableData.slopes_3.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_4 : ∀ j : Fin 2048, (magPt 4 j.val).y ≠ 0 ∧
    (magPt 4 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 4).x TableData.slopes_4 (basePt 4)
    checks_4.2 j.val
    (by rw [show TableData.slopes_4.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_5 : ∀ j : Fin 2048, (magPt 5 j.val).y ≠ 0 ∧
    (magPt 5 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 5).x TableData.slopes_5 (basePt 5)
    checks_5.2 j.val
    (by rw [show TableData.slopes_5.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_6 : ∀ j : Fin 2048, (magPt 6 j.val).y ≠ 0 ∧
    (magPt 6 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 6).x TableData.slopes_6 (basePt 6)
    checks_6.2 j.val
    (by rw [show TableData.slopes_6.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem posY_7 : ∀ j : Fin 2048, (magPt 7 j.val).y ≠ 0 ∧
    (magPt 7 j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro j
  have h := cnth_y_ne_zero (stepPt 7).x TableData.slopes_7 (basePt 7)
    checks_7.2 j.val
    (by rw [show TableData.slopes_7.length = 2047 from by decide]
        exact Nat.lt_succ_iff.mp j.isLt)
  simpa [magPt, TableData.slopes] using h

theorem magYOK : ∀ win : Fin 8, ∀ j : Fin 2048,
    (magPt win.val j.val).y ≠ 0 ∧
      (magPt win.val j.val).y.val % 18446744073709551616 ≤ lowP := by
  intro win
  match win with
  | ⟨0, _⟩ => exact posY_0
  | ⟨1, _⟩ => exact posY_1
  | ⟨2, _⟩ => exact posY_2
  | ⟨3, _⟩ => exact posY_3
  | ⟨4, _⟩ => exact posY_4
  | ⟨5, _⟩ => exact posY_5
  | ⟨6, _⟩ => exact posY_6
  | ⟨7, _⟩ => exact posY_7
  | ⟨n + 8, h⟩ => exact absurd h (by omega)

theorem magY_ne_zero : ∀ win : Fin 8, ∀ j : Fin 2048,
    (magPt win.val j.val).y ≠ 0 := fun win j => (magYOK win j).1

/-- The low 64-bit limb of every width-12 table `y` is at most the low limb of
the prime, so the schoolbook subtraction `P256 - y` never borrows. -/
theorem magY_low : ∀ win : Fin 8, ∀ j : Fin 2048,
    (magPt win.val j.val).y.val % 18446744073709551616 ≤ lowP :=
  fun win j => (magYOK win j).2

end Solution.Secp256k1ScalarMulFixedBase.Width12.TableYNonzero

end DonorFile5_5

-- Adapted donor module: SelectTop
section DonorFile5_6

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

/-- Top-window select: 4-bit signed odd digit (3 magnitude bits + sign `b[3]`),
8 magnitudes, one-hot over 7 witnessed cells plus the affine default. Mirrors
the 9-bit `Select`'s structure at the small width; the window index is fixed
at 28 (magnitude table rows `28 * 256 + j`, `j < 8`).

In the fixed-base comb the top-window sign bit `b[3]` is the compile-time
constant `1` (it is `derivedDigits …[255] = 1`), so the caller supplies the
extra assumption `b[3] = 1`.  Both output coordinates are therefore emitted as
degree-one one-hot combinations of the witnessed cells `e`, with no further
witnesses: `x` via `xSelExpr`, `y` via `ySelExpr`. -/

def sigXNat (v : ℕ) : ℕ :=
  Tables.magXNat (28 * 256 + (if 8 ≤ v then v - 8 else 7 - v))

def sigYNat (v : ℕ) : ℕ :=
  if 8 ≤ v then Tables.magYNat (28 * 256 + (v - 8))
  else P256 - Tables.magYNat (28 * 256 + (7 - v))

def bitVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (t : ℕ) (ht : t < 4) : F circomPrime :=
  Expression.eval env.toEnvironment b[t]

def xVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (t : ℕ) (ht : t < 3) : F circomPrime :=
  2 * bitVal env b 3 (by omega) * bitVal env b t (by omega)
    - bitVal env b 3 (by omega) - bitVal env b t (by omega) + 1

def blockVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (v : ℕ) : F circomPrime :=
  (if v % 2 = 1 then xVal env b 0 (by omega) else 1 - xVal env b 0 (by omega))
    * (if v / 2 % 2 = 1 then xVal env b 1 (by omega)
       else 1 - xVal env b 1 (by omega))

def mVal (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) : ℕ :=
  (bitVal env b 0 (by omega)).val + 2 * (bitVal env b 1 (by omega)).val
    + 4 * (bitVal env b 2 (by omega)).val + 8 * (bitVal env b 3 (by omega)).val

def xExpr (b : Var (fields 4) (F circomPrime))
    (w : Var (fields 3) (F circomPrime)) (t : ℕ) (ht : t < 3) :
    Expression (F circomPrime) :=
  w[t] * (2 : F circomPrime) - b[3] - b[t]'(by omega)
    + ((1 : F circomPrime) : Expression (F circomPrime))

def xCoeff (i : Fin 4) (j : Fin 7) : F circomPrime :=
  ((limbOfNat (Tables.magXNat (28 * 256 + j.val)) i.val : ℕ) : F circomPrime) -
    ((limbOfNat (Tables.magXNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def xBase (i : Fin 4) : F circomPrime :=
  ((limbOfNat (Tables.magXNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def xSelExpr (e : Var (fields 7) (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun i : Fin 4 => Select.weightedSum e (xCoeff i) (xBase i)

attribute [irreducible] xSelExpr

@[simp] theorem xSelExpr_get (e : Var (fields 7) (F circomPrime))
    (i : ℕ) (hi : i < 4) :
    (xSelExpr e)[i]'hi = Select.weightedSum e (xCoeff ⟨i, hi⟩) (xBase ⟨i, hi⟩) := by
  unfold xSelExpr
  rw [Vector.getElem_ofFn]

/-- The positive-`y` one-hot coefficients (sign bit fixed to `1`). -/
def yCoeff (i : Fin 4) (j : Fin 7) : F circomPrime :=
  ((limbOfNat (Tables.magYNat (28 * 256 + j.val)) i.val : ℕ) : F circomPrime) -
    ((limbOfNat (Tables.magYNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def yBase (i : Fin 4) : F circomPrime :=
  ((limbOfNat (Tables.magYNat (28 * 256 + 7)) i.val : ℕ) : F circomPrime)

def ySelExpr (e : Var (fields 7) (F circomPrime)) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun i : Fin 4 => Select.weightedSum e (yCoeff i) (yBase i)

attribute [irreducible] ySelExpr

@[simp] theorem ySelExpr_get (e : Var (fields 7) (F circomPrime))
    (i : ℕ) (hi : i < 4) :
    (ySelExpr e)[i]'hi = Select.weightedSum e (yCoeff ⟨i, hi⟩) (yBase ⟨i, hi⟩) := by
  unfold ySelExpr
  rw [Vector.getElem_ofFn]

def main (b : Var (fields 4) (F circomPrime)) :
    Circuit (F circomPrime) (Var Select.AffPoint (F circomPrime)) := do

  let w ← ProvableType.witness (α := fields 3) fun env =>
    Vector.ofFn fun t : Fin 3 =>
      bitVal env b 3 (by omega) * bitVal env b t.val (by omega)
  Circuit.forEach (Vector.ofFn fun t : Fin 3 =>
    b[3] * (b[t.val]'(by omega)) - w[t.val]'t.isLt) assertZero

  let blk ← ProvableType.witness (α := fields 1) fun env =>
    Vector.ofFn fun _ : Fin 1 =>
      xVal env b 0 (by omega) * xVal env b 1 (by omega)
  Circuit.forEach (Vector.ofFn fun _ : Fin 1 =>
    xExpr b w 0 (by omega) * xExpr b w 1 (by omega)
      - blk[0]'(by omega)) assertZero

  let e ← ProvableType.witness (α := fields 7) fun env =>
    Vector.ofFn fun v : Fin 7 =>
      blockVal env b (v.val % 4)
        * (if v.val / 4 = 1 then xVal env b 2 (by omega)
           else 1 - xVal env b 2 (by omega))
  Circuit.forEach (Vector.ofFn fun v : Fin 7 =>
    Select.blockExpr (xExpr b w 0 (by omega)) (xExpr b w 1 (by omega)) (blk[0]'(by omega))
        (v.val % 4)
      * (if v.val / 4 = 1 then xExpr b w 2 (by omega)
         else ((1 : F circomPrime) : Expression (F circomPrime)) - xExpr b w 2 (by omega))
      - e[v.val]'v.isLt) assertZero

  return { x := xSelExpr e, y := ySelExpr e }

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields 4) Select.AffPoint main where

  localLength _ := 11
  output _ i0 :=
    { x := xSelExpr (varFromOffset (fields 7) (i0 + 4)),
      y := ySelExpr (varFromOffset (fields 7) (i0 + 4)) }
  localLength_eq := by
    intro input offset
    simp +arith only [main, xSelExpr, ySelExpr, Select.weightedSum, circuit_norm, numLimbs]
  output_eq := by
    intro input offset
    simp +arith only [main, xSelExpr, ySelExpr, Select.weightedSum, circuit_norm, numLimbs]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, xSelExpr, ySelExpr, Select.weightedSum, circuit_norm, numLimbs]
  channelsLawful := by
    intro input offset
    simp only [main, xSelExpr, ySelExpr, Select.weightedSum, circuit_norm]

def Assumptions (b : fields 4 (F circomPrime)) : Prop :=
  (∀ i : Fin 4, IsBool b[i]) ∧ b[3]'(by omega) = 1

def bitsVal (b : fields 4 (F circomPrime)) : ℕ :=
  b[0].val + 2 * b[1].val + 4 * b[2].val + 8 * b[3].val

def Spec (b : fields 4 (F circomPrime))
    (out : Select.AffPoint (F circomPrime)) : Prop :=
  out.x = emuOfNat (sigXNat (bitsVal b)) ∧
  out.y = emuOfNat (sigYNat (bitsVal b))

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelect.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

/-- The three nonconstant bits of the top recoded digit, together with the
original scalar parity bit.  The fourth recoded bit is definitionally one in
`Comb`, so carrying it through either old selector only duplicated work. -/
structure Inputs (F : Type) where
  bits : fields 3 F
  selector : F
deriving ProvableStruct

abbrev Field := F circomPrime

/-- Möbius coefficient of a four-variable Boolean lookup table.  Bits of the
coefficient index are ordered `(b0,b1,b2,selector)`. -/
def coeff (table : Nat → Field) : Nat → Field
  | 0 => table 0
  | 1 => table 1 - table 0
  | 2 => table 2 - table 0
  | 3 => table 3 - table 2 - table 1 + table 0
  | 4 => table 4 - table 0
  | 5 => table 5 - table 4 - table 1 + table 0
  | 6 => table 6 - table 4 - table 2 + table 0
  | 7 => table 7 - table 6 - table 5 - table 3
      + table 4 + table 2 + table 1 - table 0
  | 8 => table 8 - table 0
  | 9 => table 9 - table 8 - table 1 + table 0
  | 10 => table 10 - table 8 - table 2 + table 0
  | 11 => table 11 - table 10 - table 9 - table 3
      + table 8 + table 2 + table 1 - table 0
  | 12 => table 12 - table 8 - table 4 + table 0
  | 13 => table 13 - table 12 - table 9 - table 5
      + table 8 + table 4 + table 1 - table 0
  | 14 => table 14 - table 12 - table 10 - table 6
      + table 8 + table 4 + table 2 - table 0
  | 15 => table 15 - table 14 - table 13 - table 11 - table 7
      + table 12 + table 10 + table 9 + table 6 + table 5 + table 3
      - table 8 - table 4 - table 2 - table 1 + table 0
  | _ => 0

/-- The semantic multilinear extension. -/
def lookupValue (table : Nat → Field) (b0 b1 b2 selector : Field) : Field :=
  coeff table 0
    + b0 * coeff table 1
    + b1 * coeff table 2
    + b2 * coeff table 4
    + selector * coeff table 8
    + (b0 * b1) * coeff table 3
    + (b0 * b2) * coeff table 5
    + (b0 * selector) * coeff table 9
    + (b1 * b2) * coeff table 6
    + (b1 * selector) * coeff table 10
    + (b2 * selector) * coeff table 12
    + (b0 * b1 * b2) * coeff table 7
    + (b0 * b1 * selector) * coeff table 11
    + (b0 * b2 * selector) * coeff table 13
    + (b1 * b2 * selector) * coeff table 14
    + (b0 * b1 * b2 * selector) * coeff table 15

/-- The eleven nonlinear monomials of four inputs, in the order used by
`lookupExpr`. -/
def monomialAt (b0 b1 b2 selector : Field) : Nat → Field
  | 0 => b0 * b1
  | 1 => b0 * b2
  | 2 => b0 * selector
  | 3 => b1 * b2
  | 4 => b1 * selector
  | 5 => b2 * selector
  | 6 => b0 * b1 * b2
  | 7 => b0 * b1 * selector
  | 8 => b0 * b2 * selector
  | 9 => b1 * b2 * selector
  | 10 => b0 * b1 * b2 * selector
  | _ => 0

def witnessValues (env : ProverEnvironment Field)
    (input : Var Inputs Field) : fields 11 Field :=
  let b0 := Expression.eval env.toEnvironment input.bits[0]
  let b1 := Expression.eval env.toEnvironment input.bits[1]
  let b2 := Expression.eval env.toEnvironment input.bits[2]
  let s := Expression.eval env.toEnvironment input.selector
  Vector.ofFn fun i : Fin 11 => monomialAt b0 b1 b2 s i.val

/-- R1CS equations for the eleven monomials.  Higher products are chained
through earlier witnesses, keeping every row bilinear. -/
def constraintAt (input : Var Inputs Field) (w : Var (fields 11) Field) :
    Nat → Expression Field
  | 0 => input.bits[0] * input.bits[1] - w[0]
  | 1 => input.bits[0] * input.bits[2] - w[1]
  | 2 => input.bits[0] * input.selector - w[2]
  | 3 => input.bits[1] * input.bits[2] - w[3]
  | 4 => input.bits[1] * input.selector - w[4]
  | 5 => input.bits[2] * input.selector - w[5]
  | 6 => w[0] * input.bits[2] - w[6]
  | 7 => w[0] * input.selector - w[7]
  | 8 => w[1] * input.selector - w[8]
  | 9 => w[3] * input.selector - w[9]
  | 10 => w[6] * input.selector - w[10]
  | _ => 0

/-- Affine form of the lookup after the nonlinear monomials have been
witnessed. -/
def lookupExpr (table : Nat → Field) (input : Var Inputs Field)
    (w : Var (fields 11) Field) : Expression Field :=
  coeff table 0
    + input.bits[0] * coeff table 1
    + input.bits[1] * coeff table 2
    + input.bits[2] * coeff table 4
    + input.selector * coeff table 8
    + w[0] * coeff table 3
    + w[1] * coeff table 5
    + w[2] * coeff table 9
    + w[3] * coeff table 6
    + w[4] * coeff table 10
    + w[5] * coeff table 12
    + w[6] * coeff table 7
    + w[7] * coeff table 11
    + w[8] * coeff table 13
    + w[9] * coeff table 14
    + w[10] * coeff table 15

/-- Table index `0..7` is the even-parity top point; index `8..15` is the
ordinary odd-parity top point. -/
def xTable (limb : Fin 4) (index : Nat) : Field :=
  if index < 8 then
    ((limbOfNat (EvenTableTop.evenXNatTop (8 + index)) limb.val : Nat) : Field)
  else
    ((limbOfNat (Tables.magXNat (28 * 256 + (index - 8))) limb.val : Nat) : Field)

def yTable (limb : Fin 4) (index : Nat) : Field :=
  if index < 8 then
    ((limbOfNat (EvenTableTop.evenYNatTop (8 + index)) limb.val : Nat) : Field)
  else
    ((limbOfNat (Tables.magYNat (28 * 256 + (index - 8))) limb.val : Nat) : Field)

def outputExpr (input : Var Inputs Field) (w : Var (fields 11) Field) :
    Var Select.AffPoint Field :=
  { x := Vector.ofFn fun limb : Fin 4 => lookupExpr (xTable limb) input w
    y := Vector.ofFn fun limb : Fin 4 => lookupExpr (yTable limb) input w }

def main (input : Var Inputs Field) :
    Circuit Field (Var Select.AffPoint Field) := do
  let w ← ProvableType.witness (α := fields 11) fun env =>
    witnessValues env input
  Circuit.forEach
    (Vector.ofFn fun i : Fin 11 => constraintAt input w i.val) assertZero
  return outputExpr input w

instance elaborated :
    ElaboratedCircuit Field Inputs Select.AffPoint main := by
  elaborate_circuit

def Assumptions (input : Inputs Field) : Prop :=
  (∀ i : Fin 3, IsBool input.bits[i]) ∧ IsBool input.selector

def Spec (input : Inputs Field) (out : Select.AffPoint Field) : Prop :=
  out.x = Vector.ofFn (fun limb : Fin 4 =>
      lookupValue (xTable limb) input.bits[0] input.bits[1] input.bits[2]
        input.selector) ∧
  out.y = Vector.ofFn (fun limb : Fin 4 =>
      lookupValue (yTable limb) input.bits[0] input.bits[1] input.bits[2]
        input.selector)

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 1600000 in
theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (n : ℕ)
    (hb : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      ∀ (j : ℕ) (hj : j < 4),
        Expression.eval env.toEnvironment (b[j]'hj)
          = Expression.eval env'.toEnvironment (b[j]'hj))
    (env env' : ProverEnvironment (F circomPrime)) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main b).operations n) := by
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true, implies_true]
  and_intros
  all_goals first
    | trivial
    | (intro hagree hpin
       have hbit := hb _ env env' (by omega) hagree hpin
       apply Vector.ext; intro i hi
       simp only [Vector.getElem_ofFn, bitVal, xVal, blockVal, hbit])

end ComputableWitness

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_6

-- Adapted donor module: SelectBorrow
section DonorFile5_7

/-!
### Schoolbook borrow bits for `P256 - y`

The width-12 selector needs, for every table entry, both the positive `y` limbs
and the limbs of the canonical negation `P256 - y`.  Selecting both costs two
full four-limb lookups.  This file provides the arithmetic that lets the second
lookup be replaced by an affine expression in the first one plus the three
*borrow bits* of the schoolbook subtraction `P256 - y`, which are themselves a
single (scalar) table lookup.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Borrow

/-- The borrow out of the low `k` limbs of the schoolbook subtraction `A - B`. -/
def borrowAt (A B k : ℕ) : ℕ :=
  if A % 2 ^ (limbBits * k) < B % 2 ^ (limbBits * k) then 1 else 0

theorem borrowAt_zero (A B : ℕ) : borrowAt A B 0 = 0 := by
  simp only [borrowAt, Nat.mul_zero, pow_zero, Nat.mod_one, lt_irrefl, if_false]

theorem borrowAt_le_one (A B k : ℕ) : borrowAt A B k ≤ 1 := by
  unfold borrowAt; split <;> omega

/-- Modular form of the borrow: the low `M`-part of a difference. -/
theorem sub_mod_add (A B M : ℕ) (hM : 0 < M) (hBA : B ≤ A) :
    (A - B) % M + B % M = A % M + M * (if A % M < B % M then 1 else 0) := by
  have hL : ((A - B) % M + B % M) % M = A % M := by
    rw [← Nat.add_mod, Nat.sub_add_cancel hBA]
  have hr : (A - B) % M < M := Nat.mod_lt _ hM
  have hb : B % M < M := Nat.mod_lt _ hM
  have ha : A % M < M := Nat.mod_lt _ hM
  rcases lt_or_ge ((A - B) % M + B % M) M with h | h
  · rw [Nat.mod_eq_of_lt h] at hL
    rw [if_neg (by omega)]
    omega
  · have h2 : ((A - B) % M + B % M) % M = (A - B) % M + B % M - M := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at hL
    rw [if_pos (by omega)]
    omega

/-- Extraction of a limb through a two-level modulus split. -/
theorem limbOfNat_eq_mod_div (X i : ℕ) :
    limbOfNat X i = X % 2 ^ (limbBits * (i + 1)) / 2 ^ (limbBits * i) := by
  have hpow : (2 : ℕ) ^ (limbBits * (i + 1)) = 2 ^ (limbBits * i) * 2 ^ limbBits := by
    rw [← pow_add]; ring_nf
  rw [hpow, Nat.mod_mul_right_div_self]
  rfl

/-- Pure cancellation step used by `limb_sub`. -/
private theorem cancel_step (m rA rB rD wA wB wD c0 c1 B64 : ℕ) (hm : 0 < m)
    (hbig : wD * m + rD + (wB * m + rB) = wA * m + rA + m * B64 * c1)
    (hsmall : rD + rB = rA + m * c0) :
    wB + wD + c0 = wA + B64 * c1 := by
  have h : ((wB + wD + c0) * m : ℤ) = ((wA + B64 * c1) * m : ℤ) := by
    have h1 : (wD * m + rD + (wB * m + rB) : ℤ) = wA * m + rA + m * B64 * c1 := by
      exact_mod_cast hbig
    have h2 : (rD + rB : ℤ) = rA + m * c0 := by exact_mod_cast hsmall
    linear_combination h1 - h2
  exact Nat.eq_of_mul_eq_mul_right hm (by exact_mod_cast h)

/-- Schoolbook subtraction, one limb at a time. -/
theorem limb_sub (A B : ℕ) (hBA : B ≤ A) (i : ℕ) :
    limbOfNat B i + limbOfNat (A - B) i + borrowAt A B i
      = limbOfNat A i + 2 ^ limbBits * borrowAt A B (i + 1) := by
  have hmpos : 0 < 2 ^ (limbBits * i) := Nat.two_pow_pos _
  have hMpos : 0 < 2 ^ (limbBits * (i + 1)) := Nat.two_pow_pos _
  have hMm : (2 : ℕ) ^ (limbBits * (i + 1)) = 2 ^ (limbBits * i) * 2 ^ limbBits := by
    rw [← pow_add]; ring_nf
  have hdvd : (2 : ℕ) ^ (limbBits * i) ∣ 2 ^ (limbBits * (i + 1)) := ⟨2 ^ limbBits, hMm⟩
  have hsplit : ∀ X : ℕ, X % 2 ^ (limbBits * (i + 1))
      = limbOfNat X i * 2 ^ (limbBits * i) + X % 2 ^ (limbBits * i) := by
    intro X
    have h1 : X % 2 ^ (limbBits * (i + 1)) % 2 ^ (limbBits * i) = X % 2 ^ (limbBits * i) :=
      Nat.mod_mod_of_dvd X hdvd
    have h2 : X % 2 ^ (limbBits * (i + 1)) / 2 ^ (limbBits * i) * 2 ^ (limbBits * i)
        + X % 2 ^ (limbBits * (i + 1)) % 2 ^ (limbBits * i)
        = X % 2 ^ (limbBits * (i + 1)) := Nat.div_add_mod' _ _
    rw [limbOfNat_eq_mod_div]
    omega
  have hbig := sub_mod_add A B (2 ^ (limbBits * (i + 1))) hMpos hBA
  have hsmall := sub_mod_add A B (2 ^ (limbBits * i)) hmpos hBA
  rw [show (if A % 2 ^ (limbBits * (i + 1)) < B % 2 ^ (limbBits * (i + 1)) then 1 else 0)
        = borrowAt A B (i + 1) from rfl] at hbig
  rw [show (if A % 2 ^ (limbBits * i) < B % 2 ^ (limbBits * i) then 1 else 0)
        = borrowAt A B i from rfl] at hsmall
  rw [hsplit A, hsplit B, hsplit (A - B), hMm] at hbig
  exact cancel_step _ _ _ _ _ _ _ _ _ _ hmpos hbig hsmall

/-- Packed borrow bits of `P256 - y`: bit `k` sits in limb `k`. -/
def borrowNat (y : ℕ) : ℕ :=
  borrowAt P256 y 1 + 2 ^ limbBits * borrowAt P256 y 2 +
    2 ^ limbBits * 2 ^ limbBits * borrowAt P256 y 3

theorem limbOfNat_borrowNat (y k : ℕ) (hk : k < 3) :
    limbOfNat (borrowNat y) k = borrowAt P256 y (k + 1) := by
  have h1 := borrowAt_le_one P256 y 1
  have h2 := borrowAt_le_one P256 y 2
  have h3 := borrowAt_le_one P256 y 3
  rcases (show borrowAt P256 y 1 = 0 ∨ borrowAt P256 y 1 = 1 by omega) with e1 | e1 <;>
    rcases (show borrowAt P256 y 2 = 0 ∨ borrowAt P256 y 2 = 1 by omega) with e2 | e2 <;>
      rcases (show borrowAt P256 y 3 = 0 ∨ borrowAt P256 y 3 = 1 by omega) with e3 | e3 <;>
        interval_cases k <;>
          simp only [borrowNat, limbOfNat, limbBits, e1, e2, e3] <;> norm_num

theorem limbOfNat_borrowNat_three (y : ℕ) : limbOfNat (borrowNat y) 3 = 0 := by
  have h1 := borrowAt_le_one P256 y 1
  have h2 := borrowAt_le_one P256 y 2
  have h3 := borrowAt_le_one P256 y 3
  rcases (show borrowAt P256 y 1 = 0 ∨ borrowAt P256 y 1 = 1 by omega) with e1 | e1 <;>
    rcases (show borrowAt P256 y 2 = 0 ∨ borrowAt P256 y 2 = 1 by omega) with e2 | e2 <;>
      rcases (show borrowAt P256 y 3 = 0 ∨ borrowAt P256 y 3 = 1 by omega) with e3 | e3 <;>
        simp only [borrowNat, limbOfNat, limbBits, e1, e2, e3] <;> norm_num

theorem borrowAt_four (y : ℕ) (hy : y ≤ P256) : borrowAt P256 y 4 = 0 := by
  have hp : P256 < 2 ^ (limbBits * 4) := by decide
  unfold borrowAt
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega)]
  exact if_neg (by omega)

/-- Borrow bit *out of* limb `i` (`0` at the top limb, where nothing is borrowed). -/
def bval (y i : ℕ) : ℕ := if i < 3 then limbOfNat (borrowNat y) i else 0

/-- Borrow bit *into* limb `i`. -/
def bm (y i : ℕ) : ℕ := if i = 0 then 0 else bval y (i - 1)

theorem bval_eq (y i : ℕ) (hy : y ≤ P256) (hi : i < 4) :
    bval y i = borrowAt P256 y (i + 1) := by
  unfold bval
  split
  · exact limbOfNat_borrowNat y i (by omega)
  · have : i = 3 := by omega
    subst this
    exact (borrowAt_four y hy).symm

theorem bm_eq (y i : ℕ) (hy : y ≤ P256) (hi : i < 4) :
    bm y i = borrowAt P256 y i := by
  unfold bm
  split
  · next h => rw [h, borrowAt_zero]
  · next h =>
    rw [bval_eq y (i - 1) hy (by omega)]
    congr 1
    omega

/-- The limbwise sign delta of `y`, expressed affinely in the limbs of the
canonical negation `P256 - y` and the two borrow bits. -/
theorem delta_field (y : ℕ) (hy : y ≤ P256) (i : ℕ) (hi : i < 4) :
    ((limbOfNat y i : ℕ) : F circomPrime) - ((limbOfNat (P256 - y) i : ℕ) : F circomPrime)
      = ((limbOfNat P256 i : ℕ) : F circomPrime)
          - 2 * ((limbOfNat (P256 - y) i : ℕ) : F circomPrime)
          + ((2 ^ limbBits : ℕ) : F circomPrime) * ((bval y i : ℕ) : F circomPrime)
          - ((bm y i : ℕ) : F circomPrime) := by
  have hnat := limb_sub P256 y hy i
  rw [bval_eq y i hy hi, bm_eq y i hy hi]
  have hcast : ((limbOfNat y i + limbOfNat (P256 - y) i + borrowAt P256 y i : ℕ) :
      F circomPrime)
      = ((limbOfNat P256 i + 2 ^ limbBits * borrowAt P256 y (i + 1) : ℕ) : F circomPrime) := by
    rw [hnat]
  push_cast at hcast
  push_cast
  linear_combination hcast

/-- The three borrow bits of `P256 - y`, packed into one small number. -/
def packedNat (y : ℕ) : ℕ :=
  borrowAt P256 y 1 + 2 * borrowAt P256 y 2 + 4 * borrowAt P256 y 3

theorem packedNat_lt (y : ℕ) : packedNat y < 8 := by
  have h1 := borrowAt_le_one P256 y 1
  have h2 := borrowAt_le_one P256 y 2
  have h3 := borrowAt_le_one P256 y 3
  unfold packedNat
  omega

theorem limbOfNat_packedNat (y : ℕ) : limbOfNat (packedNat y) 0 = packedNat y := by
  have h := packedNat_lt y
  simp only [limbOfNat, limbBits, Nat.mul_zero, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt (by
    have : (8 : ℕ) ≤ 2 ^ 64 := by norm_num
    omega)

theorem packedNat_eq_bvals (y : ℕ) :
    packedNat y = bval y 0 + 2 * bval y 1 + 4 * bval y 2 := by
  unfold packedNat bval
  rw [if_pos (by norm_num), if_pos (by norm_num), if_pos (by norm_num),
    limbOfNat_borrowNat y 0 (by norm_num), limbOfNat_borrowNat y 1 (by norm_num),
    limbOfNat_borrowNat y 2 (by norm_num)]

theorem bval_le_one (y i : ℕ) : bval y i ≤ 1 := by
  unfold bval
  split
  · next h =>
    rw [limbOfNat_borrowNat y i h]
    exact borrowAt_le_one _ _ _
  · omega

/-- Three boolean field elements are determined by their weighted sum. -/
theorem bits3_unique {w0 w1 w2 : F circomPrime}
    (h0 : IsBool w0) (h1 : IsBool w1) (h2 : IsBool w2)
    (n0 n1 n2 : ℕ) (hn0 : n0 ≤ 1) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (h : w0 + w1 * 2 + w2 * 4 = ((n0 + 2 * n1 + 4 * n2 : ℕ) : F circomPrime)) :
    w0 = (n0 : F circomPrime) ∧ w1 = (n1 : F circomPrime) ∧ w2 = (n2 : F circomPrime) := by
  obtain ⟨m0, hm0, hw0⟩ : ∃ m : ℕ, m ≤ 1 ∧ w0 = (m : F circomPrime) := by
    rcases h0 with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · exact ⟨1, by omega, by simpa using h⟩
  obtain ⟨m1, hm1, hw1⟩ : ∃ m : ℕ, m ≤ 1 ∧ w1 = (m : F circomPrime) := by
    rcases h1 with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · exact ⟨1, by omega, by simpa using h⟩
  obtain ⟨m2, hm2, hw2⟩ : ∃ m : ℕ, m ≤ 1 ∧ w2 = (m : F circomPrime) := by
    rcases h2 with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · exact ⟨1, by omega, by simpa using h⟩
  subst hw0; subst hw1; subst hw2
  have hcast : ((m0 + 2 * m1 + 4 * m2 : ℕ) : F circomPrime)
      = ((n0 + 2 * n1 + 4 * n2 : ℕ) : F circomPrime) := by
    push_cast
    push_cast at h
    linear_combination h
  have hlt : ∀ a b c : ℕ, a ≤ 1 → b ≤ 1 → c ≤ 1 → a + 2 * b + 4 * c < circomPrime := by
    intro a b c ha hb hc
    have : circomPrime > 8 := by decide
    omega
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (hlt m0 m1 m2 hm0 hm1 hm2),
    ZMod.val_natCast_of_lt (hlt n0 n1 n2 hn0 hn1 hn2)] at hval
  refine ⟨?_, ?_, ?_⟩ <;> [skip; skip; skip] <;> (congr 1; omega)

/-- The circuit-shaped form of `delta_field`. -/
theorem delta_field' (y : ℕ) (hy : y ≤ P256) (i : ℕ) (hi : i < 4) :
    ((limbOfNat P256 i : ℕ) : F circomPrime)
        - ((limbOfNat (P256 - y) i : ℕ) : F circomPrime) * 2
        + ((bval y i : ℕ) : F circomPrime) * ((2 ^ limbBits : ℕ) : F circomPrime)
        - (if i = 0 then 0 else ((bval y (i - 1) : ℕ) : F circomPrime))
      = ((limbOfNat y i : ℕ) : F circomPrime)
          - ((limbOfNat (P256 - y) i : ℕ) : F circomPrime) := by
  have h := delta_field y hy i hi
  have hbm : ((bm y i : ℕ) : F circomPrime)
      = (if i = 0 then 0 else ((bval y (i - 1) : ℕ) : F circomPrime)) := by
    unfold bm
    split
    · simp
    · rfl
  rw [hbm] at h
  linear_combination -h

/-!
#### Borrow-free negation

Every entry of the fixed-base tables satisfies `y % 2^64 ≤ P256 % 2^64`, which
is exactly the statement that the schoolbook subtraction `P256 - y` produces no
borrows at all (the three high limbs of `P256` are `2^64 - 1`, so they can never
be the source of a borrow).  That turns the sign delta into the purely affine
expression `limbOfNat P256 i - 2 * limbOfNat (P256 - y) i`, deleting the whole
packed-borrow selection column, its two witnessed bits, and their three
booleanity rows from the width-12 selector.
-/

private theorem mod_le_of_low (M T y : ℕ) (hMT : M = 2 ^ 64 * T) (hT : 0 < T)
    (hlow : y % 2 ^ 64 ≤ 2 ^ 64 - 4294968273) : y % M ≤ M - 4294968273 := by
  have hdvd : (2 : ℕ) ^ 64 ∣ M := ⟨T, hMT⟩
  have hr : y % M % 2 ^ 64 = y % 2 ^ 64 := Nat.mod_mod_of_dvd y hdvd
  have hq : y % M / 2 ^ 64 * 2 ^ 64 + y % M % 2 ^ 64 = y % M := Nat.div_add_mod' _ _
  have hlt : y % M < M := Nat.mod_lt _ (by omega)
  have h2 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  omega

private theorem no_borrow_step (y T : ℕ) (hT : 0 < T)
    (hP : P256 % (2 ^ 64 * T) = 2 ^ 64 * T - 4294968273)
    (hlow : y % 2 ^ 64 ≤ 2 ^ 64 - 4294968273) :
    ¬ (P256 % (2 ^ 64 * T) < y % (2 ^ 64 * T)) := by
  have h := mod_le_of_low (2 ^ 64 * T) T y rfl hT hlow
  omega

/-- Under the no-borrow precondition, every schoolbook borrow of `P256 - y`
vanishes. -/
theorem borrowAt_eq_zero (y : ℕ) (hlow : y % 2 ^ 64 ≤ P256 % 2 ^ 64)
    (k : ℕ) (hk : k ≤ 4) : borrowAt P256 y k = 0 := by
  have hlow' : y % 2 ^ 64 ≤ 2 ^ 64 - 4294968273 := by
    rwa [show P256 % 2 ^ 64 = 2 ^ 64 - 4294968273 from by decide] at hlow
  unfold borrowAt
  rw [if_neg]
  simp only [limbBits]
  interval_cases k
  · simp only [Nat.mul_zero, pow_zero, Nat.mod_one, lt_irrefl, not_false_iff]
  · rw [show (2 : ℕ) ^ (64 * 1) = 2 ^ 64 * 1 from by norm_num]
    exact no_borrow_step y 1 (by norm_num) (by decide) hlow'
  · rw [show (2 : ℕ) ^ (64 * 2) = 2 ^ 64 * 2 ^ 64 from by norm_num]
    exact no_borrow_step y (2 ^ 64) (by positivity) (by decide) hlow'
  · rw [show (2 : ℕ) ^ (64 * 3) = 2 ^ 64 * 2 ^ 128 from by norm_num]
    exact no_borrow_step y (2 ^ 128) (by positivity) (by decide) hlow'
  · rw [show (2 : ℕ) ^ (64 * 4) = 2 ^ 64 * 2 ^ 192 from by norm_num]
    exact no_borrow_step y (2 ^ 192) (by positivity) (by decide) hlow'

/-- With no borrows the packed borrow number is zero, hence every borrow bit is. -/
theorem bval_eq_zero (y : ℕ) (hlow : y % 2 ^ 64 ≤ P256 % 2 ^ 64) (i : ℕ) :
    bval y i = 0 := by
  have hb : borrowNat y = 0 := by
    unfold borrowNat
    rw [borrowAt_eq_zero y hlow 1 (by omega), borrowAt_eq_zero y hlow 2 (by omega),
      borrowAt_eq_zero y hlow 3 (by omega)]
    ring
  unfold bval
  split
  · rw [hb]
    simp [limbOfNat]
  · rfl

/-- The borrow-free sign delta: a purely affine expression in the selected
negated limbs, with no borrow bits at all. -/
theorem delta_field_noborrow (y : ℕ) (hy : y ≤ P256)
    (hlow : y % 2 ^ 64 ≤ P256 % 2 ^ 64) (i : ℕ) (hi : i < 4) :
    ((limbOfNat P256 i : ℕ) : F circomPrime)
        - ((limbOfNat (P256 - y) i : ℕ) : F circomPrime) * 2
      = ((limbOfNat y i : ℕ) : F circomPrime)
          - ((limbOfNat (P256 - y) i : ℕ) : F circomPrime) := by
  have h := delta_field' y hy i hi
  rw [bval_eq_zero y hlow i] at h
  by_cases hi0 : i = 0
  · subst hi0
    rw [if_pos rfl] at h
    simpa using h
  · rw [if_neg hi0, bval_eq_zero y hlow (i - 1)] at h
    simpa using h

end Borrow
end Solution.Secp256k1ScalarMulFixedBase


end DonorFile5_7

-- Adapted donor module: BorrowDerived
section DonorFile5_8

/-!
### The packed-borrow linking row is redundant

The width-12 selector delivers the three schoolbook borrow bits of `P256 - y`
as a *single* selected field element `s`, the packed value `Borrow.packedNat y`
(see `SelectBorrow.lean`).  The obvious way to unpack it is to witness three
bits `b0, b1, b2`, assert booleanity of each, and add one further *linking* row
`s = b0 + 2*b1 + 4*b2`.  That costs 3 allocations and 4 constraints.

This file records the observation that makes the linking row — and one of the
three allocations — unnecessary.  Witness only the two high bits `b1, b2` and
*define*

  `b0 := s - 2*b1 - 4*b2`

as a free affine expression.  Then `b0 + 2*b1 + 4*b2 = s` holds as a ring
identity rather than as a constraint, so the three booleanity rows on
`b0, b1, b2` already pin all three bits to the honest borrow bits.

`derived_bits_sound` is the soundness content (the constraints force the honest
values) and `derived_bits_complete` is the completeness content (the honest
values do satisfy the constraints).  Together they say that the 2-allocation /
3-constraint gadget is exactly equivalent to the 3-allocation / 4-constraint
one, which is the entire justification for the cost reduction.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Borrow

/-- **Soundness of the derived low borrow bit.**

If the selected packed scalar is `s = packedNat y`, and the two witnessed high
bits `b1, b2` together with the *derived* low bit `s - 2*b1 - 4*b2` are all
Boolean, then all three are forced to be the honest borrow bits of `P256 - y`.

No linking constraint is used: the weighted sum identity
`(s - 2*b1 - 4*b2) + 2*b1 + 4*b2 = s` is a ring identity. -/
theorem derived_bits_sound {s b1 b2 : F circomPrime} (y : ℕ)
    (h0 : IsBool (s - b1 * 2 - b2 * 4)) (h1 : IsBool b1) (h2 : IsBool b2)
    (hs : s = ((packedNat y : ℕ) : F circomPrime)) :
    s - b1 * 2 - b2 * 4 = ((bval y 0 : ℕ) : F circomPrime) ∧
      b1 = ((bval y 1 : ℕ) : F circomPrime) ∧
      b2 = ((bval y 2 : ℕ) : F circomPrime) := by
  refine bits3_unique h0 h1 h2 _ _ _
    (bval_le_one _ 0) (bval_le_one _ 1) (bval_le_one _ 2) ?_
  rw [← packedNat_eq_bvals, ← hs]
  ring

/-- **Completeness of the derived low borrow bit.**

With `b1, b2` set to the honest borrow bits and `s` the honest packed scalar,
the derived low bit really is the honest low borrow bit — so the three
booleanity rows are satisfiable, and nothing else has to be checked. -/
theorem derived_bits_complete (y : ℕ) :
    ((packedNat y : ℕ) : F circomPrime)
        - ((bval y 1 : ℕ) : F circomPrime) * 2
        - ((bval y 2 : ℕ) : F circomPrime) * 4
      = ((bval y 0 : ℕ) : F circomPrime) := by
  rw [packedNat_eq_bvals]
  push_cast
  ring

end Borrow
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_8

-- Adapted donor module: SelectCost
section DonorFile5_9

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select

open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS


theorem affine_blockExpr {x y wb : Expression (F circomPrime)}
    (hx : Affine x) (hy : Affine y) (hwb : Affine wb) (v : ℕ) :
    Affine (blockExpr x y wb v) := by
  unfold blockExpr
  split_ifs
  · exact Affine.add (Affine.sub (Affine.sub (Affine.const 1) hx) hy) hwb
  · exact Affine.sub hx hwb
  · exact Affine.sub hy hwb
  · exact hwb

theorem affine_ofFn_foldl_add {n : ℕ} (g : Fin n → Expression (F circomPrime))
    (hg : ∀ i, Affine (g i)) :
    Affine ((Vector.ofFn g).foldl (· + ·) 0) := by
  have hof : (Vector.ofFn g) = Vector.map g (Vector.finRange n) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_finRange]
  rw [hof, Vector.foldl_map, vector_foldl_finRange]
  exact affine_finFoldl' _ _ Affine.zero fun acc i hacc => Affine.add hacc (hg i)

end Select
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select12

/-- The width-12 selector returns the production affine-point type. -/
abbrev AffPoint := Select.AffPoint

abbrev Field := F circomPrime

def bitVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (i : Nat) (hi : i < 12) : Field := Expression.eval env.toEnvironment b[i]

def xVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (i : Nat) (hi : i < 11) : Field :=
  2 * bitVal env b 11 (by omega) * bitVal env b i (by omega) -
    bitVal env b 11 (by omega) - bitVal env b i (by omega) + 1

/-- The XNOR of the sign bit with magnitude bit `i`.  It is witnessed directly
(pinned by one rank-1 row), so it is a bare wire rather than an affine rewrite of
`b[11] * b[i]`; that keeps the whole selected-x expression free of the input
bits. -/
def xExpr (_b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (i : Nat) (hi : i < 11) : Expression Field :=
  w[i]'hi

/-- Low bit index of a magnitude-bit pair.  Pairs are
`(0,1),(2,3),(4,5),(7,8),(9,10)`; bit 6 is handled as a single-bit extension
of the inner one-hot, which is what makes the 7-bit inner / 4-bit outer split. -/
def pairLo : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | _ => 0

lemma pairLo_add_lt {p : Nat} (hp : p < 5) : pairLo p + 1 < 11 := by
  match p, hp with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

lemma pairLo_lt {p : Nat} (hp : p < 5) : pairLo p < 11 :=
  Nat.lt_of_succ_lt (pairLo_add_lt hp)

def pairExpr (x y xy : Expression Field) (v : Nat) : Expression Field :=
  if v = 0 then 1 - x - y + xy else if v = 1 then x - xy else
  if v = 2 then y - xy else xy

def pairVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (p v : Nat) (hp : p < 5) : Field :=
  let x := xVal env b (pairLo p) (pairLo_lt hp)
  let y := xVal env b (pairLo p + 1) (pairLo_add_lt hp)
  (if v % 2 = 1 then x else 1-x) * (if v / 2 % 2 = 1 then y else 1-y)

def hot4Val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (basePair v : Nat) (hp : basePair < 4) : Field :=
  pairVal env b basePair (v % 4) (by omega) *
    pairVal env b (basePair + 1) (v / 4) (by omega)

/-- Six-bit inner one-hot value (bits 0..5). -/
def hot6Val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (v : Nat) : Field := hot4Val env b 0 (v % 16) (by omega) * pairVal env b 2 (v / 16) (by omega)

/-- Seven-bit inner one-hot value (bits 0..6); the extension multiplies the
six-bit cell by the single bit-6 factor. -/
def hot7Val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (v : Nat) : Field := hot6Val env b (v % 64) *
      (if v / 64 = 1 then xVal env b 6 (by omega) else 1 - xVal env b 6 (by omega))

/-- One factor of a bit-pair one-hot, as an expression in the input bits. -/
def innerP (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 5) (u : Nat) : Expression Field :=
  pairExpr (xExpr b w (pairLo p) (pairLo_lt hp)) (xExpr b w (pairLo p + 1) (pairLo_add_lt hp))
    (blk[p]'hp) u

/-- A `4 x 4` one-hot from only nine products: the last row and the last column
are affine consequences of `sum_c P1 c = 1` and `sum_a P0 a = 1`.  Only the
fifteen cells `v < 15` are produced here; cell `15` is recovered by `hot4`. -/
def hot4gen (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field) (v : Nat) :
    Expression Field :=
  if ha : v % 4 < 3 then
    (if hc : v / 4 < 3 then h[v % 4 + 3 * (v / 4)]'(by omega)
     else P0 (v % 4) - h[v % 4]'(by omega) - h[v % 4 + 3]'(by omega) - h[v % 4 + 6]'(by omega))
  else
    (if hc : v / 4 < 3 then
      P1 (v / 4) - h[3 * (v / 4)]'(by omega) - h[3 * (v / 4) + 1]'(by omega)
        - h[3 * (v / 4) + 2]'(by omega)
     else 0)

/-- The fifteen derived cells of the four-bit one-hot on pairs `p`, `p+1`. -/
def hot4Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    Var (fields 15) Field :=
  Vector.ofFn fun v : Fin 15 =>
    hot4gen (innerP b w blk p (by omega)) (innerP b w blk (p + 1) (by omega)) h v.val

/-- The forty-eight cells of the `c < 3` part of the six-bit one-hot, from
forty-five products: the `a = 15` row is affine. -/
def inner6Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) : Var (fields 48) Field :=
  Vector.ofFn fun v : Fin 48 =>
    if hh : v.val % 16 < 15 then h[15 * (v.val / 16) + v.val % 16]'(by have := v.isLt; omega)
    else innerP b w blk 2 (by decide) (v.val / 16)
      - (Vector.ofFn fun a : Fin 15 =>
          h[15 * (v.val / 16) + a.val]'(by have := v.isLt; have := a.isLt; omega)).foldl (·+·) 0

/-- The sixty-four cells of the bit-6 layer, from sixty-three products. -/
def inner7Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field) : Var (fields 64) Field :=
  Vector.ofFn fun v : Fin 64 =>
    if hk : v.val < 63 then h[v.val]'hk
    else xExpr b w 6 (by decide)
      - (Vector.ofFn fun a : Fin 63 => h[a.val]'a.isLt).foldl (·+·) 0

/-- The sixteenth four-bit one-hot cell is affine-derived. -/
def hot4 (blk : Var (fields 5) Field) (h : Var (fields 15) Field)
    (basePair : Nat) (hbase : basePair < 4) (v : Nat) (hv : v < 16) : Expression Field :=
  if _ : v = 15 then blk[basePair+1]'(by omega) - h[12] - h[13] - h[14]
  else h[v]'(by omega)

/-- Six-bit inner one-hot; its last pair branch is affine-derived. -/
def hot6 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (v : Nat) (_hv : v < 64) : Expression Field :=
  let a := v % 16
  let c := v / 16
  if _ : c < 3 then h6[c*16+a]'(by omega)
  else hot4 blk h4 0 (by omega) a (by omega) - h6[a] - h6[16+a] - h6[32+a]

/-- Seven-bit inner one-hot; the single bit-6 zero branch is affine-derived
from the six-bit cell. -/
def hot7 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (v : Nat) (_hv : v < 128) : Expression Field :=
  let a := v % 64
  if _ : v / 64 = 1 then h7[a]'(by omega)
  else hot6 blk h4 h6 a (by omega) - h7[a]'(by omega)

def inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))).foldl (·+·) 0

def innerVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb outer : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))

/-- The free affine correction produced by pairing two one-hot terms into a
single rank-2 row.  Because the inner one-hot cells are orthogonal idempotents,
`inner o0 * inner o1` collapses to this linear combination of the same cells
with compile-time coefficients. -/
def corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))).foldl (·+·) 0

def corrVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))

/-- The value pinned by one rank-2 row: it carries **two** of the four outer
one-hot terms at the cost of a single product. -/
def pairProdVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb c t : Nat) (table : Nat → Nat) : Field :=
  (pairVal env b 3 (2*t) (by omega) + innerVal env b limb (2*t+1+4*c) table) *
    (pairVal env b 3 (2*t+1) (by omega) + innerVal env b limb (2*t+4*c) table)
    - corrVal env b limb (2*t+4*c) (2*t+1+4*c) table

/-- The value pinned by one rank-2 row of the **single-stage** outer
contraction: it carries two of the *sixteen* outer one-hot terms for one
product.  Because the two outer cells `2k` and `2k+1` differ in exactly one
boolean factor their product vanishes, and because the inner one-hot cells are
orthogonal idempotents the remaining cross term collapses to the free affine
correction `corrVal`. -/
def outProdVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb k : Nat) (table : Nat → Nat) : Field :=
  (hot4Val env b 3 (2*k) (by omega) + innerVal env b limb (2*k+1) table) *
    (hot4Val env b 3 (2*k+1) (by omega) + innerVal env b limb (2*k) table)
    - corrVal env b limb (2*k) (2*k+1) table

/-- Limbwise positive-minus-negative y lookup.  This is deliberately a field
expression, not the limbs of a packed natural-number difference. -/
def yDeltaLimb (yTable : Nat → Nat) (idx limb : Nat) : Field :=
  ((limbOfNat (yTable idx) limb : Nat) : Field) -
    ((limbOfNat (P256 - yTable idx) limb : Nat) : Field)

def deltaInner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (yTable : Nat → Nat) : Expression Field :=
  inner limb outer blk h4 h6 h7 yTable -
    inner limb outer blk h4 h6 h7 (fun j => P256 - yTable j)

def deltaInnerVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb outer : Nat) (yTable : Nat → Nat) : Field :=
  innerVal env b limb outer yTable -
    innerVal env b limb outer (fun j => P256 - yTable j)

def selected (limb : Nat) (hlimb : limb < 4) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (table : Nat → Nat) : Expression Field :=
  inner limb 15 blk inner4 inner6 inner7 table +
    (Vector.ofFn fun q : Fin 15 => prod[limb*15+q.val]'(by omega)).foldl (·+·) 0

/-- Stage-1 of the two-stage outer contraction: contract over the low outer
pair (`pair 3`) at a fixed value `c` of the high outer pair.  Three products per
`(limb, c)`; the fourth branch is the affine remainder, exactly as in
`one_hot_sum_affine`.  Building the sixteen-cell outer one-hot explicitly is
pure waste — the two-stage form pays the same fifteen products per output
column and skips the nine one-hot products altogether. -/
def zsel (limb : Nat) (hl : limb < 4) (c : Nat) (hc : c < 4) (_blk : Var (fields 5) Field)
    (_h4 : Var (fields 15) Field) (_h6 : Var (fields 48) Field) (_h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (_table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun t : Fin 2 =>
    pA[8 * limb + 2 * c + t.val]'(by have := t.isLt; omega)).foldl (·+·) 0

def zselVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb c : Nat) (table : Nat → Nat) : Field :=
  ∑ t : Fin 2, pairProdVal env b limb c t.val table

/-- Single-stage outer contraction: the sixteen outer one-hot terms are paired
into eight rank-2 rows, one product each. -/
def selected2 (limb : Nat) (hl : limb < 4) (_blk : Var (fields 5) Field)
    (_h4 : Var (fields 15) Field) (_h6 : Var (fields 48) Field) (_h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (_table : Nat → Nat) :
    Expression Field :=
  (Vector.ofFn fun k : Fin 8 =>
    pA[8 * limb + k.val]'(by have := k.isLt; omega)).foldl (·+·) 0

def selectedVal2 (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb : Nat) (table : Nat → Nat) : Field :=
  ∑ k : Fin 8, outProdVal env b limb k.val table

/-- The selected x-coordinate is already affine in the selector witnesses, so
return it directly instead of materializing four redundant output witnesses. -/
def xSelExpr (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field) (pA : Var (fields 32) Field) :
    Var Emu Field :=
  Vector.ofFn fun i : Fin 4 =>
    selected2 i.val i.isLt blk inner4 inner6 inner7 pA xTable

attribute [irreducible] xSelExpr

@[simp] theorem xSelExpr_get (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field) (pA : Var (fields 32) Field)
    (i : Nat) (hi : i < 4) :
    (xSelExpr xTable blk inner4 inner6 inner7 pA)[i]'hi =
      selected2 i hi blk inner4 inner6 inner7 pA xTable := by
  unfold xSelExpr
  rw [Vector.getElem_ofFn]

def selectedVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb : Nat) (table : Nat → Nat) : Field :=
  innerVal env b limb 15 table + ∑ q : Fin 15,
    hot4Val env b 3 q.val (by omega) *
      (innerVal env b limb q.val table - innerVal env b limb 15 table)

def selectedDelta (limb : Nat) (hlimb : limb < 4) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (yTable : Nat → Nat) : Expression Field :=
  deltaInner limb 15 blk inner4 inner6 inner7 yTable +
    (Vector.ofFn fun q : Fin 15 => prod[limb*15+q.val]'(by omega)).foldl (·+·) 0

def bitsVal (b : fields 12 Field) : Nat :=
  b[0].val + 2*b[1].val + 4*b[2].val + 8*b[3].val + 16*b[4].val +
  32*b[5].val + 64*b[6].val + 128*b[7].val + 256*b[8].val +
  512*b[9].val + 1024*b[10].val + 2048*b[11].val

def magnitudeIndex (b : fields 12 Field) : Nat :=
  if 2048 ≤ bitsVal b then bitsVal b - 2048 else 2047 - bitsVal b

/-- The magnitude index of the *evaluated* selector inputs. -/
def magIdxOf (env : ProverEnvironment Field) (b : Var (fields 12) Field) : Nat :=
  magnitudeIndex (Vector.ofFn fun j : Fin 12 => bitVal env b j.val j.isLt)

/-- The three borrow bits of `P256 - yTable j`, packed into a single small
number (so one scalar lookup delivers all three). -/
def packedTable (yTable : Nat → Nat) (j : Nat) : Nat := Borrow.packedNat (yTable j)

/-- Scalar-quantity selection over the same outer one-hot: a single field
element, so the product array is only 15 wide. -/
def selectedE (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (prod : Var (fields 15) Field) (table : Nat → Nat) : Expression Field :=
  inner 0 15 blk inner4 inner6 inner7 table +
    (Vector.ofFn fun q : Fin 15 => prod[q.val]'q.isLt).foldl (·+·) 0

/-- The borrow bit out of limb `limb` (zero at the top limb).

Only the two high borrow bits are witnessed.  The low bit is the affine
remainder `sel - 2*b1 - 4*b2` of the packed borrow selection `sel`, so the
three booleanity rows alone already pin all three bits and no extra linking
row (nor a third allocation) is required. -/
def bExpr (limb : Nat) (sel : Expression Field) (bits : Var (fields 2) Field) :
    Expression Field :=
  if limb = 0 then sel - bits[0] * (2 : Field) - bits[1] * (4 : Field)
  else if limb = 1 then bits[0]
  else if limb = 2 then bits[1]
  else 0

def bVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb : Nat) (yTable : Nat → Nat) : Field :=
  if limb < 3 then ((Borrow.bval (yTable (magIdxOf env b)) limb : Nat) : Field) else 0

/-- The limbwise sign delta.  Every fixed-base table entry satisfies
`y % 2^64 ≤ P256 % 2^64`, so the schoolbook subtraction `P256 - y` never
borrows and the delta is *purely affine* in the selected negated limbs: no
borrow-bit column, no witnessed bits, no booleanity rows (see
`Borrow.delta_field_noborrow`). -/
def deltaExpr (limb : Nat) (hlimb : limb < 4) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (negA : Var (fields 32) Field)
    (yTable : Nat → Nat) : Expression Field :=
  ((limbOfNat P256 limb : Nat) : Field)
    - selected2 limb hlimb blk inner4 inner6 inner7 negA
        (fun j => P256 - yTable j) * (2 : Field)

def deltaValE (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb : Nat) (yTable : Nat → Nat) : Field :=
  ((limbOfNat P256 limb : Nat) : Field)
    - selectedVal2 env b limb (fun j => P256 - yTable j) * (2 : Field)

def selectedDeltaVal (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (limb : Nat) (yTable : Nat → Nat) : Field :=
  deltaInnerVal env b limb 15 yTable + ∑ q : Fin 15,
    hot4Val env b 3 q.val (by omega) *
      (deltaInnerVal env b limb q.val yTable - deltaInnerVal env b limb 15 yTable)

/-- Width-12 bilinear selector (7-bit inner / 4-bit outer) parameterized only by
certified positive x/y coordinates.  Negative y and the sign delta are derived
limbwise as affine expressions, matching the width-9 production selector. -/
def main (xTable yTable : Nat → Nat)
    (b : Var (fields 12) Field) : Circuit Field (Var AffPoint Field) := do
  let w ← ProvableType.witness (α := fields 11) fun env =>
    Vector.ofFn fun i : Fin 11 => xVal env b i.val (by omega)
  Circuit.forEach (Vector.ofFn fun i : Fin 11 =>
    b[11] * (2 : Field) * b[i.val]'(by omega)
      - (w[i.val]'i.isLt + b[11] + b[i.val]'(by omega) - 1)) assertZero
  let blk ← ProvableType.witness (α := fields 5) fun env =>
    Vector.ofFn fun p : Fin 5 => xVal env b (pairLo p.val) (pairLo_lt p.isLt) *
      xVal env b (pairLo p.val + 1) (pairLo_add_lt p.isLt)
  Circuit.forEach (Vector.ofFn fun p : Fin 5 =>
    xExpr b w (pairLo p.val) (pairLo_lt p.isLt) *
    xExpr b w (pairLo p.val + 1) (pairLo_add_lt p.isLt) - blk[p.val]'p.isLt) assertZero
  let inner4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 0 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 0 (by decide) (j.val % 3) *
    innerP b w blk 1 (by decide) (j.val / 3) - inner4w[j.val]'j.isLt) assertZero
  let inner4 := hot4Vec b w blk 0 (by decide) inner4w
  let inner6w ← ProvableType.witness (α := fields 45) fun env =>
    Vector.ofFn fun j : Fin 45 => hot6Val env b (16 * (j.val / 15) + j.val % 15)
  Circuit.forEach (Vector.ofFn fun j : Fin 45 =>
    hot4 blk inner4 0 (by omega) (j.val % 15) (by omega) *
    innerP b w blk 2 (by decide) (j.val / 15) - inner6w[j.val]'j.isLt) assertZero
  let inner6 := inner6Vec b w blk inner6w
  let inner7w ← ProvableType.witness (α := fields 63) fun env =>
    Vector.ofFn fun j : Fin 63 => hot6Val env b j.val * xVal env b 6 (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 63 =>
    hot6 blk inner4 inner6 j.val (by omega) * xExpr b w 6 (by omega) - inner7w[j.val]'j.isLt) assertZero
  let inner7 := inner7Vec b w inner7w
  let outer4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 3 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 3 (by decide) (j.val % 3) *
    innerP b w blk 4 (by decide) (j.val / 3) - outer4w[j.val]'j.isLt) assertZero
  let outer4 := hot4Vec b w blk 3 (by decide) outer4w
  let xProd ← ProvableType.witness (α := fields 32) fun env =>
    Vector.ofFn fun k : Fin 32 => outProdVal env b (k.val/8) (k.val % 8) xTable
  Circuit.forEach (Vector.ofFn fun k : Fin 32 =>
    (hot4 blk outer4 3 (by omega) (2 * (k.val % 8)) (by omega) +
        inner (k.val/8) (2 * (k.val % 8) + 1) blk inner4 inner6 inner7 xTable) *
      (hot4 blk outer4 3 (by omega) (2 * (k.val % 8) + 1) (by omega) +
        inner (k.val/8) (2 * (k.val % 8)) blk inner4 inner6 inner7 xTable)
      - (corrC (k.val/8) (2 * (k.val % 8)) (2 * (k.val % 8) + 1)
            blk inner4 inner6 inner7 xTable
          + xProd[k.val]'k.isLt)) assertZero
  let yNeg ← ProvableType.witness (α := fields 32) fun env =>
    Vector.ofFn fun k : Fin 32 =>
      outProdVal env b (k.val/8) (k.val % 8) (fun j => P256 - yTable j)
  Circuit.forEach (Vector.ofFn fun k : Fin 32 =>
    (hot4 blk outer4 3 (by omega) (2 * (k.val % 8)) (by omega) +
        inner (k.val/8) (2 * (k.val % 8) + 1) blk inner4 inner6 inner7
          (fun j => P256 - yTable j)) *
      (hot4 blk outer4 3 (by omega) (2 * (k.val % 8) + 1) (by omega) +
        inner (k.val/8) (2 * (k.val % 8)) blk inner4 inner6 inner7
          (fun j => P256 - yTable j))
      - (corrC (k.val/8) (2 * (k.val % 8)) (2 * (k.val % 8) + 1)
            blk inner4 inner6 inner7 (fun j => P256 - yTable j)
          + yNeg[k.val]'k.isLt)) assertZero
  let y ← ProvableType.witness (α := Emu) fun env =>
    Vector.ofFn fun i : Fin 4 => bitVal env b 11 (by omega) * deltaValE env b i.val yTable + selectedVal2 env b i.val (fun j => P256 - yTable j)
  Circuit.forEach (Vector.ofFn fun i : Fin 4 =>
    b[11] * deltaExpr i.val i.isLt blk inner4 inner6 inner7 yNeg yTable +
      selected2 i.val i.isLt blk inner4 inner6 inner7 yNeg
        (fun j => P256 - yTable j) - y[i.val]'i.isLt) assertZero
  return {x := xSelExpr xTable blk inner4 inner6 inner7 xProd, y := y}

def ChannelsFree {α : Type} (c : Circuit Field α) : Prop :=
  ∀ n, (c.operations n).ChannelsLawful [] []

namespace ChannelsFree

theorem pure {α : Type} (a : α) : ChannelsFree (pure a : Circuit Field α) := by
  intro n
  simpa only [Circuit.pure_operations_eq] using
    (Operations.channelsLawful_nil (F := Field))

theorem bind {α β : Type} {f : Circuit Field α} {g : α → Circuit Field β}
    (hf : ChannelsFree f) (hg : ∀ a, ChannelsFree (g a)) : ChannelsFree (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq]
  simpa using Operations.channelsLawful_append_of_channelsLawful
    (hf n) (hg _ (n + f.localLength n))

theorem provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment Field → α Field) :
    ChannelsFree (ProvableType.witness compute) := by
  intro n
  change Operations.ChannelsLawful ([.witness (ProvableType.size α) _] : Operations Field) [] []
  simp only [Operations.ChannelsLawful, circuit_norm]

theorem assertZero (e : Expression Field) : ChannelsFree (Circuit.assertZero e) := by
  intro n
  change Operations.ChannelsLawful ([.assert e] : Operations Field) [] []
  simp only [Operations.ChannelsLawful, circuit_norm]

theorem lawful_flatten_ofFn {m : ℕ} (g : Fin m → Operations Field)
    (h : ∀ i, (g i).ChannelsLawful [] []) :
    Operations.ChannelsLawful (List.ofFn g).flatten [] [] := by
  induction m with
  | zero => simpa [List.ofFn_zero] using (Operations.channelsLawful_nil (F := Field))
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons]
      simpa using Operations.channelsLawful_append_of_channelsLawful
        (h 0) (ih (fun i => g i.succ) (fun i => h i.succ))

theorem forEach {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit Field Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ a, ChannelsFree (body a)) :
    ChannelsFree (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact lawful_flatten_ofFn _ (fun i => h _ _)

end ChannelsFree

private theorem channelsFree_main (xt yt : Nat → Nat)
    (b : Var (fields 12) Field) : ChannelsFree (main xt yt b) := by
  unfold main
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  exact ChannelsFree.pure _

/-- The selected x-coordinate, as it appears at a concrete offset: a pure affine
expression in the selector's own witnesses, never materialized. -/
def dummyBits : Var (fields 12) Field := Vector.ofFn fun _ : Fin 12 => (0 : Expression Field)

/-- `hot4Vec` does not read the input bits (`xExpr` ignores them), so the choice
of bit vector is irrelevant. -/
theorem hot4Vec_bits_irrel (b b' : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    hot4Vec b w blk p hp h = hot4Vec b' w blk p hp h := rfl

theorem inner6Vec_bits_irrel (b b' : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) :
    inner6Vec b w blk h = inner6Vec b' w blk h := rfl

theorem inner7Vec_bits_irrel (b b' : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field) :
    inner7Vec b w h = inner7Vec b' w h := rfl

def outXAt (xt : Nat → Nat) (i0 : Nat) : Var Emu Field :=
  xSelExpr xt (varFromOffset (fields 5) (i0 + 11))
    (hot4Vec dummyBits (varFromOffset (fields 11) i0) (varFromOffset (fields 5) (i0 + 11)) 0
      (by decide) (varFromOffset (fields 9) (i0 + 16)))
    (inner6Vec dummyBits (varFromOffset (fields 11) i0) (varFromOffset (fields 5) (i0 + 11))
      (varFromOffset (fields 45) (i0 + 25)))
    (inner7Vec dummyBits (varFromOffset (fields 11) i0) (varFromOffset (fields 63) (i0 + 70)))
    (varFromOffset (fields 32) (i0 + 142))

instance elaborated (xt yt : Nat → Nat) :
    ElaboratedCircuit Field (fields 12) AffPoint (main xt yt) where
  localLength _ := 210
  output _ i0 :=
    { x := outXAt xt i0,
      y := varFromOffset Emu (i0 + 206) }
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm, numLimbs]
  output_eq := by
    intro input offset
    simp +arith only [main, outXAt, circuit_norm, numLimbs]
    rw [hot4Vec_bits_irrel input dummyBits, inner6Vec_bits_irrel input dummyBits,
      inner7Vec_bits_irrel input dummyBits]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, numLimbs]
  channelsLawful := by
    exact channelsFree_main xt yt

def Assumptions (b : fields 12 Field) : Prop := ∀ i : Fin 12, IsBool b[i]

def Spec (xTable yTable : Nat → Nat) (b : fields 12 Field)
    (out : AffPoint Field) : Prop :=
  out.x = Vector.ofFn (fun i : Fin 4 =>
      ((limbOfNat (xTable (magnitudeIndex b)) i.val : Nat) : Field)) ∧
  out.y = Vector.ofFn (fun i : Fin 4 =>
      (b[11].val : Field) *
          (((limbOfNat (yTable (magnitudeIndex b)) i.val : Nat) : Field) -
           ((limbOfNat (P256 - yTable (magnitudeIndex b)) i.val : Nat) : Field)) +
       ((limbOfNat (P256 - yTable (magnitudeIndex b)) i.val : Nat) : Field))

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 6400000 in
theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent Field) (xt yt : Nat → Nat)
    (b : Var (fields 12) Field) (n : Nat)
    (hb : ∀ (k : Nat) (env env' : ProverEnvironment Field), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      ∀ (j : Nat) (hj : j < 12),
        Expression.eval env.toEnvironment (b[j]'hj) =
          Expression.eval env'.toEnvironment (b[j]'hj))
    (env env' : ProverEnvironment Field) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main xt yt b).operations n) := by
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true, implies_true]
  and_intros
  all_goals first
    | trivial
    | (intro hagree hpin
       try simp only [circuit_norm] at hagree
       have hbit := hb _ env env' (by omega) hagree hpin
       apply Vector.ext; intro i hi
       simp only [Vector.getElem_ofFn, bitVal, xVal, pairVal, hot4Val, hot6Val,
         hot7Val, innerVal, corrVal, outProdVal, selectedVal2, deltaValE, hbit])

end ComputableWitness

end Select12
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase.Select12
open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affineW_dummyBits : AffineW dummyBits := by
  intro i hi
  rw [dummyBits, Vector.getElem_ofFn]
  exact Affine.const _

theorem affine_xExpr (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (hw : AffineW w) (i : Nat) (hi : i < 11) : Affine (xExpr b w i hi) := by
  unfold xExpr
  exact hw i hi

theorem affine_pairExpr {x y xy : Expression Field} (hx : Affine x) (hy : Affine y)
    (hxy : Affine xy) (v : Nat) : Affine (pairExpr x y xy v) := by
  unfold pairExpr
  split_ifs
  · exact Affine.add (Affine.sub (Affine.sub (Affine.const 1) hx) hy) hxy
  · exact Affine.sub hx hxy
  · exact Affine.sub hy hxy
  · exact hxy

theorem affine_ofFn_foldl_add {n : Nat} (g : Fin n → Expression Field)
    (hg : ∀ i, Affine (g i)) : Affine ((Vector.ofFn g).foldl (·+·) 0) := by
  have hof : Vector.ofFn g = Vector.map g (Vector.finRange n) := by
    apply Vector.ext; intro i hi
    rw [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_finRange]
  rw [hof, Vector.foldl_map, vector_foldl_finRange]
  exact affine_finFoldl' _ _ Affine.zero fun acc i hacc => Affine.add hacc (hg i)

theorem affine_innerP (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk)
    (p : Nat) (hp : p < 5) (u : Nat) : Affine (innerP b w blk p hp u) := by
  unfold innerP
  exact affine_pairExpr (affine_xExpr _ _ hw _ (pairLo_lt hp))
    (affine_xExpr _ _ hw _ (pairLo_add_lt hp)) (hblk p hp) u

theorem affine_hot4gen {P0 P1 : Nat → Expression Field} {h : Var (fields 9) Field}
    (hP0 : ∀ u, Affine (P0 u)) (hP1 : ∀ u, Affine (P1 u)) (hh : AffineW h) (v : Nat) :
    Affine (hot4gen P0 P1 h v) := by
  unfold hot4gen
  split
  · split
    · exact hh _ (by omega)
    · exact Affine.sub (Affine.sub (Affine.sub (hP0 _) (hh _ (by omega))) (hh _ (by omega)))
        (hh _ (by omega))
  · split
    · exact Affine.sub (Affine.sub (Affine.sub (hP1 _) (hh _ (by omega))) (hh _ (by omega)))
        (hh _ (by omega))
    · exact Affine.zero

theorem affineW_hot4Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field)
    (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk) (hh : AffineW h) :
    AffineW (hot4Vec b w blk p hp h) := by
  intro v hv
  rw [hot4Vec, Vector.getElem_ofFn]
  exact affine_hot4gen (fun u => affine_innerP b w blk hb hw hblk p (by omega) u)
    (fun u => affine_innerP b w blk hb hw hblk (p+1) (by omega) u) hh v

theorem affineW_inner6Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field)
    (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk) (hh : AffineW h) :
    AffineW (inner6Vec b w blk h) := by
  intro v hv
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split
  · exact hh _ (by omega)
  · exact Affine.sub (affine_innerP b w blk hb hw hblk 2 (by decide) _)
      (affine_ofFn_foldl_add _ fun a => hh _ (by omega))

theorem affineW_inner7Vec (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field)
    (hb : AffineW b) (hw : AffineW w) (hh : AffineW h) :
    AffineW (inner7Vec b w h) := by
  intro v hv
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split
  · exact hh _ (by omega)
  · exact Affine.sub (affine_xExpr _ _ hw 6 (by decide))
      (affine_ofFn_foldl_add _ fun a => hh _ a.isLt)

theorem affine_hot4 {blk : Var (fields 5) Field} {h : Var (fields 15) Field}
    (hb : AffineW blk) (hh : AffineW h) (p : Nat) (hp : p < 4) (v : Nat) (hv : v < 16) :
    Affine (hot4 blk h p hp v hv) := by
  unfold hot4
  split
  · exact Affine.sub (Affine.sub (Affine.sub (hb (p+1) (by omega)) (hh 12 (by omega)))
      (hh 13 (by omega))) (hh 14 (by omega))
  · exact hh v (by omega)

theorem affine_hot6 {blk : Var (fields 5) Field} {h4 : Var (fields 15) Field}
    {h6 : Var (fields 48) Field} (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (v : Nat) (hv : v < 64) : Affine (hot6 blk h4 h6 v hv) := by
  unfold hot6
  dsimp only
  split
  · exact hh6 _ (by omega)
  · exact Affine.sub (Affine.sub (Affine.sub (affine_hot4 hb hh4 0 (by omega) _ (by omega))
      (hh6 _ (by omega))) (hh6 _ (by omega))) (hh6 _ (by omega))

theorem affine_hot7 {blk : Var (fields 5) Field} {h4 : Var (fields 15) Field}
    {h6 : Var (fields 48) Field} {h7 : Var (fields 64) Field}
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7)
    (v : Nat) (hv : v < 128) : Affine (hot7 blk h4 h6 h7 v hv) := by
  unfold hot7
  dsimp only
  split
  · exact hh7 _ (by omega)
  · exact Affine.sub (affine_hot6 hb hh4 hh6 _ (by omega)) (hh7 _ (by omega))

theorem affine_inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat)
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7) :
    Affine (inner limb outer blk h4 h6 h7 table) := by
  unfold inner
  exact affine_ofFn_foldl_add _ fun a =>
    Affine.mul_deg0 (affine_hot7 hb hh4 hh6 hh7 a.val a.isLt) (by simp [degree])

theorem affine_corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat)
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7) :
    Affine (corrC limb o0 o1 blk h4 h6 h7 table) := by
  unfold corrC
  exact affine_ofFn_foldl_add _ fun a =>
    Affine.mul_deg0 (affine_hot7 hb hh4 hh6 hh7 a.val a.isLt) (by simp [degree])

theorem affine_selected (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hp : AffineW prod) :
    Affine (selected limb hl blk h4 h6 h7 prod table) := by
  unfold selected
  exact Affine.add (affine_inner _ _ _ _ _ _ _ hb hh4 hh6 hh7)
    (affine_ofFn_foldl_add _ fun q => hp _ (by omega))

theorem affine_zsel (limb : Nat) (hl : limb < 4) (c : Nat) (hc : c < 4)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hpA : AffineW pA) :
    Affine (zsel limb hl c hc blk h4 h6 h7 pA table) := by
  unfold zsel
  exact affine_ofFn_foldl_add _ fun t => hpA _ (by have := t.isLt; omega)

theorem affine_selected2 (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hpA : AffineW pA) :
    Affine (selected2 limb hl blk h4 h6 h7 pA table) := by
  unfold selected2
  exact affine_ofFn_foldl_add _ fun k => hpA _ (by have := k.isLt; omega)

theorem affineW_xSelExpr (table : Nat → Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (hb : AffineW blk)
    (hh4 : AffineW h4)
    (hh6 : AffineW h6) (hh7 : AffineW h7) (hpA : AffineW pA) :
    AffineW (xSelExpr table blk h4 h6 h7 pA) := by
  intro i hi
  rw [xSelExpr_get]
  exact affine_selected2 i hi blk h4 h6 h7 pA table hb hh4 hh6 hh7 hpA

theorem affine_deltaInner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat)
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7) :
    Affine (deltaInner limb outer blk h4 h6 h7 table) := by
  unfold deltaInner
  exact Affine.sub (affine_inner _ _ _ _ _ _ _ hb hh4 hh6 hh7)
    (affine_inner _ _ _ _ _ _ _ hb hh4 hh6 hh7)

theorem affine_selectedDelta (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hp : AffineW prod) :
    Affine (selectedDelta limb hl blk h4 h6 h7 prod table) := by
  unfold selectedDelta
  exact Affine.add (affine_deltaInner _ _ _ _ _ _ _ hb hh4 hh6 hh7)
    (affine_ofFn_foldl_add _ fun q => hp _ (by omega))

theorem affine_selectedE (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 15) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hp : AffineW prod) :
    Affine (selectedE blk h4 h6 h7 prod table) := by
  unfold selectedE
  exact Affine.add (affine_inner _ _ _ _ _ _ _ hb hh4 hh6 hh7)
    (affine_ofFn_foldl_add _ fun q => hp _ q.isLt)

theorem affine_bExpr (limb : Nat) (sel : Expression Field) (bits : Var (fields 2) Field)
    (hsel : Affine sel) (hbits : AffineW bits) :
    Affine (bExpr limb sel bits) := by
  unfold bExpr
  split
  · exact Affine.sub (Affine.sub hsel (Affine.mul_fconst _ (hbits 0 (by omega))))
      (Affine.mul_fconst _ (hbits 1 (by omega)))
  · split
    · exact hbits 0 (by omega)
    · split
      · exact hbits 1 (by omega)
      · exact Affine.zero

theorem affine_deltaExpr (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (negA : Var (fields 32) Field)
    (yTable : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hnA : AffineW negA) :
    Affine (deltaExpr limb hl blk h4 h6 h7 negA yTable) := by
  unfold deltaExpr
  exact Affine.sub (Affine.const _)
    (Affine.mul_fconst _ (affine_selected2 _ _ _ _ _ _ _ _ hb hh4 hh6 hh7 hnA))

def selectCost : Count := ⟨210, 210⟩

set_option maxHeartbeats 4000000 in
theorem costIs_main (xt yt : Nat → Nat) (b : Var (fields 12) Field) :
    CostIs (main xt yt b) selectCost := by
  rw [show selectCost = ⟨11,0⟩ + (⟨0,11⟩ + (⟨5,0⟩ + (⟨0,5⟩ + (⟨9,0⟩ +
    (⟨0,9⟩ + (⟨45,0⟩ + (⟨0,45⟩ + (⟨63,0⟩ + (⟨0,63⟩ + (⟨9,0⟩ + (⟨0,9⟩ +
    (⟨32,0⟩ + (⟨0,32⟩ + (⟨32,0⟩ + (⟨0,32⟩ +
    (⟨4,0⟩ + (⟨0,4⟩ + (Count.zero))))))))))))))))))
    from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  exact CostIs.pure _

end Solution.Secp256k1ScalarMulFixedBase.Select12

end DonorFile5_9

-- Adapted donor module: SelectTheorems
section DonorFile5_10

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace Select

set_option maxRecDepth 2048
set_option maxHeartbeats 12800000

lemma eval_foldl_add (env : Environment (F circomPrime)) (n : ℕ)
    (f : Fin n → Expression (F circomPrime)) :
    Expression.eval env (Vector.foldl (· + ·) 0 (Vector.ofFn f))
      = ∑ j : Fin n, Expression.eval env (f j) := by
  have h1 : ∀ (l : List (Expression (F circomPrime))) (acc : Expression (F circomPrime)),
      Expression.eval env (l.foldl (· + ·) acc)
        = l.foldl (fun x e => x + Expression.eval env e) (Expression.eval env acc) := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons hd tl ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih (acc + hd)]
      rfl
  have h2 : Vector.foldl (· + ·) (0 : Expression (F circomPrime)) (Vector.ofFn f)
      = (Vector.ofFn f).toList.foldl (· + ·) 0 := by
    rcases h : Vector.ofFn f with ⟨xs, hxs⟩
    simp [Vector.foldl_mk, Array.foldl_toList, Vector.toList]
  rw [h2, Vector.toList_ofFn, h1]
  have h3 : ∀ (l : List (Expression (F circomPrime))) (acc : F circomPrime),
      l.foldl (fun x e => x + Expression.eval env e) acc
        = acc + (l.map (Expression.eval env)).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons hd tl ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      ring
  rw [show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl, h3,
    zero_add, ← List.ofFn_comp', List.sum_ofFn]

lemma one_hot_sum (n : ℕ) (c : Fin n → F circomPrime) (idx : ℕ) (hidx : idx < n)
    (e : Fin n → F circomPrime)
    (he : ∀ j : Fin n, e j = (((if j.val = idx then 1 else 0) : ℕ) : F circomPrime)) :
    (∑ j : Fin n, e j * c j) = c ⟨idx, hidx⟩ := by
  rw [Finset.sum_eq_single ⟨idx, hidx⟩]
  · rw [he ⟨idx, hidx⟩, if_pos rfl]
    norm_num
  · intro j _ hj
    rw [he j, if_neg (fun h => hj (Fin.ext h))]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma one_hot_sum_affine (n : ℕ) (c : ℕ → F circomPrime) (idx : ℕ) (hidx : idx < n + 1)
    (e : Fin n → F circomPrime)
    (he : ∀ j : Fin n, e j = (((if j.val = idx then 1 else 0) : ℕ) : F circomPrime)) :
    (∑ j : Fin n, e j * (c j.val - c n)) + c n = c idx := by
  by_cases h : idx = n
  · have hz : ∀ j : Fin n, e j = 0 := by
      intro j
      rw [he j, if_neg (by omega)]
      norm_num
    rw [Finset.sum_eq_zero (fun j _ => by rw [hz j]; ring), zero_add, h]
  · have hidx' : idx < n := by omega
    rw [Finset.sum_eq_single (⟨idx, hidx'⟩ : Fin n)]
    · rw [he ⟨idx, hidx'⟩, if_pos rfl]
      push_cast
      ring
    · intro j _ hj
      rw [he j, if_neg (fun hh => hj (Fin.ext hh))]
      ring
    · intro hc
      exact absurd (Finset.mem_univ _) hc

def blockF (x y wb : F circomPrime) (v : ℕ) : F circomPrime :=
  if v = 0 then 1 - x - y + wb else if v = 1 then x - wb else if v = 2 then y - wb else wb

lemma eval_blockExpr (env : Environment (F circomPrime))
    (x y wb : Expression (F circomPrime)) (v : ℕ) :
    Expression.eval env (blockExpr x y wb v)
      = blockF (Expression.eval env x) (Expression.eval env y)
          (Expression.eval env wb) v := by
  rw [blockExpr, blockF]
  split_ifs <;> simp [circuit_norm] <;> ring


lemma xnor_val {a b : F circomPrime} (ha : IsBool a) (hb : IsBool b) :
    (a * b) * 2 - a - b + 1
      = (((if b.val = a.val then 1 else 0) : ℕ) : F circomPrime) := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
    norm_num [ZMod.val_zero, ZMod.val_one]

lemma blockF_ind (x0N x1N : ℕ) (h0 : x0N ≤ 1) (h1 : x1N ≤ 1) (u : ℕ) (hu : u < 4) :
    blockF ((x0N : ℕ) : F circomPrime) ((x1N : ℕ) : F circomPrime)
        ((x0N * x1N : ℕ) : F circomPrime) u
      = (((if x0N + 2 * x1N = u then 1 else 0) : ℕ) : F circomPrime) := by
  interval_cases x0N <;> interval_cases x1N <;> interval_cases u <;> norm_num [blockF]

lemma sign_factor (x u : ℕ) (hx : x ≤ 1) (hu : u ≤ 1) :
    (if u = 1 then ((x : ℕ) : F circomPrime) else 1 - ((x : ℕ) : F circomPrime))
      = (((if x = u then 1 else 0) : ℕ) : F circomPrime) := by
  interval_cases x <;> interval_cases u <;> norm_num

lemma ind_mul_ind (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) * (if q then 1 else 0) : ℕ) = if p ∧ q then 1 else 0 := by
  split_ifs with h1 h2 h3 h4 <;> first | rfl | tauto

/-- Product-of-indicators, folded into a single indicator via a supplied `iff`. Used to combine
`hA`'s and `hB`'s (possibly row/column-remainder-derived) one-hot values into `e`'s one-hot
value without depending on how the individual `env.get`/`Expression.eval` chains happened to be
associated by prior simp calls. -/
lemma ind_indicator_mul_eq {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (hpqr : r ↔ (p ∧ q)) :
    (((if p then 1 else 0 : ℕ) : F circomPrime)) * (((if q then 1 else 0 : ℕ) : F circomPrime))
      = (((if r then 1 else 0 : ℕ) : F circomPrime)) := by
  rw [← Nat.cast_mul, ind_mul_ind, if_congr hpqr.symm rfl rfl]

lemma IsBool.val_le_one {x : F circomPrime} (h : IsBool x) : x.val ≤ 1 := by
  rcases h with h | h <;> rw [h]
  · rw [ZMod.val_zero]; omega
  · rw [ZMod.val_one]


/-- The row-3 affine remainder identity for a 4-bit block pair: the row selector value
(`x2N * x3N`) minus the three witnessed row-3 indicators sums to the fourth. Pure ring/case
identity over booleans, independent of soundness/completeness direction. Serves both `hA`
(bits 0–3 via `blk[1]`) and `hB` (bits 4–7 via `blk[3]`). -/
lemma hB_remainder (x0N x1N x2N x3N : ℕ) (h0 : x0N ≤ 1) (h1 : x1N ≤ 1)
    (h2 : x2N ≤ 1) (h3 : x3N ≤ 1) :
    ((x0N * x1N : ℕ) : F circomPrime)
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 3 then 1 else 0 : ℕ) : F circomPrime))
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 7 then 1 else 0 : ℕ) : F circomPrime))
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 11 then 1 else 0 : ℕ) : F circomPrime))
    = (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 15 then 1 else 0 : ℕ) : F circomPrime)) := by
  interval_cases x0N <;> interval_cases x1N <;> interval_cases x2N <;> interval_cases x3N <;>
    norm_num

lemma h14_remainder (x0N x1N x2N x3N : ℕ) (h0 : x0N ≤ 1) (h1 : x1N ≤ 1)
    (h2 : x2N ≤ 1) (h3 : x3N ≤ 1) :
    ((x2N * x3N : ℕ) : F circomPrime)
      - (((if x0N + 2*x1N + 4*x2N + 8*x3N = 12 then 1 else 0 : ℕ) : F circomPrime))
      - (((if x0N + 2*x1N + 4*x2N + 8*x3N = 13 then 1 else 0 : ℕ) : F circomPrime))
      - (((x0N*x1N : ℕ) : F circomPrime)
          - (((if x0N + 2*x1N + 4*x2N + 8*x3N = 3 then 1 else 0 : ℕ) : F circomPrime))
          - (((if x0N + 2*x1N + 4*x2N + 8*x3N = 7 then 1 else 0 : ℕ) : F circomPrime))
          - (((if x0N + 2*x1N + 4*x2N + 8*x3N = 11 then 1 else 0 : ℕ) : F circomPrime)))
    = (((if x0N + 2*x1N + 4*x2N + 8*x3N = 14 then 1 else 0 : ℕ) : F circomPrime)) := by
  interval_cases x0N <;> interval_cases x1N <;> interval_cases x2N <;> interval_cases x3N <;>
    norm_num

lemma hA_remainder (x0N x1N x2N x3N : ℕ) (h0 : x0N ≤ 1) (h1 : x1N ≤ 1) (h2 : x2N ≤ 1)
    (h3 : x3N ≤ 1) :
    ((x2N * x3N : ℕ) : F circomPrime)
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 12 then 1 else 0 : ℕ) : F circomPrime))
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 13 then 1 else 0 : ℕ) : F circomPrime))
      - (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 14 then 1 else 0 : ℕ) : F circomPrime))
    = (((if x0N + 2 * x1N + 4 * x2N + 8 * x3N = 15 then 1 else 0 : ℕ) : F circomPrime)) := by
  interval_cases x0N <;> interval_cases x1N <;> interval_cases x2N <;> interval_cases x3N <;>
    norm_num

end Select
end Solution.Secp256k1ScalarMulFixedBase



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

def xNbit (b : fields 12 Field) (i : Nat) (hi : i < 11) : Nat :=
  if b[i].val = b[11].val then 1 else 0

/-- The six low magnitude bits (0..5); the base for the inner one-hot. -/
def inner6Index (b : fields 12 Field) : Nat :=
  xNbit b 0 (by omega) + 2*xNbit b 1 (by omega) + 4*xNbit b 2 (by omega) +
  8*xNbit b 3 (by omega) + 16*xNbit b 4 (by omega) + 32*xNbit b 5 (by omega)

/-- The seven low magnitude bits (0..6); the full inner index. -/
def innerIndex (b : fields 12 Field) : Nat :=
  inner6Index b + 64*xNbit b 6 (by omega)

/-- The four high magnitude bits (7..10); the outer index. -/
def outerIndex (b : fields 12 Field) : Nat :=
  xNbit b 7 (by omega) + 2*xNbit b 8 (by omega) + 4*xNbit b 9 (by omega) +
  8*xNbit b 10 (by omega)

def transformedIndex (b : fields 12 Field) : Nat :=
  xNbit b 0 (by omega) + 2*xNbit b 1 (by omega) + 4*xNbit b 2 (by omega) +
  8*xNbit b 3 (by omega) + 16*xNbit b 4 (by omega) + 32*xNbit b 5 (by omega) +
  64*xNbit b 6 (by omega) + 128*xNbit b 7 (by omega) + 256*xNbit b 8 (by omega) +
  512*xNbit b 9 (by omega) + 1024*xNbit b 10 (by omega)

lemma xNbit_le (b : fields 12 Field) (i : Nat) (hi : i < 11) : xNbit b i hi ≤ 1 := by
  unfold xNbit
  split <;> omega

lemma transformedIndex_lt (b : fields 12 Field) : transformedIndex b < 2048 := by
  unfold transformedIndex
  have h0 := xNbit_le b 0 (by omega); have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega); have h3 := xNbit_le b 3 (by omega)
  have h4 := xNbit_le b 4 (by omega); have h5 := xNbit_le b 5 (by omega)
  have h6 := xNbit_le b 6 (by omega); have h7 := xNbit_le b 7 (by omega)
  have h8 := xNbit_le b 8 (by omega); have h9 := xNbit_le b 9 (by omega)
  have h10 := xNbit_le b 10 (by omega)
  omega

lemma inner6Index_lt (b : fields 12 Field) : inner6Index b < 64 := by
  unfold inner6Index
  have h0 := xNbit_le b 0 (by omega); have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega); have h3 := xNbit_le b 3 (by omega)
  have h4 := xNbit_le b 4 (by omega); have h5 := xNbit_le b 5 (by omega)
  omega

lemma innerIndex_lt (b : fields 12 Field) : innerIndex b < 128 := by
  unfold innerIndex
  have h6 := xNbit_le b 6 (by omega)
  have h := inner6Index_lt b
  omega

lemma outerIndex_lt (b : fields 12 Field) : outerIndex b < 16 := by
  unfold outerIndex
  have h7 := xNbit_le b 7 (by omega); have h8 := xNbit_le b 8 (by omega)
  have h9 := xNbit_le b 9 (by omega); have h10 := xNbit_le b 10 (by omega)
  omega

/-- The full inner/outer split reconstructs the transformed index. -/
lemma index_split (b : fields 12 Field) :
    128 * outerIndex b + innerIndex b = transformedIndex b := by
  unfold transformedIndex innerIndex inner6Index outerIndex
  ring

lemma transformedIndex_eq_sign_zero (b : fields 12 Field)
    (hb : ∀ i : Fin 12, IsBool b[i]) (hs : b[11] = 0) :
    transformedIndex b = 2047 - bitsVal b := by
  have hle : ∀ (j : Nat) (hj : j < 12), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have hz : ∀ x : Nat, x ≤ 1 → (if x = 0 then 1 else 0) = 1-x := by
    intro x hx; split <;> omega
  have hsval : b[11].val = 0 := by simpa using congrArg ZMod.val hs
  unfold transformedIndex xNbit
  rw [hsval]
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  have h10 := hle 10 (by omega)
  rw [hz _ h0, hz _ h1, hz _ h2, hz _ h3, hz _ h4, hz _ h5,
    hz _ h6, hz _ h7, hz _ h8, hz _ h9, hz _ h10, bitsVal, hsval]
  omega

lemma transformedIndex_eq_sign_one (b : fields 12 Field)
    (hb : ∀ i : Fin 12, IsBool b[i]) (hs : b[11] = 1) :
    transformedIndex b = bitsVal b - 2048 := by
  have hle : ∀ (j : Nat) (hj : j < 12), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have ho : ∀ x : Nat, x ≤ 1 → (if x = 1 then 1 else 0) = x := by
    intro x hx; split <;> omega
  have hsval : b[11].val = 1 := by simpa using congrArg ZMod.val hs
  unfold transformedIndex xNbit
  rw [hsval]
  rw [ho _ (hle 0 (by omega)), ho _ (hle 1 (by omega)), ho _ (hle 2 (by omega)),
    ho _ (hle 3 (by omega)), ho _ (hle 4 (by omega)), ho _ (hle 5 (by omega)),
    ho _ (hle 6 (by omega)), ho _ (hle 7 (by omega)), ho _ (hle 8 (by omega)),
    ho _ (hle 9 (by omega)), ho _ (hle 10 (by omega)), bitsVal, hsval]
  omega

lemma transformedIndex_eq (b : fields 12 Field) (hb : ∀ i : Fin 12, IsBool b[i]) :
    transformedIndex b = magnitudeIndex b := by
  rcases hb ⟨11, by omega⟩ with hs | hs
  · rw [transformedIndex_eq_sign_zero b hb hs, magnitudeIndex]
    have hsval : b[11].val = 0 := by simpa using congrArg ZMod.val hs
    have hle : ∀ (j : Nat) (hj : j < 11), b[j].val ≤ 1 := fun j hj =>
      Select.IsBool.val_le_one (hb ⟨j, by omega⟩)
    have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
    have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
    have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
    have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
    have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
    have h10 := hle 10 (by omega)
    have hlt : bitsVal b < 2048 := by rw [bitsVal, hsval]; omega
    rw [if_neg (by omega)]
  · rw [transformedIndex_eq_sign_one b hb hs, magnitudeIndex]
    have hsval : b[11].val = 1 := by simpa using congrArg ZMod.val hs
    have hge : 2048 ≤ bitsVal b := by rw [bitsVal, hsval]; omega
    rw [if_pos hge]

end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

lemma eval_pairExpr (env : Environment Field) (x y xy : Expression Field) (v : Nat) :
    Expression.eval env (pairExpr x y xy v) =
      Select.blockF (Expression.eval env x) (Expression.eval env y)
        (Expression.eval env xy) v := by
  unfold pairExpr Select.blockF
  split_ifs <;> simp [circuit_norm] <;> ring

/-- Affine derivation of the last pair branch of the six-bit inner one-hot. -/
lemma hot6_indicator_remainder (input : fields 12 Field) (a : Nat) (ha : a < 16) :
    (((if a = inner6Index input % 16 then 1 else 0) : Nat) : Field) -
        (((if a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 16+a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 32+a = inner6Index input then 1 else 0) : Nat) : Field) =
      (((if 48+a = inner6Index input then 1 else 0) : Nat) : Field) := by
  have hi := inner6Index_lt input
  split_ifs <;> norm_num <;> omega

/-- Affine derivation of the bit-6 zero branch of the seven-bit inner one-hot. -/
lemma hot7_indicator_remainder (input : fields 12 Field) (a : Nat) (ha : a < 64) :
    (((if a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 64+a = innerIndex input then 1 else 0) : Nat) : Field) =
      (((if a = innerIndex input then 1 else 0) : Nat) : Field) := by
  have hi := inner6Index_lt input
  have h6 := xNbit_le input 6 (by omega)
  have hInner : innerIndex input = inner6Index input + 64 * xNbit input 6 (by omega) := rfl
  split_ifs <;> norm_num <;> omega

lemma eval_selected_eq (env : Environment Field) (input : fields 12 Field)
    (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (table : Nat → Nat)
    (hinner : ∀ (outer : Nat), Expression.eval env (inner limb outer blk h4 h6 h7 table) =
      ((limbOfNat (table (128*outer + innerIndex input)) limb : Nat) : Field))
    (hprod : ∀ (q : Nat) (hq : q < 15),
      Expression.eval env (prod[limb*15+q]'(by omega)) =
        (((if q = outerIndex input then 1 else 0) : Nat) : Field) *
          (((limbOfNat (table (128*q + innerIndex input)) limb : Nat) : Field) -
           ((limbOfNat (table (128*15 + innerIndex input)) limb : Nat) : Field)))
    (hb : ∀ i : Fin 12, IsBool input[i]) :
  Expression.eval env (selected limb hl blk h4 h6 h7 prod table) =
      ((limbOfNat (table (magnitudeIndex input)) limb : Nat) : Field) := by
  unfold selected
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner 15]
  rw [Finset.sum_congr rfl (fun q _ => hprod q.val q.isLt)]
  have hs := Select.one_hot_sum_affine 15
    (fun q => (((limbOfNat (table (128*q + innerIndex input)) limb : Nat) : Field)))
    (outerIndex input) (outerIndex_lt input)
    (fun q : Fin 15 => (((if q.val = outerIndex input then 1 else 0) : Nat) : Field))
    (fun _ => rfl)
  rw [add_comm, hs]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input hb, ← index_split]
  change ((limbOfNat (table (128 * outerIndex input + innerIndex input)) limb : Nat) : Field) = _
  rw [hindex]

lemma eval_zsel_eq (env : Environment Field) (input : fields 12 Field)
    (limb : Nat) (hl : limb < 4) (c : Nat) (hc : c < 4) (e3 : Nat) (he3 : e3 < 4)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (table : Nat → Nat)
    (hpA : ∀ (t : Nat) (ht : t < 2),
      Expression.eval env (pA[8*limb+2*c+t]'(by omega)) =
        (((if 2*t = e3 then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*t+4*c) + innerIndex input)) limb : Nat) : Field) +
        (((if 2*t+1 = e3 then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*t+1+4*c) + innerIndex input)) limb : Nat) : Field)) :
    Expression.eval env (zsel limb hl c hc blk h4 h6 h7 pA table) =
      ((limbOfNat (table (128*(e3+4*c) + innerIndex input)) limb : Nat) : Field) := by
  unfold zsel
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  rw [Finset.sum_congr rfl (fun t : Fin 2 => fun _ => hpA t.val t.isLt)]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  interval_cases e3 <;> norm_num

lemma sum8_pair_indicator (e : Nat) (he : e < 16) (T : Nat → Field) :
    ∑ k : Fin 8, ((((if 2*k.val = e then 1 else 0) : Nat) : Field) * T (2*k.val) +
      (((if 2*k.val+1 = e then 1 else 0) : Nat) : Field) * T (2*k.val+1)) = T e := by
  rw [Fin.sum_univ_eight]
  interval_cases e <;> norm_num

lemma eval_selected2_eq (env : Environment Field) (input : fields 12 Field)
    (limb : Nat) (hl : limb < 4) (e : Nat) (he : e < 16)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (table : Nat → Nat)
    (hpA : ∀ (k : Nat) (hk : k < 8),
      Expression.eval env (pA[8*limb+k]'(by omega)) =
        (((if 2*k = e then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*k) + innerIndex input)) limb : Nat) : Field) +
        (((if 2*k+1 = e then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*k+1) + innerIndex input)) limb : Nat) : Field))
    (hb : ∀ i : Fin 12, IsBool input[i])
    (hidx : e = outerIndex input) :
    Expression.eval env (selected2 limb hl blk h4 h6 h7 pA table) =
      ((limbOfNat (table (magnitudeIndex input)) limb : Nat) : Field) := by
  unfold selected2
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  rw [Finset.sum_congr rfl (fun k : Fin 8 => fun _ => hpA k.val k.isLt)]
  rw [sum8_pair_indicator e he
    (fun j => ((limbOfNat (table (128*j + innerIndex input)) limb : Nat) : Field))]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input hb, ← index_split]
  rw [hidx, hindex]

lemma eval_selectedE_eq (env : Environment Field) (input : fields 12 Field)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 15) Field) (table : Nat -> Nat)
    (hinner : ∀ (outer : Nat), Expression.eval env (inner 0 outer blk h4 h6 h7 table) =
      ((limbOfNat (table (128*outer + innerIndex input)) 0 : Nat) : Field))
    (hprod : ∀ (q : Nat) (hq : q < 15),
      Expression.eval env (prod[q]'hq) =
        (((if q = outerIndex input then 1 else 0) : Nat) : Field) *
          (((limbOfNat (table (128*q + innerIndex input)) 0 : Nat) : Field) -
           ((limbOfNat (table (128*15 + innerIndex input)) 0 : Nat) : Field)))
    (hb : ∀ i : Fin 12, IsBool input[i]) :
  Expression.eval env (selectedE blk h4 h6 h7 prod table) =
      ((limbOfNat (table (magnitudeIndex input)) 0 : Nat) : Field) := by
  unfold selectedE
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner 15]
  rw [Finset.sum_congr rfl (fun q _ => hprod q.val q.isLt)]
  have hs := Select.one_hot_sum_affine 15
    (fun q => (((limbOfNat (table (128*q + innerIndex input)) 0 : Nat) : Field)))
    (outerIndex input) (outerIndex_lt input)
    (fun q : Fin 15 => (((if q.val = outerIndex input then 1 else 0) : Nat) : Field))
    (fun _ => rfl)
  rw [add_comm, hs]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input hb, ← index_split]
  change ((limbOfNat (table (128 * outerIndex input + innerIndex input)) 0 : Nat) : Field) = _
  rw [hindex]

lemma eval_selectedDelta_eq (env : Environment Field) (input : fields 12 Field)
    (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (yTable : Nat → Nat)
    (hinner : ∀ outer, Expression.eval env (deltaInner limb outer blk h4 h6 h7 yTable) =
      yDeltaLimb yTable (128*outer + innerIndex input) limb)
    (hprod : ∀ (q : Nat) (hq : q < 15),
      Expression.eval env (prod[limb*15+q]'(by omega)) =
      (((if q = outerIndex input then 1 else 0) : Nat) : Field) *
        (yDeltaLimb yTable (128*q + innerIndex input) limb -
         yDeltaLimb yTable (128*15 + innerIndex input) limb))
    (hb : ∀ i : Fin 12, IsBool input[i]) :
    Expression.eval env (selectedDelta limb hl blk h4 h6 h7 prod yTable) =
      yDeltaLimb yTable (magnitudeIndex input) limb := by
  unfold selectedDelta
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner 15]
  rw [Finset.sum_congr rfl (fun q _ => hprod q.val q.isLt)]
  have hs := Select.one_hot_sum_affine 15
    (fun q => yDeltaLimb yTable (128*q + innerIndex input) limb)
    (outerIndex input) (outerIndex_lt input)
    (fun q : Fin 15 => (((if q.val = outerIndex input then 1 else 0) : Nat) : Field))
    (fun _ => rfl)
  rw [add_comm, hs]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input hb, ← index_split]
  change yDeltaLimb yTable (128 * outerIndex input + innerIndex input) limb = _
  rw [hindex]

end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

lemma pairVal_sum (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (p : Nat) (hp : p < 5) :
    pairVal env b p 0 hp + pairVal env b p 1 hp + pairVal env b p 2 hp
      + pairVal env b p 3 hp = 1 := by
  unfold pairVal
  norm_num
  ring


lemma sum_ind_off (n off I : Nat) :
    (∑ a : Fin n, (((if off + a.val = I then 1 else 0) : Nat) : Field))
      = (((if off ≤ I ∧ I < off + n then 1 else 0) : Nat) : Field) := by
  by_cases hI : off ≤ I ∧ I < off + n
  · obtain ⟨hI1, hI2⟩ := hI
    rw [if_pos ⟨hI1, hI2⟩, Finset.sum_eq_single (⟨I - off, by omega⟩ : Fin n)]
    · show (((if off + (I - off) = I then 1 else 0) : Nat) : Field) = _
      rw [if_pos (by omega)]
    · intro j _ hj
      have hjl := j.isLt
      have hne : ¬ (off + j.val = I) := by
        intro hh
        exact hj (Fin.ext (show j.val = I - off by omega))
      rw [if_neg hne]
      norm_num
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · rw [if_neg hI]
    have hI' : ∀ m : Nat, m < n → ¬ (off + m = I) := by
      intro m hm hh
      exact hI ⟨by omega, by omega⟩
    have hz : ∀ j : Fin n, (((if off + j.val = I then 1 else 0) : Nat) : Field) = 0 := by
      intro j
      rw [if_neg (hI' j.val j.isLt)]
      norm_num
    simp only [hz, Finset.sum_const_zero]
    norm_num

/-- Indicator value of every used cell of a nine-product 4x4 one-hot. -/
lemma eval_hot4gen_ind (env : Environment Field) (P0 P1 : Nat → Expression Field)
    (h : Var (fields 9) Field) (A C : Nat) (hA : A < 4) (hC : C < 4)
    (hP0 : ∀ (a : Nat), a < 4 → Expression.eval env (P0 a) =
      (((if A = a then 1 else 0) : Nat) : Field))
    (hP1 : ∀ (c : Nat), c < 4 → Expression.eval env (P1 c) =
      (((if C = c then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 9), Expression.eval env (h[j]'hj) =
      (((if j % 3 + 4 * (j / 3) = A + 4 * C then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 15) :
    Expression.eval env (hot4gen P0 P1 h v) =
      (((if v = A + 4 * C then 1 else 0) : Nat) : Field) := by
  unfold hot4gen
  by_cases ha : v % 4 < 3 <;> by_cases hc : v / 4 < 3
  · rw [dif_pos ha, dif_pos hc, hh (v % 4 + 3 * (v / 4)) (by omega)]
    have a1 : (v % 4 + 3 * (v / 4)) % 3 = v % 4 := by omega
    have a2 : (v % 4 + 3 * (v / 4)) / 3 = v / 4 := by omega
    rw [a1, a2, show v % 4 + 4 * (v / 4) = v by omega]
  · rw [dif_pos ha, dif_neg hc]
    simp only [circuit_norm]
    rw [hP0 (v % 4) (by omega), hh (v % 4) (by omega), hh (v % 4 + 3) (by omega),
      hh (v % 4 + 6) (by omega)]
    have a1 : (v % 4) % 3 = v % 4 := by omega
    have a2 : (v % 4) / 3 = 0 := by omega
    have a3 : (v % 4 + 3) % 3 = v % 4 := by omega
    have a4 : (v % 4 + 3) / 3 = 1 := by omega
    have a5 : (v % 4 + 6) % 3 = v % 4 := by omega
    have a6 : (v % 4 + 6) / 3 = 2 := by omega
    have hvv : v = v % 4 + 12 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    set a := v % 4 with hadef
    have haa : a < 3 := ha
    rw [hvv]
    clear_value a
    interval_cases A <;> interval_cases C <;> interval_cases a <;> norm_num
  · rw [dif_neg ha, dif_pos hc]
    simp only [circuit_norm]
    rw [hP1 (v / 4) (by omega), hh (3 * (v / 4)) (by omega), hh (3 * (v / 4) + 1) (by omega),
      hh (3 * (v / 4) + 2) (by omega)]
    have a1 : (3 * (v / 4)) % 3 = 0 := by omega
    have a2 : (3 * (v / 4)) / 3 = v / 4 := by omega
    have a3 : (3 * (v / 4) + 1) % 3 = 1 := by omega
    have a4 : (3 * (v / 4) + 1) / 3 = v / 4 := by omega
    have a5 : (3 * (v / 4) + 2) % 3 = 2 := by omega
    have a6 : (3 * (v / 4) + 2) / 3 = v / 4 := by omega
    have hvv : v = 3 + 4 * (v / 4) := by omega
    rw [a1, a2, a3, a4, a5, a6]
    set c := v / 4 with hcdef
    have hcc : c < 3 := hc
    rw [hvv]
    clear_value c
    interval_cases A <;> interval_cases C <;> interval_cases c <;> norm_num
  · exfalso; omega

/-- Indicator value of every cell of the forty-five-product six-bit one-hot. -/
lemma eval_inner6Vec_ind (env : Environment Field)
    (b : Var (fields 12) Field) (w : Var (fields 11) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 45) Field) (I : Nat) (hI : I < 64)
    (hP2 : ∀ (c : Nat), c < 4 → Expression.eval env (innerP b w blk 2 (by decide) c) =
      (((if I / 16 = c then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 45), Expression.eval env (h[j]'hj) =
      (((if 16 * (j / 15) + j % 15 = I then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 48) :
    Expression.eval env ((inner6Vec b w blk h)[v]'hv) =
      (((if v = I then 1 else 0) : Nat) : Field) := by
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · rw [hh (15 * (v / 16) + v % 16) (by omega)]
    have d1 : (15 * (v / 16) + v % 16) / 15 = v / 16 := by omega
    have d2 : (15 * (v / 16) + v % 16) % 15 = v % 16 := by omega
    rw [d1, d2, show 16 * (v / 16) + v % 16 = v by omega]
  · have hterm : ∀ a : Fin 15,
        Expression.eval env (h[15 * (v / 16) + a.val]'(by have := a.isLt; omega)) =
          (((if 16 * (v / 16) + a.val = I then 1 else 0) : Nat) : Field) := by
      intro a
      have ha := a.isLt
      rw [hh (15 * (v / 16) + a.val) (by omega)]
      have d1 : (15 * (v / 16) + a.val) / 15 = v / 16 := by omega
      have d2 : (15 * (v / 16) + a.val) % 15 = a.val := by omega
      rw [d1, d2]
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hP2 (v / 16) (by omega), sum_ind_off 15 (16 * (v / 16)) I]
    have hv16 : v = 16 * (v / 16) + 15 := by omega
    rw [hv16]
    set c := v / 16 with hcdef
    clear_value c
    split_ifs <;> norm_num <;> omega

/-- Indicator value of every cell of the sixty-three-product bit-6 layer. -/
lemma eval_inner7Vec_ind (env : Environment Field)
    (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field) (I : Nat) (hI : I < 128)
    (hx6 : Expression.eval env (xExpr b w 6 (by decide)) =
      (((if 64 ≤ I then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 63), Expression.eval env (h[j]'hj) =
      (((if 64 + j = I then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 64) :
    Expression.eval env ((inner7Vec b w h)[v]'hv) =
      (((if 64 + v = I then 1 else 0) : Nat) : Field) := by
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 63,
        Expression.eval env (h[a.val]'a.isLt) =
          (((if 64 + a.val = I then 1 else 0) : Nat) : Field) := fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx6, sum_ind_off 63 64 I, show v = 63 by omega]
    split_ifs <;> norm_num <;> omega


/-- Prover-side value of every used cell of a nine-product 4x4 one-hot. -/
lemma eval_hot4gen_val (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field)
    (p : Nat) (hp : p < 4)
    (hP0 : ∀ (a : Nat), a < 4 → Expression.eval env.toEnvironment (P0 a) =
      pairVal env b p a (by omega))
    (hP1 : ∀ (c : Nat), c < 4 → Expression.eval env.toEnvironment (P1 c) =
      pairVal env b (p+1) c (by omega))
    (hh : ∀ (j : Nat) (hj : j < 9), Expression.eval env.toEnvironment (h[j]'hj) =
      hot4Val env b p (j % 3 + 4 * (j / 3)) (by omega))
    (v : Nat) (hv : v < 15) :
    Expression.eval env.toEnvironment (hot4gen P0 P1 h v) = hot4Val env b p v (by omega) := by
  have hhj : ∀ (j : Nat) (hj : j < 9),
      Expression.eval env.toEnvironment (h[j]'hj) =
        pairVal env b p (j % 3) (by omega) * pairVal env b (p+1) (j / 3) (by omega) := by
    intro j hj
    rw [hh j hj]
    unfold hot4Val
    have h1 : (j % 3 + 4 * (j / 3)) % 4 = j % 3 := by omega
    have h2 : (j % 3 + 4 * (j / 3)) / 4 = j / 3 := by omega
    rw [h1, h2]
  have hsumA := pairVal_sum env b p (by omega)
  have hsumB := pairVal_sum env b (p+1) (by omega)
  unfold hot4gen
  split_ifs with ha hc hc <;> simp only [circuit_norm]
  · rw [hhj (v % 4 + 3 * (v / 4)) (by omega)]
    have a1 : (v % 4 + 3 * (v / 4)) % 3 = v % 4 := by omega
    have a2 : (v % 4 + 3 * (v / 4)) / 3 = v / 4 := by omega
    rw [a1, a2]
    unfold hot4Val
    norm_num
  · rw [hP0 (v % 4) (by omega), hhj (v % 4) (by omega), hhj (v % 4 + 3) (by omega),
      hhj (v % 4 + 6) (by omega)]
    have a1 : (v % 4) % 3 = v % 4 := by omega
    have a2 : (v % 4) / 3 = 0 := by omega
    have a3 : (v % 4 + 3) % 3 = v % 4 := by omega
    have a4 : (v % 4 + 3) / 3 = 1 := by omega
    have a5 : (v % 4 + 6) % 3 = v % 4 := by omega
    have a6 : (v % 4 + 6) / 3 = 2 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    unfold hot4Val
    have hv4 : v / 4 = 3 := by omega
    rw [hv4]
    norm_num
    linear_combination (-(pairVal env b p (v % 4) (by omega))) * hsumB
  · rw [hP1 (v / 4) (by omega), hhj (3 * (v / 4)) (by omega), hhj (3 * (v / 4) + 1) (by omega),
      hhj (3 * (v / 4) + 2) (by omega)]
    have a1 : (3 * (v / 4)) % 3 = 0 := by omega
    have a2 : (3 * (v / 4)) / 3 = v / 4 := by omega
    have a3 : (3 * (v / 4) + 1) % 3 = 1 := by omega
    have a4 : (3 * (v / 4) + 1) / 3 = v / 4 := by omega
    have a5 : (3 * (v / 4) + 2) % 3 = 2 := by omega
    have a6 : (3 * (v / 4) + 2) / 3 = v / 4 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    unfold hot4Val
    have hv4 : v % 4 = 3 := by omega
    rw [hv4]
    norm_num
    linear_combination (-(pairVal env b (p+1) (v / 4) (by omega))) * hsumA
  · exfalso; omega

/-- The sixteen cells of a four-bit one-hot sum to one. -/
lemma hot4Val_sum15 (env : ProverEnvironment Field) (b : Var (fields 12) Field)
    (p : Nat) (hp : p < 4) :
    (∑ a : Fin 15, hot4Val env b p a.val (by omega)) + hot4Val env b p 15 (by omega) = 1 := by
  simp only [hot4Val, pairVal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- The sixty-four cells of the six-bit inner one-hot sum to one. -/
lemma hot6Val_sum63 (env : ProverEnvironment Field) (b : Var (fields 12) Field) :
    (∑ a : Fin 63, hot6Val env b a.val) + hot6Val env b 63 = 1 := by
  simp only [hot6Val, hot4Val, pairVal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- Prover-side value of every cell of the forty-five-product six-bit one-hot. -/
lemma eval_inner6Vec_val (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (w : Var (fields 11) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 45) Field)
    (hP2 : ∀ (c : Nat), c < 4 →
      Expression.eval env.toEnvironment (innerP b w blk 2 (by decide) c) =
        pairVal env b 2 c (by omega))
    (hh : ∀ (j : Nat) (hj : j < 45), Expression.eval env.toEnvironment (h[j]'hj) =
      hot6Val env b (16 * (j / 15) + j % 15))
    (v : Nat) (hv : v < 48) :
    Expression.eval env.toEnvironment ((inner6Vec b w blk h)[v]'hv) = hot6Val env b v := by
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · rw [hh (15 * (v / 16) + v % 16) (by omega)]
    have d1 : (15 * (v / 16) + v % 16) / 15 = v / 16 := by omega
    have d2 : (15 * (v / 16) + v % 16) % 15 = v % 16 := by omega
    rw [d1, d2, show 16 * (v / 16) + v % 16 = v by omega]
  · have hterm : ∀ a : Fin 15,
        Expression.eval env.toEnvironment (h[15 * (v / 16) + a.val]'(by have := a.isLt; omega)) =
          hot4Val env b 0 a.val (by omega) * pairVal env b 2 (v / 16) (by omega) := by
      intro a
      have ha := a.isLt
      rw [hh (15 * (v / 16) + a.val) (by omega)]
      have d1 : (15 * (v / 16) + a.val) / 15 = v / 16 := by omega
      have d2 : (15 * (v / 16) + a.val) % 15 = a.val := by omega
      rw [d1, d2]
      unfold hot6Val
      have e1 : (16 * (v / 16) + a.val) % 16 = a.val := by omega
      have e2 : (16 * (v / 16) + a.val) / 16 = v / 16 := by omega
      rw [e1, e2]
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hP2 (v / 16) (by omega), ← Finset.sum_mul]
    have hs := hot4Val_sum15 env b 0 (by omega)
    have hgoal : hot6Val env b v = hot4Val env b 0 15 (by omega) * pairVal env b 2 (v / 16) (by omega) := by
      unfold hot6Val
      have e1 : v % 16 = 15 := by omega
      rw [e1]
    rw [hgoal]
    linear_combination (-(pairVal env b 2 (v / 16) (by omega))) * hs

/-- Prover-side value of every cell of the sixty-three-product bit-6 layer. -/
lemma eval_inner7Vec_val (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (h : Var (fields 63) Field)
    (hx6 : Expression.eval env.toEnvironment (xExpr b w 6 (by decide)) =
      xVal env b 6 (by decide))
    (hh : ∀ (j : Nat) (hj : j < 63), Expression.eval env.toEnvironment (h[j]'hj) =
      hot6Val env b j * xVal env b 6 (by decide))
    (v : Nat) (hv : v < 64) :
    Expression.eval env.toEnvironment ((inner7Vec b w h)[v]'hv) =
      hot6Val env b v * xVal env b 6 (by decide) := by
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 63,
        Expression.eval env.toEnvironment (h[a.val]'a.isLt) =
          hot6Val env b a.val * xVal env b 6 (by decide) := fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx6, ← Finset.sum_mul, show v = 63 by omega]
    have hs := hot6Val_sum63 env b
    linear_combination (-(xVal env b 6 (by decide))) * hs


end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096

lemma eval_pairExpr_eq_pairVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (w : Var (fields 11) Field)
    (blk : Var (fields 5) Field)
    (hx : ∀ (i : Nat) (hi : i < 11),
      Expression.eval env.toEnvironment (xExpr b w i hi) = xVal env b i hi)
    (hblk : ∀ (p : Nat) (hp : p < 5),
      Expression.eval env.toEnvironment (blk[p]'hp) =
        xVal env b (pairLo p) (pairLo_lt hp) * xVal env b (pairLo p + 1) (pairLo_add_lt hp))
    (p v : Nat) (hp : p < 5) (hv : v < 4) :
    Expression.eval env.toEnvironment
        (pairExpr (xExpr b w (pairLo p) (pairLo_lt hp))
          (xExpr b w (pairLo p + 1) (pairLo_add_lt hp)) blk[p] v) =
      pairVal env b p v hp := by
  interval_cases v <;> norm_num [pairExpr, pairVal] <;> simp only [circuit_norm]
  all_goals try rw [hx (pairLo p) (pairLo_lt hp)]
  all_goals try rw [hx (pairLo p + 1) (pairLo_add_lt hp)]
  all_goals rw [hblk p hp]
  all_goals ring

lemma eval_hot4_eq_hot4Val (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 15) Field) (base : Nat) (hbase : base < 4)
    (hblk : ∀ (p : Nat) (hp : p < 5),
      Expression.eval env.toEnvironment (blk[p]'hp) =
        xVal env b (pairLo p) (pairLo_lt hp) * xVal env b (pairLo p + 1) (pairLo_add_lt hp))
    (hh : ∀ (v : Nat) (hv : v < 15),
      Expression.eval env.toEnvironment (h[v]'hv) = hot4Val env b base v hbase)
    (v : Nat) (hv : v < 16) :
    Expression.eval env.toEnvironment (hot4 blk h base hbase v hv) =
      hot4Val env b base v hbase := by
  unfold hot4
  split
  · subst v
    simp only [Expression.eval, circuit_norm]
    rw [hblk (base+1) (by omega), hh 12 (by omega), hh 13 (by omega), hh 14 (by omega)]
    norm_num [hot4Val, pairVal]
    ring
  · exact hh v (by omega)

lemma eval_hot6_eq_hot6Val (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (hh4 : ∀ (v : Nat) (hv : v < 16),
      Expression.eval env.toEnvironment (hot4 blk h4 0 (by omega) v hv) =
        hot4Val env b 0 v (by omega))
    (hh6 : ∀ (v : Nat) (hv : v < 48),
      Expression.eval env.toEnvironment (h6[v]'hv) = hot6Val env b v)
    (v : Nat) (hv : v < 64) :
    Expression.eval env.toEnvironment (hot6 blk h4 h6 v hv) = hot6Val env b v := by
  unfold hot6
  dsimp only
  split
  · have heq : v / 16 * 16 + v % 16 = v := by omega
    simpa only [heq] using hh6 (v / 16 * 16 + v % 16) (by omega)
  · simp only [Expression.eval, circuit_norm]
    rw [hh4 _ (by omega), hh6 (v%16) (by omega), hh6 (16+v%16) (by omega),
      hh6 (32+v%16) (by omega)]
    have hvq : v / 16 = 3 := by omega
    have he0 : hot6Val env b (v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 0 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he1 : hot6Val env b (16+v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 1 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he2 : hot6Val env b (32+v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 2 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he3 : hot6Val env b v =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 3 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    rw [he0, he1, he2, he3]
    norm_num [pairVal]
    ring

lemma eval_hot7_eq_hot7Val (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hh6 : ∀ (v : Nat) (hv : v < 64),
      Expression.eval env.toEnvironment (hot6 blk h4 h6 v hv) = hot6Val env b v)
    (hh7 : ∀ (a : Nat) (ha : a < 64),
      Expression.eval env.toEnvironment (h7[a]'ha) = hot7Val env b (64+a))
    (v : Nat) (hv : v < 128) :
    Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v := by
  unfold hot7
  dsimp only
  split
  · rw [hh7]
    congr 1
    omega
  · simp only [Expression.eval, circuit_norm]
    rw [hh6 _ (by omega), hh7]
    have hvq : v / 64 = 0 := by omega
    have he0 : hot7Val env b v =
        hot6Val env b (v%64) * (1 - xVal env b 6 (by omega)) := by
      unfold hot7Val
      rw [if_neg (by omega)]
    have he1 : hot7Val env b (64+v%64) =
        hot6Val env b (v%64) * xVal env b 6 (by omega) := by
      unfold hot7Val
      rw [if_pos (by omega)]
      congr 2 <;> omega
    rw [he0, he1]
    ring

lemma eval_inner_eq_innerVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hhot : ∀ (v : Nat) (hv : v < 128),
      Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v)
    (limb outer : Nat) (table : Nat → Nat) :
    Expression.eval env.toEnvironment (inner limb outer blk h4 h6 h7 table) =
      innerVal env b limb outer table := by
  unfold inner innerVal
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Expression.eval]
  rw [hhot a.val a.isLt]

lemma eval_corrC_eq_corrVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hhot : ∀ (v : Nat) (hv : v < 128),
      Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v)
    (limb o0 o1 : Nat) (table : Nat → Nat) :
    Expression.eval env.toEnvironment (corrC limb o0 o1 blk h4 h6 h7 table) =
      corrVal env b limb o0 o1 table := by
  unfold corrC corrVal
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Expression.eval]
  rw [hhot a.val a.isLt]

end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

lemma eval_selected_eq_selectedVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (table : Nat → Nat)
    (hinner : ∀ (limb outer : Nat),
      Expression.eval env.toEnvironment (inner limb outer blk h4 h6 h7 table) =
        innerVal env b limb outer table)
    (hprod : ∀ (k : Nat) (hk : k < 60),
      Expression.eval env.toEnvironment (prod[k]'hk) =
        hot4Val env b 3 (k%15) (by omega) *
          (innerVal env b (k/15) (k%15) table - innerVal env b (k/15) 15 table))
    (limb : Nat) (hlimb : limb < 4) :
    Expression.eval env.toEnvironment
      (selected limb hlimb blk h4 h6 h7 prod table) = selectedVal env b limb table := by
  unfold selected selectedVal
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner limb 15]
  apply congrArg (innerVal env b limb 15 table + ·)
  apply Finset.sum_congr rfl
  intro q _
  rw [hprod (limb*15+q.val) (by omega)]
  have hmod : (limb*15+q.val) % 15 = q.val := by omega
  have hdiv : (limb*15+q.val) / 15 = limb := by omega
  rw [hmod, hdiv]

lemma eval_zsel_eq_zselVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (limb : Nat) (hl : limb < 4) (c : Nat) (hc : c < 4)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (table : Nat → Nat)
    (hpA : ∀ (k : Nat) (hk : k < 32),
      Expression.eval env.toEnvironment (pA[k]'hk) =
        pairProdVal env b (k/8) (k % 8 / 2) (k % 2) table) :
    Expression.eval env.toEnvironment (zsel limb hl c hc blk h4 h6 h7 pA table) =
      zselVal env b limb c table := by
  unfold zsel zselVal
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro t _
  have ht := t.isLt
  rw [hpA (8*limb+2*c+t.val) (by omega)]
  rw [show (8*limb+2*c+t.val) / 8 = limb by omega,
    show (8*limb+2*c+t.val) % 8 / 2 = c by omega,
    show (8*limb+2*c+t.val) % 2 = t.val by omega]

lemma eval_selected2_eq_selectedVal2 (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (limb : Nat) (hl : limb < 4)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 32) Field) (table : Nat → Nat)
    (hpA : ∀ (k : Nat) (hk : k < 32),
      Expression.eval env.toEnvironment (pA[k]'hk) =
        outProdVal env b (k/8) (k % 8) table) :
    Expression.eval env.toEnvironment (selected2 limb hl blk h4 h6 h7 pA table) =
      selectedVal2 env b limb table := by
  unfold selected2 selectedVal2
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro k _
  have hk := k.isLt
  rw [hpA (8*limb+k.val) (by omega)]
  rw [show (8*limb+k.val) / 8 = limb by omega, show (8*limb+k.val) % 8 = k.val by omega]

lemma eval_selectedE_eq_selectedVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 15) Field) (table : Nat -> Nat)
    (hinner : ∀ (limb outer : Nat),
      Expression.eval env.toEnvironment (inner limb outer blk h4 h6 h7 table) =
        innerVal env b limb outer table)
    (hprod : ∀ (k : Nat) (hk : k < 15),
      Expression.eval env.toEnvironment (prod[k]'hk) =
        hot4Val env b 3 k (by omega) *
          (innerVal env b 0 k table - innerVal env b 0 15 table)) :
    Expression.eval env.toEnvironment
      (selectedE blk h4 h6 h7 prod table) = selectedVal env b 0 table := by
  unfold selectedE selectedVal
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner 0 15]
  apply congrArg (innerVal env b 0 15 table + ·)
  apply Finset.sum_congr rfl
  intro q _
  rw [hprod q.val q.isLt]

lemma eval_selectedDelta_eq_selectedDeltaVal (env : ProverEnvironment Field)
    (b : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (prod : Var (fields 60) Field) (yTable : Nat → Nat)
    (hinner : ∀ (limb outer : Nat),
      Expression.eval env.toEnvironment (deltaInner limb outer blk h4 h6 h7 yTable) =
        deltaInnerVal env b limb outer yTable)
    (hprod : ∀ (k : Nat) (hk : k < 60),
      Expression.eval env.toEnvironment (prod[k]'hk) =
        hot4Val env b 3 (k%15) (by omega) *
          (deltaInnerVal env b (k/15) (k%15) yTable -
            deltaInnerVal env b (k/15) 15 yTable))
    (limb : Nat) (hlimb : limb < 4) :
    Expression.eval env.toEnvironment
      (selectedDelta limb hlimb blk h4 h6 h7 prod yTable) =
        selectedDeltaVal env b limb yTable := by
  unfold selectedDelta selectedDeltaVal
  simp only [circuit_norm]
  rw [Select.eval_foldl_add, hinner limb 15]
  apply congrArg (deltaInnerVal env b limb 15 yTable + ·)
  apply Finset.sum_congr rfl
  intro q _
  rw [hprod (limb*15+q.val) (by omega)]
  have hmod : (limb*15+q.val) % 15 = q.val := by omega
  have hdiv : (limb*15+q.val) / 15 = limb := by omega
  rw [hmod, hdiv]

end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase.Select12

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

section ValueOneHot

/-! Value-level one-hot facts: with Boolean inputs the *witness values* computed
by the selector are the expected indicator functions.  These mirror the
constraint-level facts derived inside `soundness`, and are what the completeness
proof needs in order to discharge the borrow-bit rows. -/

variable {env : ProverEnvironment Field} {b : Var (fields 12) Field} {input : fields 12 Field}

lemma xVal_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj)) (i : Nat) (hi : i < 11) :
    xVal env b i hi = ((xNbit input i hi : Nat) : Field) := by
  unfold xVal bitVal
  rw [hin 11 (by omega), hin i (by omega)]
  have h := Select.xnor_val (hb 11 (by omega)) (hb i (by omega))
  simp only [xNbit]
  linear_combination h

lemma pairVal_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj))
    (p v : Nat) (hp : p < 5) (hv : v < 4) :
    pairVal env b p v hp =
      (((if xNbit input (pairLo p) (pairLo_lt hp) +
            2 * xNbit input (pairLo p + 1) (pairLo_add_lt hp) = v then 1 else 0) : Nat) : Field) := by
  unfold pairVal
  simp only
  rw [xVal_ind hin hb (pairLo p) (pairLo_lt hp), xVal_ind hin hb (pairLo p + 1) (pairLo_add_lt hp),
    Select.sign_factor _ (v % 2) (xNbit_le _ _ _) (by omega),
    Select.sign_factor _ (v / 2 % 2) (xNbit_le _ _ _) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input (pairLo p) (pairLo_lt hp)
  have h1 := xNbit_le input (pairLo p + 1) (pairLo_add_lt hp)
  constructor <;> intro hh <;> omega

lemma hot4Val_outer_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj)) (v : Nat) (hv : v < 16) :
    hot4Val env b 3 v (by omega) =
      (((if v = outerIndex input then 1 else 0) : Nat) : Field) := by
  unfold hot4Val
  rw [pairVal_ind hin hb 3 (v % 4) (by omega) (by omega),
    pairVal_ind hin hb 4 (v / 4) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h7 := xNbit_le input 7 (by omega); have h8 := xNbit_le input 8 (by omega)
  have h9 := xNbit_le input 9 (by omega); have h10 := xNbit_le input 10 (by omega)
  simp only [pairLo, Nat.reduceAdd, outerIndex]
  constructor <;> intro hh <;> omega

lemma hot4Val_inner_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj)) (v : Nat) (hv : v < 16) :
    hot4Val env b 0 v (by omega) =
      (((if v = inner6Index input % 16 then 1 else 0) : Nat) : Field) := by
  unfold hot4Val
  rw [pairVal_ind hin hb 0 (v % 4) (by omega) (by omega),
    pairVal_ind hin hb 1 (v / 4) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input 0 (by omega); have h1 := xNbit_le input 1 (by omega)
  have h2 := xNbit_le input 2 (by omega); have h3 := xNbit_le input 3 (by omega)
  have h4 := xNbit_le input 4 (by omega); have h5 := xNbit_le input 5 (by omega)
  simp only [pairLo, Nat.reduceAdd, inner6Index]
  constructor <;> intro hh <;> omega

lemma hot6Val_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj)) (v : Nat) (hv : v < 64) :
    hot6Val env b v = (((if v = inner6Index input then 1 else 0) : Nat) : Field) := by
  unfold hot6Val
  rw [hot4Val_inner_ind hin hb (v % 16) (by omega),
    pairVal_ind hin hb 2 (v / 16) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input 0 (by omega); have h1 := xNbit_le input 1 (by omega)
  have h2 := xNbit_le input 2 (by omega); have h3 := xNbit_le input 3 (by omega)
  have h4 := xNbit_le input 4 (by omega); have h5 := xNbit_le input 5 (by omega)
  simp only [pairLo, Nat.reduceAdd, inner6Index]
  constructor <;> intro hh <;> omega

lemma hot7Val_ind (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj)) (v : Nat) (hv : v < 128) :
    hot7Val env b v = (((if v = innerIndex input then 1 else 0) : Nat) : Field) := by
  unfold hot7Val
  rw [hot6Val_ind hin hb (v % 64) (by omega), xVal_ind hin hb 6 (by omega),
    Select.sign_factor _ (v / 64) (xNbit_le _ _ _) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h6 := xNbit_le input 6 (by omega)
  have hi6 := inner6Index_lt input
  simp only [innerIndex]
  constructor <;> intro hh <;> omega

lemma innerVal_const (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj))
    (limb outer : Nat) (table : Nat -> Nat) :
    innerVal env b limb outer table =
      ((limbOfNat (table (128 * outer + innerIndex input)) limb : Nat) : Field) := by
  unfold innerVal
  rw [Finset.sum_congr rfl (fun a _ => by rw [hot7Val_ind hin hb a.val a.isLt])]
  exact Select.one_hot_sum 128
    (fun a : Fin 128 => (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field)))
    (innerIndex input) (innerIndex_lt input) _ (fun _ => rfl)

lemma selectedVal_const (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 12), IsBool (input[j]'hj))
    (limb : Nat) (table : Nat -> Nat) :
    selectedVal env b limb table =
      ((limbOfNat (table (magnitudeIndex input)) limb : Nat) : Field) := by
  unfold selectedVal
  rw [innerVal_const hin hb limb 15 table]
  rw [Finset.sum_congr rfl (fun q : Fin 15 => fun _ => by
    rw [hot4Val_outer_ind hin hb q.val (by omega), innerVal_const hin hb limb q.val table])]
  have hs := Select.one_hot_sum_affine 15
    (fun q => (((limbOfNat (table (128*q + innerIndex input)) limb : Nat) : Field)))
    (outerIndex input) (outerIndex_lt input)
    (fun q : Fin 15 => (((if q.val = outerIndex input then 1 else 0) : Nat) : Field))
    (fun _ => rfl)
  rw [add_comm, hs]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input (fun i => hb i.val i.isLt), ← index_split]
  change ((limbOfNat (table (128 * outerIndex input + innerIndex input)) limb : Nat) : Field) = _
  rw [hindex]

lemma magIdxOf_eq (hin : ∀ (j : Nat) (hj : j < 12),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj) :
    magIdxOf env b = magnitudeIndex input := by
  unfold magIdxOf
  congr 1
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  exact hin i hi

end ValueOneHot


end Solution.Secp256k1ScalarMulFixedBase.Select12



namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select12


end Select12
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_10

-- Adapted donor module: SelectTopTheorems
section DonorFile5_11

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace SelectTop

open Select (eval_foldl_add one_hot_sum blockF eval_blockExpr xnor_val blockF_ind
  sign_factor ind_mul_ind ind_indicator_mul_eq IsBool.val_le_one)

set_option maxRecDepth 2048
set_option maxHeartbeats 1600000

lemma one_hot_sum_affine7 (c : ℕ → F circomPrime) (idx : ℕ) (hidx : idx < 8)
    (e : Fin 7 → F circomPrime)
    (he : ∀ j : Fin 7, e j = (((if j.val = idx then 1 else 0) : ℕ) : F circomPrime)) :
    (∑ j : Fin 7, e j * (c j.val - c 7)) + c 7 = c idx := by
  by_cases h : idx = 7
  · subst h
    have hz : ∀ j : Fin 7, e j = 0 := by
      intro j
      rw [he j, if_neg (by omega)]
      norm_num
    rw [Finset.sum_eq_zero (fun j _ => by rw [hz j]; ring), zero_add]
  · have hidx' : idx < 7 := by omega
    rw [Finset.sum_eq_single (⟨idx, hidx'⟩ : Fin 7)]
    · rw [he ⟨idx, hidx'⟩, if_pos rfl]
      push_cast
      ring
    · intro j _ hj
      rw [he j, if_neg (fun hh => hj (Fin.ext hh))]
      ring
    · intro hcontra
      exact absurd (Finset.mem_univ _) hcontra

lemma eval_xExpr (env : Environment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (i₀ t : ℕ) (ht : t < 3) :
    Expression.eval env
        (xExpr b (Vector.mapRange 3 fun i => var { index := i₀ + i }) t ht)
      = env.get (i₀ + t) * 2 - Expression.eval env (b[3]'(by omega))
          - Expression.eval env (b[t]'(by omega)) + 1 := by
  simp only [xExpr, circuit_norm, Vector.getElem_mapRange]
  ring

def xNbit (b : fields 4 (F circomPrime)) (t : ℕ) (ht : t < 3) : ℕ :=
  if (b[t]'(by omega)).val = (b[3]'(by omega)).val then 1 else 0

def magIdxN (b : fields 4 (F circomPrime)) : ℕ :=
  xNbit b 0 (by omega) + 2 * xNbit b 1 (by omega) + 4 * xNbit b 2 (by omega)

lemma xNbit_le (b : fields 4 (F circomPrime)) (t : ℕ) (ht : t < 3) :
    xNbit b t ht ≤ 1 := by
  rw [xNbit]
  split <;> omega

lemma magIdxN_lt (b : fields 4 (F circomPrime)) : magIdxN b < 8 := by
  have h0 := xNbit_le b 0 (by omega)
  have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega)
  rw [magIdxN]
  omega

lemma magIdxN_eq (b : fields 4 (F circomPrime)) (hb : ∀ i : Fin 4, IsBool b[i]) :
    magIdxN b = if 8 ≤ bitsVal b then bitsVal b - 8 else 7 - bitsVal b := by
  have hle : ∀ (j : ℕ) (hj : j < 4), (b[j]'hj).val ≤ 1 := fun j hj =>
    IsBool.val_le_one (hb ⟨j, hj⟩)
  have h0 := hle 0 (by omega)
  have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega)
  have h3 := hle 3 (by omega)
  have hzero : ∀ x : ℕ, x ≤ 1 → (if x = 0 then (1 : ℕ) else 0) = 1 - x := by
    intro x hx
    split <;> omega
  have hone : ∀ x : ℕ, x ≤ 1 → (if x = 1 then (1 : ℕ) else 0) = x := by
    intro x hx
    split <;> omega
  rw [magIdxN, bitsVal]
  simp only [xNbit]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h3 with h | h <;> rw [h]
  · rw [hzero _ h0, hzero _ h1, hzero _ h2, if_neg (by omega)]
    omega
  · rw [hone _ h0, hone _ h1, hone _ h2, if_pos (by omega)]
    omega

theorem soundness :
    Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hw, hblk, he⟩ := h_holds
  obtain ⟨h_assumptions, h_sign⟩ := h_assumptions
  have hin : ∀ (j : ℕ) (hj : j < 4),
      Expression.eval env (input_var[j]'hj) = input[j]'hj := by
    intro j hj
    rw [← h_input, Vector.getElem_map]
  have hbool : ∀ (j : ℕ) (hj : j < 4), IsBool (input[j]'hj) := fun j hj =>
    h_assumptions ⟨j, hj⟩

  have hwc : ∀ (t : ℕ) (ht : t < 3),
      env.get (i₀ + t) = input[3]'(by omega) * input[t]'(by omega) := by
    intro t ht
    have h := hw ⟨t, ht⟩
    simp only [Vector.getElem_ofFn, circuit_norm] at h
    rw [hin 3 (by omega), hin t (by omega)] at h
    linear_combination -h

  have hxv : ∀ (t : ℕ) (ht : t < 3),
      Expression.eval env
          (xExpr input_var (Vector.mapRange 3 fun i => var { index := i₀ + i }) t ht)
        = ((xNbit input t ht : ℕ) : F circomPrime) := by
    intro t ht
    rw [eval_xExpr env input_var i₀ t ht, hin 3 (by omega), hin t (by omega), hwc t ht]
    simp only [xNbit]
    exact xnor_val (hbool 3 (by omega)) (hbool t (by omega))

  have hblkc :
      env.get (i₀ + 3 + 3 * 0)
        = ((xNbit input 0 (by omega) * xNbit input 1 (by omega) : ℕ) : F circomPrime) := by
    have h := hblk ⟨0, by omega⟩
    simp only [Vector.getElem_ofFn, circuit_norm] at h
    rw [hxv 0 (by omega), hxv 1 (by omega)] at h
    push_cast
    linear_combination -h

  have hec : ∀ (j : ℕ) (hj : j < 7),
      env.get (i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j)
        = (((if j = magIdxN input then 1 else 0) : ℕ) : F circomPrime) := by
    intro j hj
    have h := he ⟨j, hj⟩
    simp only [Vector.getElem_ofFn, circuit_norm] at h
    rw [eval_blockExpr, hxv 0 (by omega), hxv 1 (by omega)] at h
    simp only [circuit_norm] at h
    rw [apply_ite (Expression.eval env)] at h
    simp only [circuit_norm] at h
    rw [hxv 2 (by omega)] at h
    have e0 : env.get (i₀ + 3 + 3 * 0)
        = ((xNbit input 0 (by omega) * xNbit input 1 (by omega) : ℕ) : F circomPrime) := hblkc
    rw [show i₀ + 3 + 3 * 0 + 0 = i₀ + 3 + 3 * 0 from by omega] at *
    rw [e0,
      blockF_ind _ _ (xNbit_le input 0 (by omega)) (xNbit_le input 1 (by omega)) (j % 4)
        (by omega)] at h
    have hsgn : (if j / 4 = 1
          then ((xNbit input 2 (by omega) : ℕ) : F circomPrime)
          else 1 + -((xNbit input 2 (by omega) : ℕ) : F circomPrime))
        = (((if xNbit input 2 (by omega) = j / 4 then 1 else 0) : ℕ) : F circomPrime) := by
      rw [show (1 + -((xNbit input 2 (by omega) : ℕ) : F circomPrime))
          = 1 - ((xNbit input 2 (by omega) : ℕ) : F circomPrime) from by ring]
      exact sign_factor _ _ (xNbit_le input 2 (by omega)) (by omega)
    rw [hsgn] at h
    have hx0 := xNbit_le input 0 (by omega)
    have hx1 := xNbit_le input 1 (by omega)
    have hx2 := xNbit_le input 2 (by omega)
    have hiff : (xNbit input 0 (by omega) + 2 * xNbit input 1 (by omega) = j % 4)
          ∧ (xNbit input 2 (by omega) = j / 4)
        ↔ (j = magIdxN input) := by
      rw [magIdxN]
      constructor
      · intro hh
        omega
      · intro hh
        constructor <;> omega
    rw [← if_congr hiff rfl rfl, ← ind_mul_ind]
    push_cast at h ⊢
    linear_combination -h

  have hxSelc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env
        ((xSelExpr (Vector.mapRange 7 fun j => var { index := i₀ + 4 + j }))[i]'hi)
        = ((limbOfNat (Tables.magXNat (28 * 256 + magIdxN input)) i : ℕ) : F circomPrime) := by
    intro i hi
    unfold xSelExpr Select.weightedSum
    rw [Vector.getElem_ofFn]
    simp only [circuit_norm]
    rw [eval_foldl_add]
    have hterm : ∀ j : Fin 7,
        Expression.eval env
          (var { index := i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val }
            * Expression.const (xCoeff ⟨i, hi⟩ j))
        = (((if j.val = magIdxN input then 1 else 0) : ℕ) : F circomPrime)
            * xCoeff ⟨i, hi⟩ j := by
      intro j
      simp only [circuit_norm]
      rw [hec j.val j.isLt]
    have hidx : ∀ j : Fin 7, i₀ + 4 + j.val = i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val := by
      intro j
      omega
    rw [show (∑ j : Fin 7,
          Expression.eval env (var (F := F circomPrime) { index := i₀ + 4 + j.val }
            * Expression.const (xCoeff ⟨i, hi⟩ j)))
        = ∑ j : Fin 7,
          Expression.eval env (var (F := F circomPrime)
              { index := i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val }
            * Expression.const (xCoeff ⟨i, hi⟩ j))
      from Finset.sum_congr rfl fun j _ => by rw [hidx j]]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    simpa only [xCoeff, xBase] using one_hot_sum_affine7
      (fun k => ((limbOfNat (Tables.magXNat (28 * 256 + k)) i : ℕ) : F circomPrime))
      (magIdxN input) (magIdxN_lt input) _ (fun j => rfl)
  have hySelc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env
        ((ySelExpr (Vector.mapRange 7 fun j => var { index := i₀ + 4 + j }))[i]'hi)
        = ((limbOfNat (Tables.magYNat (28 * 256 + magIdxN input)) i : ℕ) : F circomPrime) := by
    intro i hi
    unfold ySelExpr Select.weightedSum
    rw [Vector.getElem_ofFn]
    simp only [circuit_norm]
    rw [eval_foldl_add]
    have hterm : ∀ j : Fin 7,
        Expression.eval env
          (var { index := i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val }
            * Expression.const (yCoeff ⟨i, hi⟩ j))
        = (((if j.val = magIdxN input then 1 else 0) : ℕ) : F circomPrime)
            * yCoeff ⟨i, hi⟩ j := by
      intro j
      simp only [circuit_norm]
      rw [hec j.val j.isLt]
    have hidx : ∀ j : Fin 7, i₀ + 4 + j.val = i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val := by
      intro j
      omega
    rw [show (∑ j : Fin 7,
          Expression.eval env (var (F := F circomPrime) { index := i₀ + 4 + j.val }
            * Expression.const (yCoeff ⟨i, hi⟩ j)))
        = ∑ j : Fin 7,
          Expression.eval env (var (F := F circomPrime)
              { index := i₀ + 3 + 3 * 0 + 1 + 1 * 0 + j.val }
            * Expression.const (yCoeff ⟨i, hi⟩ j))
      from Finset.sum_congr rfl fun j _ => by rw [hidx j]]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    simpa only [yCoeff, yBase] using one_hot_sum_affine7
      (fun k => ((limbOfNat (Tables.magYNat (28 * 256 + k)) i : ℕ) : F circomPrime))
      (magIdxN input) (magIdxN_lt input) _ (fun j => rfl)

  have hmag := magIdxN_eq input h_assumptions
  have hvle : ∀ (j : ℕ) (hj : j < 4), (input[j]'hj).val ≤ 1 := fun j hj =>
    IsBool.val_le_one (hbool j hj)
  have h8 : 8 ≤ bitsVal input := by
    have hb3 : (input[3]'(by omega)).val = 1 := by rw [h_sign, ZMod.val_one]
    rw [bitsVal]
    omega
  refine ⟨?_, ?_⟩
  · apply Vector.ext
    intro k hk
    rw [Vector.getElem_map]
    change Expression.eval env
      ((xSelExpr (Vector.mapRange 7 fun j => var { index := i₀ + 4 + j }))[k]'hk) = _
    rw [hxSelc k hk, emuOfNat_getElem _ k hk, sigXNat, hmag]
  · apply Vector.ext
    intro k hk
    rw [Vector.getElem_map]
    change Expression.eval env
      ((ySelExpr (Vector.mapRange 7 fun j => var { index := i₀ + 4 + j }))[k]'hk) = _
    rw [hySelc k hk, emuOfNat_getElem _ k hk, sigYNat, if_pos h8, hmag, if_pos h8]

lemma blockVal_ind (env : ProverEnvironment (F circomPrime))
    (b : Var (fields 4) (F circomPrime)) (input : fields 4 (F circomPrime))
    (h_input : Vector.map (Expression.eval env.toEnvironment) b = input)
    (hb : ∀ i : Fin 4, IsBool input[i])
    (v : ℕ) (hv : v < 4) :
    blockVal env b v
      = (((if xNbit input 0 (by omega) + 2 * xNbit input 1 (by omega) = v
           then 1 else 0) : ℕ) : F circomPrime) := by
  have hin : ∀ (j : ℕ) (hj : j < 4),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj := by
    intro j hj
    rw [← h_input, Vector.getElem_map]
  have hbool : ∀ (j : ℕ) (hj : j < 4), IsBool (input[j]'hj) := fun j hj => hb ⟨j, hj⟩
  have hxvv : ∀ (u : ℕ) (hu : u < 3),
      xVal env b u hu = ((xNbit input u hu : ℕ) : F circomPrime) := by
    intro u hu
    rw [xVal, bitVal, bitVal, hin 3 (by omega), hin u (by omega)]
    simp only [xNbit]
    linear_combination xnor_val (hbool 3 (by omega)) (hbool u (by omega))
  rw [blockVal, hxvv 0 (by omega), hxvv 1 (by omega),
    sign_factor _ (v % 2) (xNbit_le input 0 (by omega)) (by omega),
    sign_factor _ (v / 2 % 2) (xNbit_le input 1 (by omega)) (by omega),
    ← Nat.cast_mul, ind_mul_ind]
  have hxt := xNbit_le input 0 (by omega)
  have hxt1 := xNbit_le input 1 (by omega)
  have hiff : ((xNbit input 0 (by omega) = v % 2 ∧ xNbit input 1 (by omega) = v / 2 % 2))
      ↔ (xNbit input 0 (by omega) + 2 * xNbit input 1 (by omega) = v) := by
    constructor
    · intro hh
      omega
    · intro hh
      constructor <;> omega
  rw [if_congr hiff rfl rfl]

theorem completeness :
    Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨hwE, hblkE, -, heE, -⟩ := h_env
  obtain ⟨h_assumptions, -⟩ := h_assumptions
  have hin : ∀ (j : ℕ) (hj : j < 4),
      Expression.eval env.toEnvironment (input_var[j]'hj) = input[j]'hj := by
    intro j hj
    rw [← h_input, Vector.getElem_map]
  have hbool : ∀ (j : ℕ) (hj : j < 4), IsBool (input[j]'hj) := fun j hj =>
    h_assumptions ⟨j, hj⟩
  have hbit : ∀ (t : ℕ) (ht : t < 4), bitVal env input_var t ht = input[t]'ht := by
    intro t ht
    rw [bitVal, hin t ht]

  have hwc : ∀ (t : ℕ) (ht : t < 3),
      env.get (i₀ + t) = input[3]'(by omega) * input[t]'(by omega) := by
    intro t ht
    have h := hwE ⟨t, ht⟩
    rw [Vector.getElem_ofFn] at h
    rw [h, hbit 3 (by omega), hbit t (by omega)]
  have hxvv : ∀ (u : ℕ) (hu : u < 3),
      xVal env input_var u hu = ((xNbit input u hu : ℕ) : F circomPrime) := by
    intro u hu
    rw [xVal, bitVal, bitVal, hin 3 (by omega), hin u (by omega)]
    simp only [xNbit]
    linear_combination xnor_val (hbool 3 (by omega)) (hbool u (by omega))
  have hxe : ∀ (t : ℕ) (ht : t < 3),
      Expression.eval env.toEnvironment
          (xExpr input_var (Vector.mapRange 3 fun i => var { index := i₀ + i }) t ht)
        = ((xNbit input t ht : ℕ) : F circomPrime) := by
    intro t ht
    rw [eval_xExpr env.toEnvironment input_var i₀ t ht, hin 3 (by omega), hin t (by omega),
      hwc t ht]
    simp only [xNbit]
    exact xnor_val (hbool 3 (by omega)) (hbool t (by omega))
  have hblkc :
      env.get (i₀ + 3 + 3 * 0)
        = ((xNbit input 0 (by omega) * xNbit input 1 (by omega) : ℕ) : F circomPrime) := by
    have h := hblkE ⟨0, by omega⟩
    rw [Vector.getElem_ofFn] at h
    rw [show i₀ + 3 + 3 * 0 = 3 * 0 + (i₀ + 3) from by omega, h,
      hxvv 0 (by omega), hxvv 1 (by omega)]
    push_cast
    ring
  have hec : ∀ (j : ℕ) (hj : j < 7),
      env.get (i₀ + 3 + 3 * 0 + 1 + j)
        = (((if j = magIdxN input then 1 else 0) : ℕ) : F circomPrime) := by
    intro j hj
    have h := heE ⟨j, hj⟩
    simp only [Vector.getElem_ofFn] at h
    rw [show i₀ + 3 + 3 * 0 + 1 + j
        = 3 * 0 + (i₀ + 3) + 1 + j from by omega,
      h, blockVal_ind env input_var input h_input h_assumptions (j % 4) (by omega),
      hxvv 2 (by omega),
      sign_factor _ (j / 4) (xNbit_le input 2 (by omega)) (by omega),
      ← Nat.cast_mul, ind_mul_ind]
    have hx0 := xNbit_le input 0 (by omega)
    have hx1 := xNbit_le input 1 (by omega)
    have hx2 := xNbit_le input 2 (by omega)
    have hiff : ((xNbit input 0 (by omega) + 2 * xNbit input 1 (by omega) = j % 4)
          ∧ (xNbit input 2 (by omega) = j / 4))
        ↔ (j = magIdxN input) := by
      rw [magIdxN]
      constructor
      · intro hh
        omega
      · intro hh
        constructor <;> omega
    rw [if_congr hiff rfl rfl]

  have hmval : mVal env input_var = bitsVal input := by
    rw [mVal, bitsVal, hbit 0 (by omega), hbit 1 (by omega), hbit 2 (by omega),
      hbit 3 (by omega)]
  have hmag := magIdxN_eq input h_assumptions
  have hvle : ∀ (j : ℕ) (hj : j < 4), (input[j]'hj).val ≤ 1 := fun j hj =>
    IsBool.val_le_one (hbool j hj)

  refine ⟨?_, ?_, ?_⟩
  ·
    intro i
    simp only [Vector.getElem_ofFn, circuit_norm]
    rw [hin 3 (by omega), hin i.val (by omega), hwc i.val i.isLt]
    ring
  ·
    intro i
    simp only [Vector.getElem_ofFn, circuit_norm]
    rw [hxe 0 (by omega), hxe 1 (by omega), hblkc]
    push_cast
    ring
  ·
    intro j
    simp only [Vector.getElem_ofFn, circuit_norm]
    rw [eval_blockExpr, hxe 0 (by omega), hxe 1 (by omega)]
    simp only [circuit_norm]
    rw [apply_ite (Expression.eval env.toEnvironment)]
    simp only [circuit_norm]
    rw [hxe 2 (by omega)]
    rw [hec j.val j.isLt, hblkc,
      blockF_ind _ _ (xNbit_le input 0 (by omega)) (xNbit_le input 1 (by omega)) (j.val % 4)
        (by omega)]
    have hsgn : (if j.val / 4 = 1
          then ((xNbit input 2 (by omega) : ℕ) : F circomPrime)
          else 1 + -((xNbit input 2 (by omega) : ℕ) : F circomPrime))
        = (((if xNbit input 2 (by omega) = j.val / 4 then 1 else 0) : ℕ) : F circomPrime) := by
      rw [show (1 + -((xNbit input 2 (by omega) : ℕ) : F circomPrime))
          = 1 - ((xNbit input 2 (by omega) : ℕ) : F circomPrime) from by ring]
      exact sign_factor _ _ (xNbit_le input 2 (by omega)) (by omega)
    rw [hsgn, ← Nat.cast_mul, ind_mul_ind]
    have hx0 := xNbit_le input 0 (by omega)
    have hx1 := xNbit_le input 1 (by omega)
    have hx2 := xNbit_le input 2 (by omega)
    have hiff : ((xNbit input 0 (by omega) + 2 * xNbit input 1 (by omega) = j.val % 4)
          ∧ (xNbit input 2 (by omega) = j.val / 4))
        ↔ (j.val = magIdxN input) := by
      rw [magIdxN]
      constructor
      · intro hh
        omega
      · intro hh
        constructor <;> omega
    rw [if_congr hiff rfl rfl]
    ring

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectTheorems.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

/-- Möbius interpolation agrees with its table on the Boolean hypercube. -/
theorem lookupValue_bool (table : Nat → Field) (b0 b1 b2 selector : Field)
    (h0 : IsBool b0) (h1 : IsBool b1) (h2 : IsBool b2)
    (hs : IsBool selector) :
    lookupValue table b0 b1 b2 selector =
      table (b0.val + 2 * b1.val + 4 * b2.val + 8 * selector.val) := by
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases hs with hs | hs <;>
    simp [h0, h1, h2, hs, ZMod.val_zero, ZMod.val_one,
      lookupValue, coeff] <;> ring

theorem soundness : Soundness Field main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbits, hselector⟩ := h_input
  have hin : ∀ (j : Nat) (hj : j < 3),
      Expression.eval env (input_var_bits[j]'hj) = input_bits[j]'hj := by
    intro j hj
    rw [← hbits, Vector.getElem_map]

  have hw0 : env.get i₀ = input_bits[0] * input_bits[1] := by
    have h := h_holds ⟨0, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 0 (by omega), hin 1 (by omega)] at h
    linear_combination -h
  have hw1 : env.get (i₀ + 1) = input_bits[0] * input_bits[2] := by
    have h := h_holds ⟨1, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 0 (by omega), hin 2 (by omega)] at h
    linear_combination -h
  have hw2 : env.get (i₀ + 2) = input_bits[0] * input_selector := by
    have h := h_holds ⟨2, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 0 (by omega), hselector] at h
    linear_combination -h
  have hw3 : env.get (i₀ + 3) = input_bits[1] * input_bits[2] := by
    have h := h_holds ⟨3, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 1 (by omega), hin 2 (by omega)] at h
    linear_combination -h
  have hw4 : env.get (i₀ + 4) = input_bits[1] * input_selector := by
    have h := h_holds ⟨4, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 1 (by omega), hselector] at h
    linear_combination -h
  have hw5 : env.get (i₀ + 5) = input_bits[2] * input_selector := by
    have h := h_holds ⟨5, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hin 2 (by omega), hselector] at h
    linear_combination -h
  have hw6 : env.get (i₀ + 6) = input_bits[0] * input_bits[1] * input_bits[2] := by
    have h := h_holds ⟨6, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hw0, hin 2 (by omega)] at h
    linear_combination -h
  have hw7 : env.get (i₀ + 7) = input_bits[0] * input_bits[1] * input_selector := by
    have h := h_holds ⟨7, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hw0, hselector] at h
    linear_combination -h
  have hw8 : env.get (i₀ + 8) = input_bits[0] * input_bits[2] * input_selector := by
    have h := h_holds ⟨8, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hw1, hselector] at h
    linear_combination -h
  have hw9 : env.get (i₀ + 9) = input_bits[1] * input_bits[2] * input_selector := by
    have h := h_holds ⟨9, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hw3, hselector] at h
    linear_combination -h
  have hw10 : env.get (i₀ + 10) =
      input_bits[0] * input_bits[1] * input_bits[2] * input_selector := by
    have h := h_holds ⟨10, by decide⟩
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm] at h
    rw [hw6, hselector] at h
    linear_combination -h

  constructor
  · apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    rw [outputExpr, Vector.getElem_ofFn]
    change Expression.eval env
      (lookupExpr (xTable ⟨i, hi⟩)
        { bits := input_var_bits, selector := input_var_selector }
        (Vector.mapRange 11 fun j => var { index := i₀ + j })) =
      lookupValue (xTable ⟨i, hi⟩) input_bits[0] input_bits[1] input_bits[2]
        input_selector
    simp only [lookupExpr, lookupValue, circuit_norm]
    rw [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hselector,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10]
  · apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    rw [outputExpr, Vector.getElem_ofFn]
    change Expression.eval env
      (lookupExpr (yTable ⟨i, hi⟩)
        { bits := input_var_bits, selector := input_var_selector }
        (Vector.mapRange 11 fun j => var { index := i₀ + j })) =
      lookupValue (yTable ⟨i, hi⟩) input_bits[0] input_bits[1] input_bits[2]
        input_selector
    simp only [lookupExpr, lookupValue, circuit_norm]
    rw [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hselector,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10]

theorem completeness : Completeness Field main Assumptions := by
  circuit_proof_start
  obtain ⟨hbits, hselector⟩ := h_input
  have hin : ∀ (j : Nat) (hj : j < 3),
      Expression.eval env.toEnvironment (input_var_bits[j]'hj) =
        input_bits[j]'hj := by
    intro j hj
    rw [← hbits, Vector.getElem_map]
  have hwc : ∀ (j : Nat) (hj : j < 11),
      env.get (i₀ + j) =
        monomialAt input_bits[0] input_bits[1] input_bits[2] input_selector j := by
    intro j hj
    have h := h_env ⟨j, hj⟩
    simp only [witnessValues, Vector.getElem_ofFn] at h
    simpa only [circuit_norm, hin 0 (by omega), hin 1 (by omega),
      hin 2 (by omega), hselector] using h
  have hwc0 : env.get i₀ = input_bits[0] * input_bits[1] := by
    simpa only [Nat.add_zero, monomialAt] using hwc 0 (by omega)
  intro i
  fin_cases i <;>
    simp only [Vector.getElem_ofFn, constraintAt, circuit_norm]
  all_goals simp only [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega),
    hselector, hwc0, hwc 1 (by omega), hwc 2 (by omega),
    hwc 3 (by omega), hwc 4 (by omega), hwc 5 (by omega), hwc 6 (by omega),
    hwc 7 (by omega), hwc 8 (by omega), hwc 9 (by omega), hwc 10 (by omega),
    monomialAt, Nat.add_zero]
  all_goals ring

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_11

-- Adapted donor module: SelectTopCircuit
section DonorFile5_12

namespace Solution.Secp256k1ScalarMulFixedBase
namespace SelectTop

set_option maxRecDepth 4096

def circuit : FormalCircuit (F circomPrime) (fields 4) Select.AffPoint where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SelectTop
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectCircuit.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

def circuit : FormalCircuit Field Inputs Select.AffPoint where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_12

-- Adapted donor module: CWHelpers
section DonorFile5_13

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CWHelpers

open Challenge.Utils.ComputableWitnessLemmas

theorem witnessOutput_stable {M : TypeMap} [ProvableType M]
    (compute : ProverEnvironment (F circomPrime) → M (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + size M ≤ k) :
    eval env ((ProvableType.witness (α := M) compute).output offset) =
      eval env' ((ProvableType.witness (α := M) compute).output offset) := by
  have hout : (ProvableType.witness (α := M) compute).output offset
      = varFromOffset M offset := rfl
  rw [hout, CircuitType.eval_expression_prover_to_verifier,
    CircuitType.eval_expression_prover_to_verifier, ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi,
    ← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (offset + i) (by omega)

theorem emuWitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → Emu (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((ProvableType.witness (α := Emu) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

theorem fieldsWitnessOutput_stable {m : ℕ}
    (compute : ProverEnvironment (F circomPrime) → fields m (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    eval env ((ProvableType.witness (α := fields m) compute).output offset) =
      eval env' ((ProvableType.witness (α := fields m) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := fields m) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := fields m) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

theorem fieldWitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → F circomPrime)
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset < k) :
    Expression.eval env.toEnvironment
        ((ProvableType.witness (α := field) compute).output offset) =
      Expression.eval env'.toEnvironment
        ((ProvableType.witness (α := field) compute).output offset) := by
  simp [Circuit.output, ProvableType.witness, ProvableType.varFromOffset,
    explicit_provable_type]
  exact h_agree offset hk

theorem varFromOffset_stable {M : TypeMap} [ProvableType M]
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + size M ≤ k) :
    eval env (varFromOffset M offset : Var M (F circomPrime))
      = eval env' (varFromOffset M offset : Var M (F circomPrime)) := by
  rw [CircuitType.eval_expression_prover_to_verifier,
    CircuitType.eval_expression_prover_to_verifier, ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi,
    ← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (offset + i) (by omega)

theorem assertion_structuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input) (parentInput : Var Parent (F circomPrime))
    (input : Var Input (F circomPrime)) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
    ∀ env env',
      FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((assertion circuit input).operations n) := by
  intro env env'
  rw [FormalAssertion.assertion_structuralComputableWitnesses_iff]
  exact FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    circuit parentInput input n hinput hcircuit env env'

end CWHelpers
end Solution.Secp256k1ScalarMulFixedBase

/-! ### merged from `TopSelectCW.lean` (submission file-count cap) -/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace TopSelect

open Challenge.Utils.ComputableWitnessLemmas

theorem lookupExpr_eval_stable (table : Nat → Field)
    (input : Var Inputs Field) (w : Var (fields 11) Field)
    {env env' : ProverEnvironment Field}
    (hinput : eval env input = eval env' input)
    (hw : eval env w = eval env' w) :
    Expression.eval env.toEnvironment (lookupExpr table input w) =
      Expression.eval env'.toEnvironment (lookupExpr table input w) := by
  rcases input with ⟨bits, selector⟩
  simp only [circuit_norm, Inputs.mk.injEq] at hinput
  obtain ⟨hbits, hselector⟩ := hinput
  have hb : ∀ (j : Nat) (hj : j < 3),
      Expression.eval env.toEnvironment (bits[j]'hj) =
        Expression.eval env'.toEnvironment (bits[j]'hj) := by
    intro j hj
    have h := congrArg (fun v : fields 3 Field => v[j]'hj) hbits
    simpa only [Vector.getElem_map] using h
  have hwi : ∀ (j : Nat) (hj : j < 11),
      Expression.eval env.toEnvironment (w[j]'hj) =
        Expression.eval env'.toEnvironment (w[j]'hj) := by
    intro j hj
    have h := congrArg (fun v : fields 11 Field => v[j]'hj) hw
    simpa only [circuit_norm] using h
  simp only [lookupExpr, Expression.eval,
    hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hselector,
    hwi 0 (by omega), hwi 1 (by omega), hwi 2 (by omega),
    hwi 3 (by omega), hwi 4 (by omega), hwi 5 (by omega),
    hwi 6 (by omega), hwi 7 (by omega), hwi 8 (by omega),
    hwi 9 (by omega), hwi 10 (by omega)]

theorem outputExpr_eval_stable (input : Var Inputs Field) (w : Var (fields 11) Field)
    {env env' : ProverEnvironment Field}
    (hinput : eval env input = eval env' input)
    (hw : eval env w = eval env' w) :
    eval env (outputExpr input w) = eval env' (outputExpr input w) := by
  simp only [outputExpr, circuit_norm, Select.AffPoint.mk.injEq]
  constructor
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    exact lookupExpr_eval_stable _ _ _ hinput hw
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    exact lookupExpr_eval_stable _ _ _ hinput hw

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  rcases input with ⟨bits, selector⟩
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hcomp :
        eval env (Inputs.mk bits selector) =
          eval env' (Inputs.mk bits selector) := h_input
    simp only [circuit_norm, Inputs.mk.injEq] at hcomp
    obtain ⟨hbits, hselector⟩ := hcomp
    have hb : ∀ (j : Nat) (hj : j < 3),
        Expression.eval env.toEnvironment (bits[j]'hj) =
          Expression.eval env'.toEnvironment (bits[j]'hj) := by
      intro j hj
      have h := congrArg (fun v : fields 3 Field => v[j]'hj) hbits
      simpa only [Vector.getElem_map] using h
    apply Vector.ext
    intro i hi
    simp only [witnessValues, Vector.getElem_ofFn, circuit_norm,
      hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hselector]
  · intro _
    trivial

theorem computableWitness : ∀ n (input : Var Inputs Field),
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment Field => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end TopSelect
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_13

-- Adapted donor module: Select13Cost
section DonorFile5_14

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select13

/-- The width-12 selector returns the production affine-point type. -/
abbrev AffPoint := Select.AffPoint

abbrev Field := F circomPrime

def bitVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (i : Nat) (hi : i < 13) : Field := Expression.eval env.toEnvironment b[i]

def xVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (i : Nat) (hi : i < 12) : Field :=
  2 * bitVal env b 12 (by omega) * bitVal env b i (by omega) -
    bitVal env b 12 (by omega) - bitVal env b i (by omega) + 1

/-- The XNOR of the sign bit with magnitude bit `i`.  It is witnessed directly
(pinned by one rank-1 row), so it is a bare wire rather than an affine rewrite of
`b[12] * b[i]`; that keeps the whole selected-x expression free of the input
bits. -/
def xExpr (_b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (i : Nat) (hi : i < 12) : Expression Field :=
  w[i]'hi

/-- Low bit index of a magnitude-bit pair.  Pairs are
`(0,1),(2,3),(4,5),(7,8),(9,10)`; bit 6 is handled as a single-bit extension
of the inner one-hot, which is what makes the 7-bit inner / 4-bit outer split. -/
def pairLo : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | _ => 0

lemma pairLo_add_lt {p : Nat} (hp : p < 5) : pairLo p + 1 < 12 := by
  match p, hp with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

lemma pairLo_lt {p : Nat} (hp : p < 5) : pairLo p < 12 :=
  Nat.lt_of_succ_lt (pairLo_add_lt hp)

def pairExpr (x y xy : Expression Field) (v : Nat) : Expression Field :=
  if v = 0 then 1 - x - y + xy else if v = 1 then x - xy else
  if v = 2 then y - xy else xy

def pairVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (p v : Nat) (hp : p < 5) : Field :=
  let x := xVal env b (pairLo p) (pairLo_lt hp)
  let y := xVal env b (pairLo p + 1) (pairLo_add_lt hp)
  (if v % 2 = 1 then x else 1-x) * (if v / 2 % 2 = 1 then y else 1-y)

def hot4Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (basePair v : Nat) (hp : basePair < 4) : Field :=
  pairVal env b basePair (v % 4) (by omega) *
    pairVal env b (basePair + 1) (v / 4) (by omega)

/-- Six-bit inner one-hot value (bits 0..5). -/
def hot6Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot4Val env b 0 (v % 16) (by omega) * pairVal env b 2 (v / 16) (by omega)

/-- Seven-bit inner one-hot value (bits 0..6); the extension multiplies the
six-bit cell by the single bit-6 factor. -/
def hot7Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot6Val env b (v % 64) *
      (if v / 64 = 1 then xVal env b 6 (by omega) else 1 - xVal env b 6 (by omega))


/-- Five-bit outer one-hot value (bits 7..11); the extension multiplies the
four-bit outer cell by the single bit-11 factor. -/
def hot5Val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (v : Nat) : Field := hot4Val env b 3 (v % 16) (by omega) *
      (if v / 16 = 1 then xVal env b 11 (by omega) else 1 - xVal env b 11 (by omega))

/-- One factor of a bit-pair one-hot, as an expression in the input bits. -/
def innerP (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 5) (u : Nat) : Expression Field :=
  pairExpr (xExpr b w (pairLo p) (pairLo_lt hp)) (xExpr b w (pairLo p + 1) (pairLo_add_lt hp))
    (blk[p]'hp) u

/-- A `4 x 4` one-hot from only nine products: the last row and the last column
are affine consequences of `sum_c P1 c = 1` and `sum_a P0 a = 1`.  Only the
fifteen cells `v < 15` are produced here; cell `15` is recovered by `hot4`. -/
def hot4gen (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field) (v : Nat) :
    Expression Field :=
  if ha : v % 4 < 3 then
    (if hc : v / 4 < 3 then h[v % 4 + 3 * (v / 4)]'(by omega)
     else P0 (v % 4) - h[v % 4]'(by omega) - h[v % 4 + 3]'(by omega) - h[v % 4 + 6]'(by omega))
  else
    (if hc : v / 4 < 3 then
      P1 (v / 4) - h[3 * (v / 4)]'(by omega) - h[3 * (v / 4) + 1]'(by omega)
        - h[3 * (v / 4) + 2]'(by omega)
     else 0)

/-- The fifteen derived cells of the four-bit one-hot on pairs `p`, `p+1`. -/
def hot4Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    Var (fields 15) Field :=
  Vector.ofFn fun v : Fin 15 =>
    hot4gen (innerP b w blk p (by omega)) (innerP b w blk (p + 1) (by omega)) h v.val

/-- The forty-eight cells of the `c < 3` part of the six-bit one-hot, from
forty-five products: the `a = 15` row is affine. -/
def inner6Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) : Var (fields 48) Field :=
  Vector.ofFn fun v : Fin 48 =>
    if hh : v.val % 16 < 15 then h[15 * (v.val / 16) + v.val % 16]'(by have := v.isLt; omega)
    else innerP b w blk 2 (by decide) (v.val / 16)
      - (Vector.ofFn fun a : Fin 15 =>
          h[15 * (v.val / 16) + a.val]'(by have := v.isLt; have := a.isLt; omega)).foldl (·+·) 0

/-- The sixty-four cells of the bit-6 layer, from sixty-three products. -/
def inner7Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field) : Var (fields 64) Field :=
  Vector.ofFn fun v : Fin 64 =>
    if hk : v.val < 63 then h[v.val]'hk
    else xExpr b w 6 (by decide)
      - (Vector.ofFn fun a : Fin 63 => h[a.val]'a.isLt).foldl (·+·) 0


/-- The sixteen cells of the bit-11 outer layer, from fifteen products. -/
def outer5Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 15) Field) : Var (fields 16) Field :=
  Vector.ofFn fun v : Fin 16 =>
    if hk : v.val < 15 then h[v.val]'hk
    else xExpr b w 11 (by decide)
      - (Vector.ofFn fun a : Fin 15 => h[a.val]'a.isLt).foldl (·+·) 0

/-- The sixteenth four-bit one-hot cell is affine-derived. -/
def hot4 (blk : Var (fields 5) Field) (h : Var (fields 15) Field)
    (basePair : Nat) (hbase : basePair < 4) (v : Nat) (hv : v < 16) : Expression Field :=
  if _ : v = 15 then blk[basePair+1]'(by omega) - h[12] - h[13] - h[14]
  else h[v]'(by omega)

/-- Six-bit inner one-hot; its last pair branch is affine-derived. -/
def hot6 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (v : Nat) (_hv : v < 64) : Expression Field :=
  let a := v % 16
  let c := v / 16
  if _ : c < 3 then h6[c*16+a]'(by omega)
  else hot4 blk h4 0 (by omega) a (by omega) - h6[a] - h6[16+a] - h6[32+a]

/-- Seven-bit inner one-hot; the single bit-6 zero branch is affine-derived
from the six-bit cell. -/
def hot7 (blk : Var (fields 5) Field) (h4 : Var (fields 15) Field)
    (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (v : Nat) (_hv : v < 128) : Expression Field :=
  let a := v % 64
  if _ : v / 64 = 1 then h7[a]'(by omega)
  else hot6 blk h4 h6 a (by omega) - h7[a]'(by omega)


/-- Five-bit outer one-hot; the single bit-11 zero branch is affine-derived
from the four-bit outer cell. -/
def hot5 (blk : Var (fields 5) Field) (h4o : Var (fields 15) Field)
    (h5 : Var (fields 16) Field) (v : Nat) (_hv : v < 32) : Expression Field :=
  let a := v % 16
  if _ : v / 16 = 1 then h5[a]'(by omega)
  else hot4 blk h4o 3 (by omega) a (by omega) - h5[a]'(by omega)

def inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))).foldl (·+·) 0

def innerVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb outer : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field))

/-- The free affine correction produced by pairing two one-hot terms into a
single rank-2 row.  Because the inner one-hot cells are orthogonal idempotents,
`inner o0 * inner o1` collapses to this linear combination of the same cells
with compile-time coefficients. -/
def corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat) : Expression Field :=
  (Vector.ofFn fun a : Fin 128 => hot7 blk h4 h6 h7 a.val a.isLt *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))).foldl (·+·) 0

def corrVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb o0 o1 : Nat) (table : Nat → Nat) : Field :=
  ∑ a : Fin 128, hot7Val env b a.val *
    ((((limbOfNat (table (128*o0+a.val)) limb : Nat) : Field)) *
      (((limbOfNat (table (128*o1+a.val)) limb : Nat) : Field)))

/-- The value pinned by one rank-2 row of the **single-stage** outer
contraction: it carries two of the *sixteen* outer one-hot terms for one
product.  Because the two outer cells `2k` and `2k+1` differ in exactly one
boolean factor their product vanishes, and because the inner one-hot cells are
orthogonal idempotents the remaining cross term collapses to the free affine
correction `corrVal`. -/
def outProdVal (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb k : Nat) (table : Nat → Nat) : Field :=
  (hot5Val env b (2*k) + innerVal env b limb (2*k+1) table) *
    (hot5Val env b (2*k+1) + innerVal env b limb (2*k) table)
    - corrVal env b limb (2*k) (2*k+1) table

def selected2 (limb : Nat) (hl : limb < 4) (_blk : Var (fields 5) Field)
    (_h4 : Var (fields 15) Field) (_h6 : Var (fields 48) Field) (_h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field) (_table : Nat → Nat) :
    Expression Field :=
  (Vector.ofFn fun k : Fin 16 =>
    pA[16 * limb + k.val]'(by have := k.isLt; omega)).foldl (·+·) 0

def selectedVal2 (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb : Nat) (table : Nat → Nat) : Field :=
  ∑ k : Fin 16, outProdVal env b limb k.val table

/-- The selected x-coordinate is already affine in the selector witnesses, so
return it directly instead of materializing four redundant output witnesses. -/
def xSelExpr (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field) (pA : Var (fields 64) Field) :
    Var Emu Field :=
  Vector.ofFn fun i : Fin 4 =>
    selected2 i.val i.isLt blk inner4 inner6 inner7 pA xTable

attribute [irreducible] xSelExpr

@[simp] theorem xSelExpr_get (xTable : Nat → Nat) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field) (pA : Var (fields 64) Field)
    (i : Nat) (hi : i < 4) :
    (xSelExpr xTable blk inner4 inner6 inner7 pA)[i]'hi =
      selected2 i hi blk inner4 inner6 inner7 pA xTable := by
  unfold xSelExpr
  rw [Vector.getElem_ofFn]

def bitsVal (b : fields 13 Field) : Nat :=
  b[0].val + 2*b[1].val + 4*b[2].val + 8*b[3].val + 16*b[4].val +
  32*b[5].val + 64*b[6].val + 128*b[7].val + 256*b[8].val +
  512*b[9].val + 1024*b[10].val + 2048*b[11].val + 4096*b[12].val

def magnitudeIndex (b : fields 13 Field) : Nat :=
  if 4096 ≤ bitsVal b then bitsVal b - 4096 else 4095 - bitsVal b

/-- The magnitude index of the *evaluated* selector inputs. -/
def magIdxOf (env : ProverEnvironment Field) (b : Var (fields 13) Field) : Nat :=
  magnitudeIndex (Vector.ofFn fun j : Fin 13 => bitVal env b j.val j.isLt)


/-- Limbwise positive-minus-negative y lookup.  This is deliberately a field
expression, not the limbs of a packed natural-number difference. -/
def yDeltaLimb (yTable : Nat → Nat) (idx limb : Nat) : Field :=
  ((limbOfNat (yTable idx) limb : Nat) : Field) -
    ((limbOfNat (P256 - yTable idx) limb : Nat) : Field)

/-- The limbwise sign delta.  Every fixed-base table entry satisfies
`y % 2^64 ≤ P256 % 2^64`, so the schoolbook subtraction `P256 - y` never
borrows and the delta is *purely affine* in the selected negated limbs: no
borrow-bit column, no witnessed bits, no booleanity rows (see
`Borrow.delta_field_noborrow`). -/
def deltaExpr (limb : Nat) (hlimb : limb < 4) (blk : Var (fields 5) Field)
    (inner4 : Var (fields 15) Field) (inner6 : Var (fields 48) Field)
    (inner7 : Var (fields 64) Field)
    (negA : Var (fields 64) Field)
    (yTable : Nat → Nat) : Expression Field :=
  ((limbOfNat P256 limb : Nat) : Field)
    - selected2 limb hlimb blk inner4 inner6 inner7 negA
        (fun j => P256 - yTable j) * (2 : Field)

def deltaValE (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (limb : Nat) (yTable : Nat → Nat) : Field :=
  ((limbOfNat P256 limb : Nat) : Field)
    - selectedVal2 env b limb (fun j => P256 - yTable j) * (2 : Field)

/-- Width-12 bilinear selector (7-bit inner / 4-bit outer) parameterized only by
certified positive x/y coordinates.  Negative y and the sign delta are derived
limbwise as affine expressions, matching the width-9 production selector. -/
def main (xTable yTable : Nat → Nat)
    (b : Var (fields 13) Field) : Circuit Field (Var AffPoint Field) := do
  let w ← ProvableType.witness (α := fields 12) fun env =>
    Vector.ofFn fun i : Fin 12 => xVal env b i.val (by omega)
  Circuit.forEach (Vector.ofFn fun i : Fin 12 =>
    b[12] * (2 : Field) * b[i.val]'(by omega)
      - (w[i.val]'i.isLt + b[12] + b[i.val]'(by omega) - 1)) assertZero
  let blk ← ProvableType.witness (α := fields 5) fun env =>
    Vector.ofFn fun p : Fin 5 => xVal env b (pairLo p.val) (pairLo_lt p.isLt) *
      xVal env b (pairLo p.val + 1) (pairLo_add_lt p.isLt)
  Circuit.forEach (Vector.ofFn fun p : Fin 5 =>
    xExpr b w (pairLo p.val) (pairLo_lt p.isLt) *
    xExpr b w (pairLo p.val + 1) (pairLo_add_lt p.isLt) - blk[p.val]'p.isLt) assertZero
  let inner4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 0 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 0 (by decide) (j.val % 3) *
    innerP b w blk 1 (by decide) (j.val / 3) - inner4w[j.val]'j.isLt) assertZero
  let inner4 := hot4Vec b w blk 0 (by decide) inner4w
  let inner6w ← ProvableType.witness (α := fields 45) fun env =>
    Vector.ofFn fun j : Fin 45 => hot6Val env b (16 * (j.val / 15) + j.val % 15)
  Circuit.forEach (Vector.ofFn fun j : Fin 45 =>
    hot4 blk inner4 0 (by omega) (j.val % 15) (by omega) *
    innerP b w blk 2 (by decide) (j.val / 15) - inner6w[j.val]'j.isLt) assertZero
  let inner6 := inner6Vec b w blk inner6w
  let inner7w ← ProvableType.witness (α := fields 63) fun env =>
    Vector.ofFn fun j : Fin 63 => hot6Val env b j.val * xVal env b 6 (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 63 =>
    hot6 blk inner4 inner6 j.val (by omega) * xExpr b w 6 (by omega) - inner7w[j.val]'j.isLt) assertZero
  let inner7 := inner7Vec b w inner7w
  let outer4w ← ProvableType.witness (α := fields 9) fun env =>
    Vector.ofFn fun j : Fin 9 => hot4Val env b 3 (j.val % 3 + 4 * (j.val / 3)) (by omega)
  Circuit.forEach (Vector.ofFn fun j : Fin 9 =>
    innerP b w blk 3 (by decide) (j.val % 3) *
    innerP b w blk 4 (by decide) (j.val / 3) - outer4w[j.val]'j.isLt) assertZero
  let outer4 := hot4Vec b w blk 3 (by decide) outer4w
  let outer5w ← ProvableType.witness (α := fields 15) fun env =>
    Vector.ofFn fun j : Fin 15 => hot5Val env b (16 + j.val)
  Circuit.forEach (Vector.ofFn fun j : Fin 15 =>
    hot4 blk outer4 3 (by omega) j.val (by omega) *
    xExpr b w 11 (by omega) - outer5w[j.val]'j.isLt) assertZero
  let outer5 := outer5Vec b w outer5w
  let xProd ← ProvableType.witness (α := fields 64) fun env =>
    Vector.ofFn fun k : Fin 64 => outProdVal env b (k.val/16) (k.val % 16) xTable
  Circuit.forEach (Vector.ofFn fun k : Fin 64 =>
    (hot5 blk outer4 outer5 (2 * (k.val % 16)) (by omega) +
        inner (k.val/16) (2 * (k.val % 16) + 1) blk inner4 inner6 inner7 xTable) *
      (hot5 blk outer4 outer5 (2 * (k.val % 16) + 1) (by omega) +
        inner (k.val/16) (2 * (k.val % 16)) blk inner4 inner6 inner7 xTable)
      - (corrC (k.val/16) (2 * (k.val % 16)) (2 * (k.val % 16) + 1)
            blk inner4 inner6 inner7 xTable
          + xProd[k.val]'k.isLt)) assertZero
  let yNeg ← ProvableType.witness (α := fields 64) fun env =>
    Vector.ofFn fun k : Fin 64 =>
      outProdVal env b (k.val/16) (k.val % 16) (fun j => P256 - yTable j)
  Circuit.forEach (Vector.ofFn fun k : Fin 64 =>
    (hot5 blk outer4 outer5 (2 * (k.val % 16)) (by omega) +
        inner (k.val/16) (2 * (k.val % 16) + 1) blk inner4 inner6 inner7
          (fun j => P256 - yTable j)) *
      (hot5 blk outer4 outer5 (2 * (k.val % 16) + 1) (by omega) +
        inner (k.val/16) (2 * (k.val % 16)) blk inner4 inner6 inner7
          (fun j => P256 - yTable j))
      - (corrC (k.val/16) (2 * (k.val % 16)) (2 * (k.val % 16) + 1)
            blk inner4 inner6 inner7 (fun j => P256 - yTable j)
          + yNeg[k.val]'k.isLt)) assertZero
  let y ← ProvableType.witness (α := Emu) fun env =>
    Vector.ofFn fun i : Fin 4 => bitVal env b 12 (by omega) * deltaValE env b i.val yTable + selectedVal2 env b i.val (fun j => P256 - yTable j)
  Circuit.forEach (Vector.ofFn fun i : Fin 4 =>
    b[12] * deltaExpr i.val i.isLt blk inner4 inner6 inner7 yNeg yTable +
      selected2 i.val i.isLt blk inner4 inner6 inner7 yNeg
        (fun j => P256 - yTable j) - y[i.val]'i.isLt) assertZero
  return {x := xSelExpr xTable blk inner4 inner6 inner7 xProd, y := y}

def ChannelsFree {α : Type} (c : Circuit Field α) : Prop :=
  ∀ n, (c.operations n).ChannelsLawful [] []

namespace ChannelsFree

theorem pure {α : Type} (a : α) : ChannelsFree (pure a : Circuit Field α) := by
  intro n
  simpa only [Circuit.pure_operations_eq] using
    (Operations.channelsLawful_nil (F := Field))

theorem bind {α β : Type} {f : Circuit Field α} {g : α → Circuit Field β}
    (hf : ChannelsFree f) (hg : ∀ a, ChannelsFree (g a)) : ChannelsFree (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq]
  simpa using Operations.channelsLawful_append_of_channelsLawful
    (hf n) (hg _ (n + f.localLength n))

theorem provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment Field → α Field) :
    ChannelsFree (ProvableType.witness compute) := by
  intro n
  change Operations.ChannelsLawful ([.witness (ProvableType.size α) _] : Operations Field) [] []
  simp only [Operations.ChannelsLawful, circuit_norm]

theorem assertZero (e : Expression Field) : ChannelsFree (Circuit.assertZero e) := by
  intro n
  change Operations.ChannelsLawful ([.assert e] : Operations Field) [] []
  simp only [Operations.ChannelsLawful, circuit_norm]

theorem lawful_flatten_ofFn {m : ℕ} (g : Fin m → Operations Field)
    (h : ∀ i, (g i).ChannelsLawful [] []) :
    Operations.ChannelsLawful (List.ofFn g).flatten [] [] := by
  induction m with
  | zero => simpa [List.ofFn_zero] using (Operations.channelsLawful_nil (F := Field))
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons]
      simpa using Operations.channelsLawful_append_of_channelsLawful
        (h 0) (ih (fun i => g i.succ) (fun i => h i.succ))

theorem forEach {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit Field Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ a, ChannelsFree (body a)) :
    ChannelsFree (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact lawful_flatten_ofFn _ (fun i => h _ _)

end ChannelsFree

private theorem channelsFree_main (xt yt : Nat → Nat)
    (b : Var (fields 13) Field) : ChannelsFree (main xt yt b) := by
  unfold main
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.provableWitness _) fun _ => ?_
  refine ChannelsFree.bind (ChannelsFree.forEach fun _ => ChannelsFree.assertZero _) fun _ => ?_
  exact ChannelsFree.pure _

/-- The selected x-coordinate, as it appears at a concrete offset: a pure affine
expression in the selector's own witnesses, never materialized. -/
def dummyBits : Var (fields 13) Field := Vector.ofFn fun _ : Fin 13 => (0 : Expression Field)

/-- `hot4Vec` does not read the input bits (`xExpr` ignores them), so the choice
of bit vector is irrelevant. -/
theorem hot4Vec_bits_irrel (b b' : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field) :
    hot4Vec b w blk p hp h = hot4Vec b' w blk p hp h := rfl

theorem inner6Vec_bits_irrel (b b' : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field) :
    inner6Vec b w blk h = inner6Vec b' w blk h := rfl

theorem inner7Vec_bits_irrel (b b' : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field) :
    inner7Vec b w h = inner7Vec b' w h := rfl

def outXAt (xt : Nat → Nat) (i0 : Nat) : Var Emu Field :=
  xSelExpr xt (varFromOffset (fields 5) (i0 + 12))
    (hot4Vec dummyBits (varFromOffset (fields 12) i0) (varFromOffset (fields 5) (i0 + 12)) 0
      (by decide) (varFromOffset (fields 9) (i0 + 17)))
    (inner6Vec dummyBits (varFromOffset (fields 12) i0) (varFromOffset (fields 5) (i0 + 12))
      (varFromOffset (fields 45) (i0 + 26)))
    (inner7Vec dummyBits (varFromOffset (fields 12) i0) (varFromOffset (fields 63) (i0 + 71)))
    (varFromOffset (fields 64) (i0 + 158))

instance elaborated (xt yt : Nat → Nat) :
    ElaboratedCircuit Field (fields 13) AffPoint (main xt yt) where
  localLength _ := 290
  output _ i0 :=
    { x := outXAt xt i0,
      y := varFromOffset Emu (i0 + 286) }
  localLength_eq := by
    intro input offset
    simp +arith only [main, circuit_norm, numLimbs]
  output_eq := by
    intro input offset
    simp +arith only [main, outXAt, circuit_norm, numLimbs]
    rw [hot4Vec_bits_irrel input dummyBits, inner6Vec_bits_irrel input dummyBits,
      inner7Vec_bits_irrel input dummyBits]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, numLimbs]
  channelsLawful := by
    exact channelsFree_main xt yt

def Assumptions (b : fields 13 Field) : Prop := ∀ i : Fin 13, IsBool b[i]

def Spec (xTable yTable : Nat → Nat) (b : fields 13 Field)
    (out : AffPoint Field) : Prop :=
  out.x = Vector.ofFn (fun i : Fin 4 =>
      ((limbOfNat (xTable (magnitudeIndex b)) i.val : Nat) : Field)) ∧
  out.y = Vector.ofFn (fun i : Fin 4 =>
      (b[12].val : Field) *
          (((limbOfNat (yTable (magnitudeIndex b)) i.val : Nat) : Field) -
           ((limbOfNat (P256 - yTable (magnitudeIndex b)) i.val : Nat) : Field)) +
       ((limbOfNat (P256 - yTable (magnitudeIndex b)) i.val : Nat) : Field))

section ComputableWitness
open Challenge.Utils.ComputableWitnessLemmas

set_option maxHeartbeats 6400000 in
theorem structuralCW {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent Field) (xt yt : Nat → Nat)
    (b : Var (fields 13) Field) (n : Nat)
    (hb : ∀ (k : Nat) (env env' : ProverEnvironment Field), n ≤ k →
      env.AgreesBelow k env' → eval env parentInput = eval env' parentInput →
      ∀ (j : Nat) (hj : j < 13),
        Expression.eval env.toEnvironment (b[j]'hj) =
          Expression.eval env'.toEnvironment (b[j]'hj))
    (env env' : ProverEnvironment Field) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n ((main xt yt b).operations n) := by
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true, implies_true]
  and_intros
  all_goals first
    | trivial
    | (intro hagree hpin
       try simp only [circuit_norm] at hagree
       have hbit := hb _ env env' (by omega) hagree hpin
       apply Vector.ext; intro i hi
       simp only [Vector.getElem_ofFn, bitVal, xVal, pairVal, hot4Val, hot6Val,
         hot7Val, hot5Val, innerVal, corrVal, outProdVal, selectedVal2, deltaValE, hbit])

end ComputableWitness

end Select13
end Solution.Secp256k1ScalarMulFixedBase

namespace Solution.Secp256k1ScalarMulFixedBase.Select13
open Challenge.CostR1CS
open Cost
open CompactAdd (isR1CSRow_add_mul_sub)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affineW_dummyBits : AffineW dummyBits := by
  intro i hi
  rw [dummyBits, Vector.getElem_ofFn]
  exact Affine.const _

theorem affine_xExpr (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (hw : AffineW w) (i : Nat) (hi : i < 12) : Affine (xExpr b w i hi) := by
  unfold xExpr
  exact hw i hi

theorem affine_pairExpr {x y xy : Expression Field} (hx : Affine x) (hy : Affine y)
    (hxy : Affine xy) (v : Nat) : Affine (pairExpr x y xy v) := by
  unfold pairExpr
  split_ifs
  · exact Affine.add (Affine.sub (Affine.sub (Affine.const 1) hx) hy) hxy
  · exact Affine.sub hx hxy
  · exact Affine.sub hy hxy
  · exact hxy

theorem affine_ofFn_foldl_add {n : Nat} (g : Fin n → Expression Field)
    (hg : ∀ i, Affine (g i)) : Affine ((Vector.ofFn g).foldl (·+·) 0) := by
  have hof : Vector.ofFn g = Vector.map g (Vector.finRange n) := by
    apply Vector.ext; intro i hi
    rw [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_finRange]
  rw [hof, Vector.foldl_map, vector_foldl_finRange]
  exact affine_finFoldl' _ _ Affine.zero fun acc i hacc => Affine.add hacc (hg i)

theorem affine_innerP (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk)
    (p : Nat) (hp : p < 5) (u : Nat) : Affine (innerP b w blk p hp u) := by
  unfold innerP
  exact affine_pairExpr (affine_xExpr _ _ hw _ (pairLo_lt hp))
    (affine_xExpr _ _ hw _ (pairLo_add_lt hp)) (hblk p hp) u

theorem affine_hot4gen {P0 P1 : Nat → Expression Field} {h : Var (fields 9) Field}
    (hP0 : ∀ u, Affine (P0 u)) (hP1 : ∀ u, Affine (P1 u)) (hh : AffineW h) (v : Nat) :
    Affine (hot4gen P0 P1 h v) := by
  unfold hot4gen
  split
  · split
    · exact hh _ (by omega)
    · exact Affine.sub (Affine.sub (Affine.sub (hP0 _) (hh _ (by omega))) (hh _ (by omega)))
        (hh _ (by omega))
  · split
    · exact Affine.sub (Affine.sub (Affine.sub (hP1 _) (hh _ (by omega))) (hh _ (by omega)))
        (hh _ (by omega))
    · exact Affine.zero

theorem affineW_hot4Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (p : Nat) (hp : p < 4) (h : Var (fields 9) Field)
    (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk) (hh : AffineW h) :
    AffineW (hot4Vec b w blk p hp h) := by
  intro v hv
  rw [hot4Vec, Vector.getElem_ofFn]
  exact affine_hot4gen (fun u => affine_innerP b w blk hb hw hblk p (by omega) u)
    (fun u => affine_innerP b w blk hb hw hblk (p+1) (by omega) u) hh v

theorem affineW_inner6Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field) (h : Var (fields 45) Field)
    (hb : AffineW b) (hw : AffineW w) (hblk : AffineW blk) (hh : AffineW h) :
    AffineW (inner6Vec b w blk h) := by
  intro v hv
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split
  · exact hh _ (by omega)
  · exact Affine.sub (affine_innerP b w blk hb hw hblk 2 (by decide) _)
      (affine_ofFn_foldl_add _ fun a => hh _ (by omega))

theorem affineW_inner7Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field)
    (hb : AffineW b) (hw : AffineW w) (hh : AffineW h) :
    AffineW (inner7Vec b w h) := by
  intro v hv
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split
  · exact hh _ (by omega)
  · exact Affine.sub (affine_xExpr _ _ hw 6 (by decide))
      (affine_ofFn_foldl_add _ fun a => hh _ a.isLt)

theorem affine_hot4 {blk : Var (fields 5) Field} {h : Var (fields 15) Field}
    (hb : AffineW blk) (hh : AffineW h) (p : Nat) (hp : p < 4) (v : Nat) (hv : v < 16) :
    Affine (hot4 blk h p hp v hv) := by
  unfold hot4
  split
  · exact Affine.sub (Affine.sub (Affine.sub (hb (p+1) (by omega)) (hh 12 (by omega)))
      (hh 13 (by omega))) (hh 14 (by omega))
  · exact hh v (by omega)

theorem affine_hot6 {blk : Var (fields 5) Field} {h4 : Var (fields 15) Field}
    {h6 : Var (fields 48) Field} (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (v : Nat) (hv : v < 64) : Affine (hot6 blk h4 h6 v hv) := by
  unfold hot6
  dsimp only
  split
  · exact hh6 _ (by omega)
  · exact Affine.sub (Affine.sub (Affine.sub (affine_hot4 hb hh4 0 (by omega) _ (by omega))
      (hh6 _ (by omega))) (hh6 _ (by omega))) (hh6 _ (by omega))

theorem affine_hot7 {blk : Var (fields 5) Field} {h4 : Var (fields 15) Field}
    {h6 : Var (fields 48) Field} {h7 : Var (fields 64) Field}
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7)
    (v : Nat) (hv : v < 128) : Affine (hot7 blk h4 h6 h7 v hv) := by
  unfold hot7
  dsimp only
  split
  · exact hh7 _ (by omega)
  · exact Affine.sub (affine_hot6 hb hh4 hh6 _ (by omega)) (hh7 _ (by omega))

theorem affine_inner (limb outer : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat)
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7) :
    Affine (inner limb outer blk h4 h6 h7 table) := by
  unfold inner
  exact affine_ofFn_foldl_add _ fun a =>
    Affine.mul_deg0 (affine_hot7 hb hh4 hh6 hh7 a.val a.isLt) (by simp [degree])

theorem affine_corrC (limb o0 o1 : Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (table : Nat → Nat)
    (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6) (hh7 : AffineW h7) :
    Affine (corrC limb o0 o1 blk h4 h6 h7 table) := by
  unfold corrC
  exact affine_ofFn_foldl_add _ fun a =>
    Affine.mul_deg0 (affine_hot7 hb hh4 hh6 hh7 a.val a.isLt) (by simp [degree])

theorem affine_selected2 (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field)
    (table : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hpA : AffineW pA) :
    Affine (selected2 limb hl blk h4 h6 h7 pA table) := by
  unfold selected2
  exact affine_ofFn_foldl_add _ fun k => hpA _ (by have := k.isLt; omega)


theorem affineW_outer5Vec (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 15) Field)
    (hb : AffineW b) (hw : AffineW w) (hh : AffineW h) :
    AffineW (outer5Vec b w h) := by
  intro v hv
  rw [outer5Vec, Vector.getElem_ofFn]
  dsimp only
  split
  · exact hh _ (by omega)
  · exact Affine.sub (affine_xExpr _ _ hw 11 (by decide))
      (affine_ofFn_foldl_add _ fun a => hh _ a.isLt)

theorem affine_hot5 {blk : Var (fields 5) Field} {h4o : Var (fields 15) Field}
    {h5 : Var (fields 16) Field}
    (hb : AffineW blk) (hh4 : AffineW h4o) (hh5 : AffineW h5)
    (v : Nat) (hv : v < 32) : Affine (hot5 blk h4o h5 v hv) := by
  unfold hot5
  dsimp only
  split
  · exact hh5 _ (by omega)
  · exact Affine.sub (affine_hot4 hb hh4 3 (by omega) _ (by omega)) (hh5 _ (by omega))

theorem affineW_xSelExpr (table : Nat → Nat) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field) (hb : AffineW blk)
    (hh4 : AffineW h4)
    (hh6 : AffineW h6) (hh7 : AffineW h7) (hpA : AffineW pA) :
    AffineW (xSelExpr table blk h4 h6 h7 pA) := by
  intro i hi
  rw [xSelExpr_get]
  exact affine_selected2 i hi blk h4 h6 h7 pA table hb hh4 hh6 hh7 hpA

theorem affine_deltaExpr (limb : Nat) (hl : limb < 4) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (negA : Var (fields 64) Field)
    (yTable : Nat → Nat) (hb : AffineW blk) (hh4 : AffineW h4) (hh6 : AffineW h6)
    (hh7 : AffineW h7) (hnA : AffineW negA) :
    Affine (deltaExpr limb hl blk h4 h6 h7 negA yTable) := by
  unfold deltaExpr
  exact Affine.sub (Affine.const _)
    (Affine.mul_fconst _ (affine_selected2 _ _ _ _ _ _ _ _ hb hh4 hh6 hh7 hnA))

def selectCost : Count := ⟨290, 290⟩

set_option maxHeartbeats 4000000 in
theorem costIs_main (xt yt : Nat → Nat) (b : Var (fields 13) Field) :
    CostIs (main xt yt b) selectCost := by
  rw [show selectCost = ⟨12,0⟩ + (⟨0,12⟩ + (⟨5,0⟩ + (⟨0,5⟩ + (⟨9,0⟩ +
    (⟨0,9⟩ + (⟨45,0⟩ + (⟨0,45⟩ + (⟨63,0⟩ + (⟨0,63⟩ + (⟨9,0⟩ + (⟨0,9⟩ +
    (⟨15,0⟩ + (⟨0,15⟩ +
    (⟨64,0⟩ + (⟨0,64⟩ + (⟨64,0⟩ + (⟨0,64⟩ +
    (⟨4,0⟩ + (⟨0,4⟩ + (Count.zero))))))))))))))))))))
    from by decide]
  unfold main
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero a k) fun _ => ?_
  exact CostIs.pure _

end Solution.Secp256k1ScalarMulFixedBase.Select13

end DonorFile5_14

-- Adapted donor module: SelectTheorems13
section DonorFile5_15

namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

def xNbit (b : fields 13 Field) (i : Nat) (hi : i < 12) : Nat :=
  if b[i].val = b[12].val then 1 else 0

/-- The six low magnitude bits (0..5); the base for the inner one-hot. -/
def inner6Index (b : fields 13 Field) : Nat :=
  xNbit b 0 (by omega) + 2*xNbit b 1 (by omega) + 4*xNbit b 2 (by omega) +
  8*xNbit b 3 (by omega) + 16*xNbit b 4 (by omega) + 32*xNbit b 5 (by omega)

/-- The seven low magnitude bits (0..6); the full inner index. -/
def innerIndex (b : fields 13 Field) : Nat :=
  inner6Index b + 64*xNbit b 6 (by omega)

/-- The five high magnitude bits (7..11); the outer index. -/
def outerIndex (b : fields 13 Field) : Nat :=
  xNbit b 7 (by omega) + 2*xNbit b 8 (by omega) + 4*xNbit b 9 (by omega) +
  8*xNbit b 10 (by omega) + 16*xNbit b 11 (by omega)

def transformedIndex (b : fields 13 Field) : Nat :=
  xNbit b 0 (by omega) + 2*xNbit b 1 (by omega) + 4*xNbit b 2 (by omega) +
  8*xNbit b 3 (by omega) + 16*xNbit b 4 (by omega) + 32*xNbit b 5 (by omega) +
  64*xNbit b 6 (by omega) + 128*xNbit b 7 (by omega) + 256*xNbit b 8 (by omega) +
  512*xNbit b 9 (by omega) + 1024*xNbit b 10 (by omega) + 2048*xNbit b 11 (by omega)

lemma xNbit_le (b : fields 13 Field) (i : Nat) (hi : i < 12) : xNbit b i hi ≤ 1 := by
  unfold xNbit
  split <;> omega

lemma transformedIndex_lt (b : fields 13 Field) : transformedIndex b < 4096 := by
  unfold transformedIndex
  have h0 := xNbit_le b 0 (by omega); have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega); have h3 := xNbit_le b 3 (by omega)
  have h4 := xNbit_le b 4 (by omega); have h5 := xNbit_le b 5 (by omega)
  have h6 := xNbit_le b 6 (by omega); have h7 := xNbit_le b 7 (by omega)
  have h8 := xNbit_le b 8 (by omega); have h9 := xNbit_le b 9 (by omega)
  have h10 := xNbit_le b 10 (by omega)
  have h11 := xNbit_le b 11 (by omega)
  omega

lemma inner6Index_lt (b : fields 13 Field) : inner6Index b < 64 := by
  unfold inner6Index
  have h0 := xNbit_le b 0 (by omega); have h1 := xNbit_le b 1 (by omega)
  have h2 := xNbit_le b 2 (by omega); have h3 := xNbit_le b 3 (by omega)
  have h4 := xNbit_le b 4 (by omega); have h5 := xNbit_le b 5 (by omega)
  omega

lemma innerIndex_lt (b : fields 13 Field) : innerIndex b < 128 := by
  unfold innerIndex
  have h6 := xNbit_le b 6 (by omega)
  have h := inner6Index_lt b
  omega

lemma outerIndex_lt (b : fields 13 Field) : outerIndex b < 32 := by
  unfold outerIndex
  have h7 := xNbit_le b 7 (by omega); have h8 := xNbit_le b 8 (by omega)
  have h9 := xNbit_le b 9 (by omega); have h10 := xNbit_le b 10 (by omega)
  have h11 := xNbit_le b 11 (by omega)
  omega

/-- The full inner/outer split reconstructs the transformed index. -/
lemma index_split (b : fields 13 Field) :
    128 * outerIndex b + innerIndex b = transformedIndex b := by
  unfold transformedIndex innerIndex inner6Index outerIndex
  ring

lemma transformedIndex_eq_sign_zero (b : fields 13 Field)
    (hb : ∀ i : Fin 13, IsBool b[i]) (hs : b[12] = 0) :
    transformedIndex b = 4095 - bitsVal b := by
  have hle : ∀ (j : Nat) (hj : j < 13), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have hz : ∀ x : Nat, x ≤ 1 → (if x = 0 then 1 else 0) = 1-x := by
    intro x hx; split <;> omega
  have hsval : b[12].val = 0 := by simpa using congrArg ZMod.val hs
  unfold transformedIndex xNbit
  rw [hsval]
  have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
  have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
  have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
  have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
  have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
  have h10 := hle 10 (by omega); have h11 := hle 11 (by omega)
  rw [hz _ h0, hz _ h1, hz _ h2, hz _ h3, hz _ h4, hz _ h5,
    hz _ h6, hz _ h7, hz _ h8, hz _ h9, hz _ h10, hz _ h11, bitsVal, hsval]
  omega

lemma transformedIndex_eq_sign_one (b : fields 13 Field)
    (hb : ∀ i : Fin 13, IsBool b[i]) (hs : b[12] = 1) :
    transformedIndex b = bitsVal b - 4096 := by
  have hle : ∀ (j : Nat) (hj : j < 13), b[j].val ≤ 1 := fun j hj =>
    Select.IsBool.val_le_one (hb ⟨j, hj⟩)
  have ho : ∀ x : Nat, x ≤ 1 → (if x = 1 then 1 else 0) = x := by
    intro x hx; split <;> omega
  have hsval : b[12].val = 1 := by simpa using congrArg ZMod.val hs
  unfold transformedIndex xNbit
  rw [hsval]
  rw [ho _ (hle 0 (by omega)), ho _ (hle 1 (by omega)), ho _ (hle 2 (by omega)),
    ho _ (hle 3 (by omega)), ho _ (hle 4 (by omega)), ho _ (hle 5 (by omega)),
    ho _ (hle 6 (by omega)), ho _ (hle 7 (by omega)), ho _ (hle 8 (by omega)),
    ho _ (hle 9 (by omega)), ho _ (hle 10 (by omega)), ho _ (hle 11 (by omega)),
    bitsVal, hsval]
  omega

lemma transformedIndex_eq (b : fields 13 Field) (hb : ∀ i : Fin 13, IsBool b[i]) :
    transformedIndex b = magnitudeIndex b := by
  rcases hb ⟨12, by omega⟩ with hs | hs
  · rw [transformedIndex_eq_sign_zero b hb hs, magnitudeIndex]
    have hsval : b[12].val = 0 := by simpa using congrArg ZMod.val hs
    have hle : ∀ (j : Nat) (hj : j < 12), b[j].val ≤ 1 := fun j hj =>
      Select.IsBool.val_le_one (hb ⟨j, by omega⟩)
    have h0 := hle 0 (by omega); have h1 := hle 1 (by omega)
    have h2 := hle 2 (by omega); have h3 := hle 3 (by omega)
    have h4 := hle 4 (by omega); have h5 := hle 5 (by omega)
    have h6 := hle 6 (by omega); have h7 := hle 7 (by omega)
    have h8 := hle 8 (by omega); have h9 := hle 9 (by omega)
    have h10 := hle 10 (by omega); have h11 := hle 11 (by omega)
    have hlt : bitsVal b < 4096 := by rw [bitsVal, hsval]; omega
    rw [if_neg (by omega)]
  · rw [transformedIndex_eq_sign_one b hb hs, magnitudeIndex]
    have hsval : b[12].val = 1 := by simpa using congrArg ZMod.val hs
    have hge : 4096 ≤ bitsVal b := by rw [bitsVal, hsval]; omega
    rw [if_pos hge]

end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

lemma eval_pairExpr (env : Environment Field) (x y xy : Expression Field) (v : Nat) :
    Expression.eval env (pairExpr x y xy v) =
      Select.blockF (Expression.eval env x) (Expression.eval env y)
        (Expression.eval env xy) v := by
  unfold pairExpr Select.blockF
  split_ifs <;> simp [circuit_norm] <;> ring

/-- Affine derivation of the last pair branch of the six-bit inner one-hot. -/
lemma hot6_indicator_remainder (input : fields 13 Field) (a : Nat) (ha : a < 16) :
    (((if a = inner6Index input % 16 then 1 else 0) : Nat) : Field) -
        (((if a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 16+a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 32+a = inner6Index input then 1 else 0) : Nat) : Field) =
      (((if 48+a = inner6Index input then 1 else 0) : Nat) : Field) := by
  have hi := inner6Index_lt input
  split_ifs <;> norm_num <;> omega

/-- Affine derivation of the bit-6 zero branch of the seven-bit inner one-hot. -/
lemma hot7_indicator_remainder (input : fields 13 Field) (a : Nat) (ha : a < 64) :
    (((if a = inner6Index input then 1 else 0) : Nat) : Field) -
        (((if 64+a = innerIndex input then 1 else 0) : Nat) : Field) =
      (((if a = innerIndex input then 1 else 0) : Nat) : Field) := by
  have hi := inner6Index_lt input
  have h6 := xNbit_le input 6 (by omega)
  have hInner : innerIndex input = inner6Index input + 64 * xNbit input 6 (by omega) := rfl
  split_ifs <;> norm_num <;> omega

/-- Affine derivation of the bit-11 zero branch of the five-bit outer one-hot. -/
lemma hot5_indicator_remainder (input : fields 13 Field) (a : Nat) (ha : a < 16) :
    (((if a = outerIndex input % 16 then 1 else 0) : Nat) : Field) -
        (((if 16+a = outerIndex input then 1 else 0) : Nat) : Field) =
      (((if a = outerIndex input then 1 else 0) : Nat) : Field) := by
  have h7 := xNbit_le input 7 (by omega); have h8 := xNbit_le input 8 (by omega)
  have h9 := xNbit_le input 9 (by omega); have h10 := xNbit_le input 10 (by omega)
  have h11 := xNbit_le input 11 (by omega)
  have hOuter : outerIndex input =
      (xNbit input 7 (by omega) + 2*xNbit input 8 (by omega) + 4*xNbit input 9 (by omega) +
        8*xNbit input 10 (by omega)) + 16 * xNbit input 11 (by omega) := by
    unfold outerIndex; ring
  split_ifs <;> norm_num <;> omega

lemma sum8_pair_indicator (e : Nat) (he : e < 32) (T : Nat → Field) :
    ∑ k : Fin 16, ((((if 2*k.val = e then 1 else 0) : Nat) : Field) * T (2*k.val) +
      (((if 2*k.val+1 = e then 1 else 0) : Nat) : Field) * T (2*k.val+1)) = T e := by
  have hk0 : e / 2 < 16 := by omega
  rw [Finset.sum_eq_single (⟨e / 2, hk0⟩ : Fin 16)]
  · rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h1 : 2 * (e / 2) = e := by omega
      have h2 : ¬ (2 * (e / 2) + 1 = e) := by omega
      rw [if_pos h1, if_neg h2, h1]
      norm_num
    · have h1 : ¬ (2 * (e / 2) = e) := by omega
      have h2 : 2 * (e / 2) + 1 = e := by omega
      rw [if_neg h1, if_pos h2, h2]
      norm_num
  · intro j _ hj
    have hjne : j.val ≠ e / 2 := fun h => hj (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega)]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma eval_selected2_eq (env : Environment Field) (input : fields 13 Field)
    (limb : Nat) (hl : limb < 4) (e : Nat) (he : e < 32)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field) (table : Nat → Nat)
    (hpA : ∀ (k : Nat) (hk : k < 16),
      Expression.eval env (pA[16*limb+k]'(by omega)) =
        (((if 2*k = e then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*k) + innerIndex input)) limb : Nat) : Field) +
        (((if 2*k+1 = e then 1 else 0) : Nat) : Field) *
            ((limbOfNat (table (128*(2*k+1) + innerIndex input)) limb : Nat) : Field))
    (hb : ∀ i : Fin 13, IsBool input[i])
    (hidx : e = outerIndex input) :
    Expression.eval env (selected2 limb hl blk h4 h6 h7 pA table) =
      ((limbOfNat (table (magnitudeIndex input)) limb : Nat) : Field) := by
  unfold selected2
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  rw [Finset.sum_congr rfl (fun k : Fin 16 => fun _ => hpA k.val k.isLt)]
  rw [sum8_pair_indicator e he
    (fun j => ((limbOfNat (table (128*j + innerIndex input)) limb : Nat) : Field))]
  have hindex : 128 * outerIndex input + innerIndex input = magnitudeIndex input := by
    rw [← transformedIndex_eq input hb, ← index_split]
  rw [hidx, hindex]
end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 32000000

lemma pairVal_sum (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (p : Nat) (hp : p < 5) :
    pairVal env b p 0 hp + pairVal env b p 1 hp + pairVal env b p 2 hp
      + pairVal env b p 3 hp = 1 := by
  unfold pairVal
  norm_num
  ring


lemma sum_ind_off (n off I : Nat) :
    (∑ a : Fin n, (((if off + a.val = I then 1 else 0) : Nat) : Field))
      = (((if off ≤ I ∧ I < off + n then 1 else 0) : Nat) : Field) := by
  by_cases hI : off ≤ I ∧ I < off + n
  · obtain ⟨hI1, hI2⟩ := hI
    rw [if_pos ⟨hI1, hI2⟩, Finset.sum_eq_single (⟨I - off, by omega⟩ : Fin n)]
    · show (((if off + (I - off) = I then 1 else 0) : Nat) : Field) = _
      rw [if_pos (by omega)]
    · intro j _ hj
      have hjl := j.isLt
      have hne : ¬ (off + j.val = I) := by
        intro hh
        exact hj (Fin.ext (show j.val = I - off by omega))
      rw [if_neg hne]
      norm_num
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · rw [if_neg hI]
    have hI' : ∀ m : Nat, m < n → ¬ (off + m = I) := by
      intro m hm hh
      exact hI ⟨by omega, by omega⟩
    have hz : ∀ j : Fin n, (((if off + j.val = I then 1 else 0) : Nat) : Field) = 0 := by
      intro j
      rw [if_neg (hI' j.val j.isLt)]
      norm_num
    simp only [hz, Finset.sum_const_zero]
    norm_num

/-- Indicator value of every used cell of a nine-product 4x4 one-hot. -/
lemma eval_hot4gen_ind (env : Environment Field) (P0 P1 : Nat → Expression Field)
    (h : Var (fields 9) Field) (A C : Nat) (hA : A < 4) (hC : C < 4)
    (hP0 : ∀ (a : Nat), a < 4 → Expression.eval env (P0 a) =
      (((if A = a then 1 else 0) : Nat) : Field))
    (hP1 : ∀ (c : Nat), c < 4 → Expression.eval env (P1 c) =
      (((if C = c then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 9), Expression.eval env (h[j]'hj) =
      (((if j % 3 + 4 * (j / 3) = A + 4 * C then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 15) :
    Expression.eval env (hot4gen P0 P1 h v) =
      (((if v = A + 4 * C then 1 else 0) : Nat) : Field) := by
  unfold hot4gen
  by_cases ha : v % 4 < 3 <;> by_cases hc : v / 4 < 3
  · rw [dif_pos ha, dif_pos hc, hh (v % 4 + 3 * (v / 4)) (by omega)]
    have a1 : (v % 4 + 3 * (v / 4)) % 3 = v % 4 := by omega
    have a2 : (v % 4 + 3 * (v / 4)) / 3 = v / 4 := by omega
    rw [a1, a2, show v % 4 + 4 * (v / 4) = v by omega]
  · rw [dif_pos ha, dif_neg hc]
    simp only [circuit_norm]
    rw [hP0 (v % 4) (by omega), hh (v % 4) (by omega), hh (v % 4 + 3) (by omega),
      hh (v % 4 + 6) (by omega)]
    have a1 : (v % 4) % 3 = v % 4 := by omega
    have a2 : (v % 4) / 3 = 0 := by omega
    have a3 : (v % 4 + 3) % 3 = v % 4 := by omega
    have a4 : (v % 4 + 3) / 3 = 1 := by omega
    have a5 : (v % 4 + 6) % 3 = v % 4 := by omega
    have a6 : (v % 4 + 6) / 3 = 2 := by omega
    have hvv : v = v % 4 + 12 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    set a := v % 4 with hadef
    have haa : a < 3 := ha
    rw [hvv]
    clear_value a
    interval_cases A <;> interval_cases C <;> interval_cases a <;> norm_num
  · rw [dif_neg ha, dif_pos hc]
    simp only [circuit_norm]
    rw [hP1 (v / 4) (by omega), hh (3 * (v / 4)) (by omega), hh (3 * (v / 4) + 1) (by omega),
      hh (3 * (v / 4) + 2) (by omega)]
    have a1 : (3 * (v / 4)) % 3 = 0 := by omega
    have a2 : (3 * (v / 4)) / 3 = v / 4 := by omega
    have a3 : (3 * (v / 4) + 1) % 3 = 1 := by omega
    have a4 : (3 * (v / 4) + 1) / 3 = v / 4 := by omega
    have a5 : (3 * (v / 4) + 2) % 3 = 2 := by omega
    have a6 : (3 * (v / 4) + 2) / 3 = v / 4 := by omega
    have hvv : v = 3 + 4 * (v / 4) := by omega
    rw [a1, a2, a3, a4, a5, a6]
    set c := v / 4 with hcdef
    have hcc : c < 3 := hc
    rw [hvv]
    clear_value c
    interval_cases A <;> interval_cases C <;> interval_cases c <;> norm_num
  · exfalso; omega

/-- Indicator value of every cell of the forty-five-product six-bit one-hot. -/
lemma eval_inner6Vec_ind (env : Environment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 45) Field) (I : Nat) (hI : I < 64)
    (hP2 : ∀ (c : Nat), c < 4 → Expression.eval env (innerP b w blk 2 (by decide) c) =
      (((if I / 16 = c then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 45), Expression.eval env (h[j]'hj) =
      (((if 16 * (j / 15) + j % 15 = I then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 48) :
    Expression.eval env ((inner6Vec b w blk h)[v]'hv) =
      (((if v = I then 1 else 0) : Nat) : Field) := by
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · rw [hh (15 * (v / 16) + v % 16) (by omega)]
    have d1 : (15 * (v / 16) + v % 16) / 15 = v / 16 := by omega
    have d2 : (15 * (v / 16) + v % 16) % 15 = v % 16 := by omega
    rw [d1, d2, show 16 * (v / 16) + v % 16 = v by omega]
  · have hterm : ∀ a : Fin 15,
        Expression.eval env (h[15 * (v / 16) + a.val]'(by have := a.isLt; omega)) =
          (((if 16 * (v / 16) + a.val = I then 1 else 0) : Nat) : Field) := by
      intro a
      have ha := a.isLt
      rw [hh (15 * (v / 16) + a.val) (by omega)]
      have d1 : (15 * (v / 16) + a.val) / 15 = v / 16 := by omega
      have d2 : (15 * (v / 16) + a.val) % 15 = a.val := by omega
      rw [d1, d2]
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hP2 (v / 16) (by omega), sum_ind_off 15 (16 * (v / 16)) I]
    have hv16 : v = 16 * (v / 16) + 15 := by omega
    rw [hv16]
    set c := v / 16 with hcdef
    clear_value c
    split_ifs <;> norm_num <;> omega

/-- Indicator value of every cell of the sixty-three-product bit-6 layer. -/
lemma eval_inner7Vec_ind (env : Environment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field) (I : Nat) (hI : I < 128)
    (hx6 : Expression.eval env (xExpr b w 6 (by decide)) =
      (((if 64 ≤ I then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 63), Expression.eval env (h[j]'hj) =
      (((if 64 + j = I then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 64) :
    Expression.eval env ((inner7Vec b w h)[v]'hv) =
      (((if 64 + v = I then 1 else 0) : Nat) : Field) := by
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 63,
        Expression.eval env (h[a.val]'a.isLt) =
          (((if 64 + a.val = I then 1 else 0) : Nat) : Field) := fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx6, sum_ind_off 63 64 I, show v = 63 by omega]
    split_ifs <;> norm_num <;> omega



lemma eval_outer5Vec_ind (env : Environment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 15) Field) (I : Nat) (hI : I < 32)
    (hx11 : Expression.eval env (xExpr b w 11 (by decide)) =
      (((if 16 ≤ I then 1 else 0) : Nat) : Field))
    (hh : ∀ (j : Nat) (hj : j < 15), Expression.eval env (h[j]'hj) =
      (((if 16 + j = I then 1 else 0) : Nat) : Field))
    (v : Nat) (hv : v < 16) :
    Expression.eval env ((outer5Vec b w h)[v]'hv) =
      (((if 16 + v = I then 1 else 0) : Nat) : Field) := by
  rw [outer5Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 15,
        Expression.eval env (h[a.val]'a.isLt) =
          (((if 16 + a.val = I then 1 else 0) : Nat) : Field) := fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx11, sum_ind_off 15 16 I, show v = 15 by omega]
    split_ifs <;> norm_num <;> omega

/-- Prover-side value of every used cell of a nine-product 4x4 one-hot. -/
lemma eval_hot4gen_val (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (P0 P1 : Nat → Expression Field) (h : Var (fields 9) Field)
    (p : Nat) (hp : p < 4)
    (hP0 : ∀ (a : Nat), a < 4 → Expression.eval env.toEnvironment (P0 a) =
      pairVal env b p a (by omega))
    (hP1 : ∀ (c : Nat), c < 4 → Expression.eval env.toEnvironment (P1 c) =
      pairVal env b (p+1) c (by omega))
    (hh : ∀ (j : Nat) (hj : j < 9), Expression.eval env.toEnvironment (h[j]'hj) =
      hot4Val env b p (j % 3 + 4 * (j / 3)) (by omega))
    (v : Nat) (hv : v < 15) :
    Expression.eval env.toEnvironment (hot4gen P0 P1 h v) = hot4Val env b p v (by omega) := by
  have hhj : ∀ (j : Nat) (hj : j < 9),
      Expression.eval env.toEnvironment (h[j]'hj) =
        pairVal env b p (j % 3) (by omega) * pairVal env b (p+1) (j / 3) (by omega) := by
    intro j hj
    rw [hh j hj]
    unfold hot4Val
    have h1 : (j % 3 + 4 * (j / 3)) % 4 = j % 3 := by omega
    have h2 : (j % 3 + 4 * (j / 3)) / 4 = j / 3 := by omega
    rw [h1, h2]
  have hsumA := pairVal_sum env b p (by omega)
  have hsumB := pairVal_sum env b (p+1) (by omega)
  unfold hot4gen
  split_ifs with ha hc hc <;> simp only [circuit_norm]
  · rw [hhj (v % 4 + 3 * (v / 4)) (by omega)]
    have a1 : (v % 4 + 3 * (v / 4)) % 3 = v % 4 := by omega
    have a2 : (v % 4 + 3 * (v / 4)) / 3 = v / 4 := by omega
    rw [a1, a2]
    unfold hot4Val
    norm_num
  · rw [hP0 (v % 4) (by omega), hhj (v % 4) (by omega), hhj (v % 4 + 3) (by omega),
      hhj (v % 4 + 6) (by omega)]
    have a1 : (v % 4) % 3 = v % 4 := by omega
    have a2 : (v % 4) / 3 = 0 := by omega
    have a3 : (v % 4 + 3) % 3 = v % 4 := by omega
    have a4 : (v % 4 + 3) / 3 = 1 := by omega
    have a5 : (v % 4 + 6) % 3 = v % 4 := by omega
    have a6 : (v % 4 + 6) / 3 = 2 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    unfold hot4Val
    have hv4 : v / 4 = 3 := by omega
    rw [hv4]
    norm_num
    linear_combination (-(pairVal env b p (v % 4) (by omega))) * hsumB
  · rw [hP1 (v / 4) (by omega), hhj (3 * (v / 4)) (by omega), hhj (3 * (v / 4) + 1) (by omega),
      hhj (3 * (v / 4) + 2) (by omega)]
    have a1 : (3 * (v / 4)) % 3 = 0 := by omega
    have a2 : (3 * (v / 4)) / 3 = v / 4 := by omega
    have a3 : (3 * (v / 4) + 1) % 3 = 1 := by omega
    have a4 : (3 * (v / 4) + 1) / 3 = v / 4 := by omega
    have a5 : (3 * (v / 4) + 2) % 3 = 2 := by omega
    have a6 : (3 * (v / 4) + 2) / 3 = v / 4 := by omega
    rw [a1, a2, a3, a4, a5, a6]
    unfold hot4Val
    have hv4 : v % 4 = 3 := by omega
    rw [hv4]
    norm_num
    linear_combination (-(pairVal env b (p+1) (v / 4) (by omega))) * hsumA
  · exfalso; omega

/-- The sixteen cells of a four-bit one-hot sum to one. -/
lemma hot4Val_sum15 (env : ProverEnvironment Field) (b : Var (fields 13) Field)
    (p : Nat) (hp : p < 4) :
    (∑ a : Fin 15, hot4Val env b p a.val (by omega)) + hot4Val env b p 15 (by omega) = 1 := by
  simp only [hot4Val, pairVal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- The sixty-four cells of the six-bit inner one-hot sum to one. -/
lemma hot6Val_sum63 (env : ProverEnvironment Field) (b : Var (fields 13) Field) :
    (∑ a : Fin 63, hot6Val env b a.val) + hot6Val env b 63 = 1 := by
  simp only [hot6Val, hot4Val, pairVal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- Prover-side value of every cell of the forty-five-product six-bit one-hot. -/
lemma eval_inner6Vec_val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 45) Field)
    (hP2 : ∀ (c : Nat), c < 4 →
      Expression.eval env.toEnvironment (innerP b w blk 2 (by decide) c) =
        pairVal env b 2 c (by omega))
    (hh : ∀ (j : Nat) (hj : j < 45), Expression.eval env.toEnvironment (h[j]'hj) =
      hot6Val env b (16 * (j / 15) + j % 15))
    (v : Nat) (hv : v < 48) :
    Expression.eval env.toEnvironment ((inner6Vec b w blk h)[v]'hv) = hot6Val env b v := by
  rw [inner6Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · rw [hh (15 * (v / 16) + v % 16) (by omega)]
    have d1 : (15 * (v / 16) + v % 16) / 15 = v / 16 := by omega
    have d2 : (15 * (v / 16) + v % 16) % 15 = v % 16 := by omega
    rw [d1, d2, show 16 * (v / 16) + v % 16 = v by omega]
  · have hterm : ∀ a : Fin 15,
        Expression.eval env.toEnvironment (h[15 * (v / 16) + a.val]'(by have := a.isLt; omega)) =
          hot4Val env b 0 a.val (by omega) * pairVal env b 2 (v / 16) (by omega) := by
      intro a
      have ha := a.isLt
      rw [hh (15 * (v / 16) + a.val) (by omega)]
      have d1 : (15 * (v / 16) + a.val) / 15 = v / 16 := by omega
      have d2 : (15 * (v / 16) + a.val) % 15 = a.val := by omega
      rw [d1, d2]
      unfold hot6Val
      have e1 : (16 * (v / 16) + a.val) % 16 = a.val := by omega
      have e2 : (16 * (v / 16) + a.val) / 16 = v / 16 := by omega
      rw [e1, e2]
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hP2 (v / 16) (by omega), ← Finset.sum_mul]
    have hs := hot4Val_sum15 env b 0 (by omega)
    have hgoal : hot6Val env b v = hot4Val env b 0 15 (by omega) * pairVal env b 2 (v / 16) (by omega) := by
      unfold hot6Val
      have e1 : v % 16 = 15 := by omega
      rw [e1]
    rw [hgoal]
    linear_combination (-(pairVal env b 2 (v / 16) (by omega))) * hs

/-- Prover-side value of every cell of the sixty-three-product bit-6 layer. -/
lemma eval_inner7Vec_val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 63) Field)
    (hx6 : Expression.eval env.toEnvironment (xExpr b w 6 (by decide)) =
      xVal env b 6 (by decide))
    (hh : ∀ (j : Nat) (hj : j < 63), Expression.eval env.toEnvironment (h[j]'hj) =
      hot6Val env b j * xVal env b 6 (by decide))
    (v : Nat) (hv : v < 64) :
    Expression.eval env.toEnvironment ((inner7Vec b w h)[v]'hv) =
      hot6Val env b v * xVal env b 6 (by decide) := by
  rw [inner7Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 63,
        Expression.eval env.toEnvironment (h[a.val]'a.isLt) =
          hot6Val env b a.val * xVal env b 6 (by decide) := fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx6, ← Finset.sum_mul, show v = 63 by omega]
    have hs := hot6Val_sum63 env b
    linear_combination (-(xVal env b 6 (by decide))) * hs


/-- Prover-side value of every cell of the fifteen-product bit-11 outer layer. -/
lemma eval_outer5Vec_val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (h : Var (fields 15) Field)
    (hx11 : Expression.eval env.toEnvironment (xExpr b w 11 (by decide)) =
      xVal env b 11 (by decide))
    (hh : ∀ (j : Nat) (hj : j < 15), Expression.eval env.toEnvironment (h[j]'hj) =
      hot4Val env b 3 j (by omega) * xVal env b 11 (by decide))
    (v : Nat) (hv : v < 16) :
    Expression.eval env.toEnvironment ((outer5Vec b w h)[v]'hv) =
      hot4Val env b 3 v (by omega) * xVal env b 11 (by decide) := by
  rw [outer5Vec, Vector.getElem_ofFn]
  dsimp only
  split <;> rename_i hk
  · exact hh v hk
  · have hterm : ∀ a : Fin 15,
        Expression.eval env.toEnvironment (h[a.val]'a.isLt) =
          hot4Val env b 3 a.val (by omega) * xVal env b 11 (by decide) :=
      fun a => hh a.val a.isLt
    simp only [circuit_norm]
    rw [Select.eval_foldl_add]
    simp only [hterm]
    rw [hx11, ← Finset.sum_mul, show v = 15 by omega]
    have hs := hot4Val_sum15 env b 3 (by omega)
    linear_combination (-(xVal env b 11 (by decide))) * hs



end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096

lemma eval_pairExpr_eq_pairVal (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (w : Var (fields 12) Field)
    (blk : Var (fields 5) Field)
    (hx : ∀ (i : Nat) (hi : i < 12),
      Expression.eval env.toEnvironment (xExpr b w i hi) = xVal env b i hi)
    (hblk : ∀ (p : Nat) (hp : p < 5),
      Expression.eval env.toEnvironment (blk[p]'hp) =
        xVal env b (pairLo p) (pairLo_lt hp) * xVal env b (pairLo p + 1) (pairLo_add_lt hp))
    (p v : Nat) (hp : p < 5) (hv : v < 4) :
    Expression.eval env.toEnvironment
        (pairExpr (xExpr b w (pairLo p) (pairLo_lt hp))
          (xExpr b w (pairLo p + 1) (pairLo_add_lt hp)) blk[p] v) =
      pairVal env b p v hp := by
  interval_cases v <;> norm_num [pairExpr, pairVal] <;> simp only [circuit_norm]
  all_goals try rw [hx (pairLo p) (pairLo_lt hp)]
  all_goals try rw [hx (pairLo p + 1) (pairLo_add_lt hp)]
  all_goals rw [hblk p hp]
  all_goals ring

lemma eval_hot4_eq_hot4Val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h : Var (fields 15) Field) (base : Nat) (hbase : base < 4)
    (hblk : ∀ (p : Nat) (hp : p < 5),
      Expression.eval env.toEnvironment (blk[p]'hp) =
        xVal env b (pairLo p) (pairLo_lt hp) * xVal env b (pairLo p + 1) (pairLo_add_lt hp))
    (hh : ∀ (v : Nat) (hv : v < 15),
      Expression.eval env.toEnvironment (h[v]'hv) = hot4Val env b base v hbase)
    (v : Nat) (hv : v < 16) :
    Expression.eval env.toEnvironment (hot4 blk h base hbase v hv) =
      hot4Val env b base v hbase := by
  unfold hot4
  split
  · subst v
    simp only [Expression.eval, circuit_norm]
    rw [hblk (base+1) (by omega), hh 12 (by omega), hh 13 (by omega), hh 14 (by omega)]
    norm_num [hot4Val, pairVal]
    ring
  · exact hh v (by omega)

lemma eval_hot6_eq_hot6Val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field)
    (hh4 : ∀ (v : Nat) (hv : v < 16),
      Expression.eval env.toEnvironment (hot4 blk h4 0 (by omega) v hv) =
        hot4Val env b 0 v (by omega))
    (hh6 : ∀ (v : Nat) (hv : v < 48),
      Expression.eval env.toEnvironment (h6[v]'hv) = hot6Val env b v)
    (v : Nat) (hv : v < 64) :
    Expression.eval env.toEnvironment (hot6 blk h4 h6 v hv) = hot6Val env b v := by
  unfold hot6
  dsimp only
  split
  · have heq : v / 16 * 16 + v % 16 = v := by omega
    simpa only [heq] using hh6 (v / 16 * 16 + v % 16) (by omega)
  · simp only [Expression.eval, circuit_norm]
    rw [hh4 _ (by omega), hh6 (v%16) (by omega), hh6 (16+v%16) (by omega),
      hh6 (32+v%16) (by omega)]
    have hvq : v / 16 = 3 := by omega
    have he0 : hot6Val env b (v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 0 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he1 : hot6Val env b (16+v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 1 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he2 : hot6Val env b (32+v%16) =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 2 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    have he3 : hot6Val env b v =
        hot4Val env b 0 (v%16) (by omega) * pairVal env b 2 3 (by omega) := by
      unfold hot6Val
      congr 2 <;> omega
    rw [he0, he1, he2, he3]
    norm_num [pairVal]
    ring

lemma eval_hot7_eq_hot7Val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hh6 : ∀ (v : Nat) (hv : v < 64),
      Expression.eval env.toEnvironment (hot6 blk h4 h6 v hv) = hot6Val env b v)
    (hh7 : ∀ (a : Nat) (ha : a < 64),
      Expression.eval env.toEnvironment (h7[a]'ha) = hot7Val env b (64+a))
    (v : Nat) (hv : v < 128) :
    Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v := by
  unfold hot7
  dsimp only
  split
  · rw [hh7]
    congr 1
    omega
  · simp only [Expression.eval, circuit_norm]
    rw [hh6 _ (by omega), hh7]
    have hvq : v / 64 = 0 := by omega
    have he0 : hot7Val env b v =
        hot6Val env b (v%64) * (1 - xVal env b 6 (by omega)) := by
      unfold hot7Val
      rw [if_neg (by omega)]
    have he1 : hot7Val env b (64+v%64) =
        hot6Val env b (v%64) * xVal env b 6 (by omega) := by
      unfold hot7Val
      rw [if_pos (by omega)]
      congr 2 <;> omega
    rw [he0, he1]
    ring


lemma eval_hot5_eq_hot5Val (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h4o : Var (fields 15) Field) (h5 : Var (fields 16) Field)
    (hh4 : ∀ (v : Nat) (hv : v < 16),
      Expression.eval env.toEnvironment (hot4 blk h4o 3 (by omega) v hv) =
        hot4Val env b 3 v (by omega))
    (hh5 : ∀ (a : Nat) (ha : a < 16),
      Expression.eval env.toEnvironment (h5[a]'ha) = hot5Val env b (16+a))
    (v : Nat) (hv : v < 32) :
    Expression.eval env.toEnvironment (hot5 blk h4o h5 v hv) = hot5Val env b v := by
  unfold hot5
  dsimp only
  split
  · rw [hh5]
    congr 1
    omega
  · simp only [Expression.eval, circuit_norm]
    rw [hh4 _ (by omega), hh5]
    have he0 : hot5Val env b v =
        hot4Val env b 3 (v%16) (by omega) * (1 - xVal env b 11 (by omega)) := by
      unfold hot5Val
      rw [if_neg (by omega)]
    have he1 : hot5Val env b (16+v%16) =
        hot4Val env b 3 (v%16) (by omega) * xVal env b 11 (by omega) := by
      unfold hot5Val
      rw [if_pos (by omega)]
      congr 2 <;> omega
    rw [he0, he1]
    ring


lemma eval_inner_eq_innerVal (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hhot : ∀ (v : Nat) (hv : v < 128),
      Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v)
    (limb outer : Nat) (table : Nat → Nat) :
    Expression.eval env.toEnvironment (inner limb outer blk h4 h6 h7 table) =
      innerVal env b limb outer table := by
  unfold inner innerVal
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Expression.eval]
  rw [hhot a.val a.isLt]

lemma eval_corrC_eq_corrVal (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (hhot : ∀ (v : Nat) (hv : v < 128),
      Expression.eval env.toEnvironment (hot7 blk h4 h6 h7 v hv) = hot7Val env b v)
    (limb o0 o1 : Nat) (table : Nat → Nat) :
    Expression.eval env.toEnvironment (corrC limb o0 o1 blk h4 h6 h7 table) =
      corrVal env b limb o0 o1 table := by
  unfold corrC corrVal
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Expression.eval]
  rw [hhot a.val a.isLt]

end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
lemma eval_selected2_eq_selectedVal2 (env : ProverEnvironment Field)
    (b : Var (fields 13) Field) (limb : Nat) (hl : limb < 4)
    (blk : Var (fields 5) Field)
    (h4 : Var (fields 15) Field) (h6 : Var (fields 48) Field) (h7 : Var (fields 64) Field)
    (pA : Var (fields 64) Field) (table : Nat → Nat)
    (hpA : ∀ (k : Nat) (hk : k < 64),
      Expression.eval env.toEnvironment (pA[k]'hk) =
        outProdVal env b (k/16) (k % 16) table) :
    Expression.eval env.toEnvironment (selected2 limb hl blk h4 h6 h7 pA table) =
      selectedVal2 env b limb table := by
  unfold selected2 selectedVal2
  simp only [circuit_norm]
  rw [Select.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro k _
  have hk := k.isLt
  rw [hpA (16*limb+k.val) (by omega)]
  rw [show (16*limb+k.val) / 16 = limb by omega, show (16*limb+k.val) % 16 = k.val by omega]
end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase.Select13

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

section ValueOneHot

/-! Value-level one-hot facts: with Boolean inputs the *witness values* computed
by the selector are the expected indicator functions.  These mirror the
constraint-level facts derived inside `soundness`, and are what the completeness
proof needs in order to discharge the borrow-bit rows. -/

variable {env : ProverEnvironment Field} {b : Var (fields 13) Field} {input : fields 13 Field}

lemma xVal_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj)) (i : Nat) (hi : i < 12) :
    xVal env b i hi = ((xNbit input i hi : Nat) : Field) := by
  unfold xVal bitVal
  rw [hin 12 (by omega), hin i (by omega)]
  have h := Select.xnor_val (hb 12 (by omega)) (hb i (by omega))
  simp only [xNbit]
  linear_combination h

lemma pairVal_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj))
    (p v : Nat) (hp : p < 5) (hv : v < 4) :
    pairVal env b p v hp =
      (((if xNbit input (pairLo p) (pairLo_lt hp) +
            2 * xNbit input (pairLo p + 1) (pairLo_add_lt hp) = v then 1 else 0) : Nat) : Field) := by
  unfold pairVal
  simp only
  rw [xVal_ind hin hb (pairLo p) (pairLo_lt hp), xVal_ind hin hb (pairLo p + 1) (pairLo_add_lt hp),
    Select.sign_factor _ (v % 2) (xNbit_le _ _ _) (by omega),
    Select.sign_factor _ (v / 2 % 2) (xNbit_le _ _ _) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input (pairLo p) (pairLo_lt hp)
  have h1 := xNbit_le input (pairLo p + 1) (pairLo_add_lt hp)
  constructor <;> intro hh <;> omega

lemma hot4Val_outer_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj)) (v : Nat) (hv : v < 16) :
    hot4Val env b 3 v (by omega) =
      (((if v = outerIndex input % 16 then 1 else 0) : Nat) : Field) := by
  unfold hot4Val
  rw [pairVal_ind hin hb 3 (v % 4) (by omega) (by omega),
    pairVal_ind hin hb 4 (v / 4) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h7 := xNbit_le input 7 (by omega); have h8 := xNbit_le input 8 (by omega)
  have h9 := xNbit_le input 9 (by omega); have h10 := xNbit_le input 10 (by omega)
  have h11 := xNbit_le input 11 (by omega)
  simp only [pairLo, Nat.reduceAdd, outerIndex]
  constructor <;> intro hh <;> omega

lemma hot4Val_inner_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj)) (v : Nat) (hv : v < 16) :
    hot4Val env b 0 v (by omega) =
      (((if v = inner6Index input % 16 then 1 else 0) : Nat) : Field) := by
  unfold hot4Val
  rw [pairVal_ind hin hb 0 (v % 4) (by omega) (by omega),
    pairVal_ind hin hb 1 (v / 4) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input 0 (by omega); have h1 := xNbit_le input 1 (by omega)
  have h2 := xNbit_le input 2 (by omega); have h3 := xNbit_le input 3 (by omega)
  have h4 := xNbit_le input 4 (by omega); have h5 := xNbit_le input 5 (by omega)
  simp only [pairLo, Nat.reduceAdd, inner6Index]
  constructor <;> intro hh <;> omega

lemma hot6Val_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj)) (v : Nat) (hv : v < 64) :
    hot6Val env b v = (((if v = inner6Index input then 1 else 0) : Nat) : Field) := by
  unfold hot6Val
  rw [hot4Val_inner_ind hin hb (v % 16) (by omega),
    pairVal_ind hin hb 2 (v / 16) (by omega) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h0 := xNbit_le input 0 (by omega); have h1 := xNbit_le input 1 (by omega)
  have h2 := xNbit_le input 2 (by omega); have h3 := xNbit_le input 3 (by omega)
  have h4 := xNbit_le input 4 (by omega); have h5 := xNbit_le input 5 (by omega)
  simp only [pairLo, Nat.reduceAdd, inner6Index]
  constructor <;> intro hh <;> omega

lemma hot7Val_ind (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj)) (v : Nat) (hv : v < 128) :
    hot7Val env b v = (((if v = innerIndex input then 1 else 0) : Nat) : Field) := by
  unfold hot7Val
  rw [hot6Val_ind hin hb (v % 64) (by omega), xVal_ind hin hb 6 (by omega),
    Select.sign_factor _ (v / 64) (xNbit_le _ _ _) (by omega)]
  refine Select.ind_indicator_mul_eq ?_
  have h6 := xNbit_le input 6 (by omega)
  have hi6 := inner6Index_lt input
  simp only [innerIndex]
  constructor <;> intro hh <;> omega

lemma innerVal_const (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj)
    (hb : ∀ (j : Nat) (hj : j < 13), IsBool (input[j]'hj))
    (limb outer : Nat) (table : Nat -> Nat) :
    innerVal env b limb outer table =
      ((limbOfNat (table (128 * outer + innerIndex input)) limb : Nat) : Field) := by
  unfold innerVal
  rw [Finset.sum_congr rfl (fun a _ => by rw [hot7Val_ind hin hb a.val a.isLt])]
  exact Select.one_hot_sum 128
    (fun a : Fin 128 => (((limbOfNat (table (128*outer+a.val)) limb : Nat) : Field)))
    (innerIndex input) (innerIndex_lt input) _ (fun _ => rfl)
lemma magIdxOf_eq (hin : ∀ (j : Nat) (hj : j < 13),
      Expression.eval env.toEnvironment (b[j]'hj) = input[j]'hj) :
    magIdxOf env b = magnitudeIndex input := by
  unfold magIdxOf
  congr 1
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  exact hin i hi

end ValueOneHot


end Solution.Secp256k1ScalarMulFixedBase.Select13



namespace Solution.Secp256k1ScalarMulFixedBase
namespace Select13


end Select13
end Solution.Secp256k1ScalarMulFixedBase

end DonorFile5_15
