

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq

open Nat

def a : ℕ := 7629217
def m : ℕ := 11184810

variable {n : ℕ}


lemma a_1mod2 : a ≡ 1 [MOD 2] := by decide
lemma a_1mod3 : a ≡ 1 [MOD 3] := by decide
lemma a_2mod5 : a ≡ 2 [MOD 5] := by decide
lemma a_1mod7 : a ≡ 1 [MOD 7] := by decide
lemma a_11mod13 : a ≡ 11 [MOD 13] := by decide
lemma a_8mod17 : a ≡ 8 [MOD 17] := by decide
lemma a_121mod241 : a ≡ 121 [MOD 241] := by decide

lemma n_aMODm_implies_n_1MOD2 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 2] := by
  have hm : 2 ∣ m := by decide
  have : n ≡ a [MOD 2] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod2
lemma n_aMODm_implies_n_1MOD3 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 3] := by
  have hm : 3 ∣ m := by decide
  have : n ≡ a [MOD 3] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod3
lemma n_aMODm_implies_n_2MOD5 (h : n ≡ a [MOD m]) :
    n ≡ 2 [MOD 5] := by
  have hm : 5 ∣ m := by decide
  have : n ≡ a [MOD 5] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_2mod5
lemma n_aMODm_implies_n_1MOD7 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 7] := by
  have hm : 7 ∣ m := by decide
  have : n ≡ a [MOD 7] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod7
lemma n_aMODm_implies_n_11MOD13 (h : n ≡ a [MOD m]) :
    n ≡ 11 [MOD 13] := by
  have hm : 13 ∣ m := by decide
  have : n ≡ a [MOD 13] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_11mod13
lemma n_aMODm_implies_n_8MOD17 (h : n ≡ a [MOD m]) :
    n ≡ 8 [MOD 17] := by
  have hm : 17 ∣ m := by decide
  have : n ≡ a [MOD 17] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_8mod17
lemma n_aMODm_implies_n_121MOD241 (h : n ≡ a [MOD m]) :
    n ≡ 121 [MOD 241] := by
  have hm : 241 ∣ m := by decide
  have : n ≡ a [MOD 241] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_121mod241


lemma cover (k : ℕ) :
    k ≡ 0 [MOD 2] ∨ k ≡ 0 [MOD 3] ∨ k ≡ 1 [MOD 4] ∨
    k ≡ 3 [MOD 8] ∨ k ≡ 7 [MOD 12] ∨ k ≡ 23 [MOD 24] := by
  let r := k % 24
  have hk : k ≡ r [MOD 24] := by exact ModEq.symm (mod_modEq k 24)
  have hr : r < 24 := Nat.mod_lt k (by norm_num)
  interval_cases r
  · left -- 0 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    exact Nat.ModEq.of_dvd this hk
  · right; right; left -- 1 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    exact Nat.ModEq.of_dvd this hk
  · left -- 2 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 2 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 3 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 3 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 4 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 4 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 5 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 5 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 6 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 6 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; right; left -- 7 mod 24 -> 7 mod 12
    have : 12 ∣ 24 := by decide
    have : k ≡ 7 [MOD 12] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 8 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 8 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 9 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 9 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 10 mod 24 -> 0 omd 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 10 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; left -- 11 mod 24 -> 3 mod 8
    have : 8 ∣ 24 := by decide
    have : k ≡ 11 [MOD 8] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 12
    have : 2 ∣ 24 := by decide
    have : k ≡ 12 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 13 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 13 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 14
    have : 2 ∣ 24 := by decide
    have : k ≡ 14 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 15 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 15 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 16
    have : 2 ∣ 24 := by decide
    have : k ≡ 16 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 17 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 17 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 18 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 18 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; left -- 19 mod 24 -> 3 mod 8
    have : 8 ∣ 24 := by decide
    have : k ≡ 19 [MOD 8] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 20
    have : 2 ∣ 24 := by decide
    have : k ≡ 20 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 21 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 21 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 22
    have : 2 ∣ 24 := by decide
    have : k ≡ 22 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; right; right
    apply hk



lemma branch_k_0mod2_forces_3mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 0 [MOD 2])
    (hrep : n = p + 2 ^ k) :
    3 ∣ p := by
  have : 2 ∣ k := by exact dvd_of_mod_eq_zero hk
  obtain ⟨t, ht⟩ := this
  have h_4power : 2 ^ k = 4 ^ t := by
    rw [ht]; rw [pow_mul]; norm_num
  have : 4 ≡ 1 [MOD 3] := by decide
  have h_2k : 4 ^ t ≡ 1 ^ t [MOD 3] := by exact ModEq.pow t this
  simp only [one_pow] at h_2k; rw [← h_4power] at h_2k
  have h_1mod3 : n ≡ 1 [MOD 3] := by exact n_aMODm_implies_n_1MOD3 hn
  rw [hrep] at h_1mod3
  have hp : p + 2 ^ k - 2 ^ k ≡ 1 - 1 [MOD 3] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact NeZero.one_le)
      h_1mod3
      h_2k
  have : p ≡ 0 [MOD 3] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_0mod3_forces_7mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 0 [MOD 3])
    (hrep : n = p + 2 ^ k) :
    7 ∣ p := by
  have : 3 ∣ k := by exact dvd_of_mod_eq_zero hk
  obtain ⟨t, ht⟩ := this
  have h_8power : 2 ^ k = 8 ^ t := by
    rw [ht]; rw [pow_mul]; norm_num
  have : 8 ≡ 1 [MOD 7] := by decide
  have h_2k : 8 ^ t ≡ 1 ^ t [MOD 7] := by exact ModEq.pow t this
  simp only [one_pow] at h_2k; rw [← h_8power] at h_2k
  have h_1mod7 : n ≡ 1 [MOD 7] := by exact n_aMODm_implies_n_1MOD7 hn
  rw [hrep] at h_1mod7
  have hp : p + 2 ^ k - 2 ^ k ≡ 1 - 1 [MOD 7] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact NeZero.one_le)
      h_1mod7
      h_2k
  have : p ≡ 0 [MOD 7] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_1mod4_forces_5mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 1 [MOD 4])
    (hrep : n = p + 2 ^ k) :
    5 ∣ p := by
  have : 1 ≡ k [MOD 4] := by exact ModEq.symm hk
  have k_pos : 1 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact one_lt_succ_succ (k + 2))
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 2 * 16 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^4 = 16)]
  have : 16 ≡ 1 [MOD 5] := by decide
  have h_16t : 16 ^ t ≡ 1 ^ t [MOD 5] := by exact ModEq.pow t this
  simp only [one_pow] at h_16t;
  have h_2k : 2 * 16 ^ t ≡ 2 [MOD 5] := by exact ModEq.mul_left 2 h_16t
  rw [← h_k_by_t] at h_2k
  have h_2mod5 : n ≡ 2 [MOD 5] := by exact n_aMODm_implies_n_2MOD5 hn
  rw [hrep] at h_2mod5
  have hp : p + 2 ^ k - 2 ^ k ≡ 2 - 2 [MOD 5] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact AtLeastTwo.prop)
      h_2mod5
      h_2k
  have : p ≡ 0 [MOD 5] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_3mod8_forces_17mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 3 [MOD 8])
    (hrep : n = p + 2 ^ k) :
    17 ∣ p := by
  have : 3 ≡ k [MOD 8] := by exact ModEq.symm hk
  have k_pos : 3 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 8 * 256 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^8 = 256)]
  have : 256 ≡ 1 [MOD 17] := by decide
  have h_256t : 256 ^ t ≡ 1 ^ t [MOD 17] := by exact ModEq.pow t this
  simp only [one_pow] at h_256t;
  have h_2k : 8 * 256 ^ t ≡ 8 [MOD 17] := by exact ModEq.mul_left 8 h_256t
  rw [← h_k_by_t] at h_2k
  have h_8mod17 : n ≡ 8 [MOD 17] := by exact n_aMODm_implies_n_8MOD17 hn
  rw [hrep] at h_8mod17
  have hp : p + 2 ^ k - 2 ^ k ≡ 8 - 8 [MOD 17] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_8mod17
      h_2k
  have : p ≡ 0 [MOD 17] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_7mod12_forces_13mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 7 [MOD 12])
    (hrep : n = p + 2 ^ k) :
    13 ∣ p := by
  have : 7 ≡ k [MOD 12] := by exact ModEq.symm hk
  have k_pos : 7 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 128 * 4096 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^12 = 4096)]
  have : 4096 ≡ 1 [MOD 13] := by decide
  have h_4096t : 4096 ^ t ≡ 1 ^ t [MOD 13] := by exact ModEq.pow t this
  simp only [one_pow] at h_4096t;
  have h_2k : 128 * 4096 ^ t ≡ 128 [MOD 13] := by exact ModEq.mul_left 128 h_4096t
  rw [← h_k_by_t] at h_2k
  have h_11mod13 : n ≡ 11 [MOD 13] := by exact n_aMODm_implies_n_11MOD13 hn
  rw [hrep] at h_11mod13
  have hp : p + 2 ^ k - 2 ^ k ≡ 11 - 11 [MOD 13] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_11mod13
      h_2k
  have : p ≡ 0 [MOD 13] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_23mod24_forces_241mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 23 [MOD 24])
    (hrep : n = p + 2 ^ k) :
    241 ∣ p := by
  have : 23 ≡ k [MOD 24] := by exact ModEq.symm hk
  have k_pos : 23 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 8388608 * 16777216 ^ t := by -- 2^23=8388608, 2^24=16777216
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^24 = 16777216)]
  have : 16777216 ≡ 1 [MOD 241] := by decide
  have h_16777216t : 16777216 ^ t ≡ 1 ^ t [MOD 241] := by exact ModEq.pow t this
  simp only [one_pow] at h_16777216t;
  have h_2k : 8388608 * 16777216 ^ t ≡ 8388608 [MOD 241] := by
    exact ModEq.mul_left 8388608 h_16777216t
  rw [← h_k_by_t] at h_2k
  have h_121mod241 : n ≡ 121 [MOD 241] := by exact n_aMODm_implies_n_121MOD241 hn
  rw [hrep] at h_121mod241
  have hp : p + 2 ^ k - 2 ^ k ≡ 121 - 121 [MOD 241] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_121mod241
      h_2k
  have : p ≡ 0 [MOD 241] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this







theorem exists_progression_no_prime_add_pow_two (hn : n ≡ a [MOD m]) :
    n ≡ a [MOD m] → ¬ ∃ (p k : ℕ), p.Prime ∧ n = p + 2^k := by
  sorry
