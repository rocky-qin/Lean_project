import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

import Mathlib.Tactic.IntervalCases

open Nat

def a : ℕ := 7629217
def m : ℕ := 11184810

lemma m_divisors :
  2 ∣ m ∧ 3 ∣ m ∧ 5 ∣ m ∧ 7 ∣ m ∧ 13 ∣ m ∧ 17 ∣ m ∧ 241 ∣ m := by decide

lemma dvd_m_2 : 2   ∣ m := by norm_num[m]
lemma dvd_m_3 : 3   ∣ m := by norm_num[m]
lemma dvd_m_5 : 5   ∣ m := by norm_num[m]
lemma dvd_m_7 : 7   ∣ m := by norm_num[m]
lemma dvd_m_13 : 13  ∣ m := by norm_num[m]
lemma dvd_m_17 : 17  ∣ m := by norm_num[m]
lemma dvd_m_241 : 241 ∣ m := by norm_num[m]


lemma a_mod2 : a ≡ 1 [MOD 2] := by norm_num [a]
lemma a_mod3 : a ≡ 1 [MOD 3] := by norm_num [a]
lemma a_mod5 : a ≡ 2 [MOD 5] := by norm_num [a]
lemma a_mod7 : a ≡ 1 [MOD 7] := by norm_num [a]
lemma a_mod13 : a ≡ 11 [MOD 13] := by norm_num [a]
lemma a_mod17 : a ≡ 8 [MOD 17] := by norm_num [a]
lemma a_mod241 : a ≡ 121 [MOD 241] := by norm_num [a]

variable {n : ℕ} (hn : n ≡ a [MOD m])

-- modEq.of_dvd : d ∣ m  n ≡ a MOD m   =>   n ≡ a MOD d
-- then use a_mod_d (a ≡ r MOD d) and transtivity
-- finally n ≡ r MOD d


-- notice that we have m_divisors, we can use right right left to choose
-- to be convinient we write another 7 lemmas with dvd
theorem n_mod2 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 2] :=
  ModEq.trans (ModEq.of_dvd m_divisors.left h) a_mod2
theorem n_mod3 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 3] :=
  ModEq.trans (ModEq.of_dvd m_divisors.right.left h) a_mod3
theorem n_mod5 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 2 [MOD 5] :=
  ModEq.trans (ModEq.of_dvd m_divisors.right.right.left h) a_mod5
theorem n_mod7 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 7] :=
  ModEq.trans (ModEq.of_dvd dvd_m_7 h) a_mod7
theorem n_mod13 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 11 [MOD 13] :=
  ModEq.trans (ModEq.of_dvd dvd_m_13 h) a_mod13
theorem n_mod17 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 8 [MOD 17] :=
  ModEq.trans (ModEq.of_dvd dvd_m_17 h) a_mod17
theorem n_mod241 (n : Nat) (h : n ≡ a [MOD m]) : n ≡ 121 [MOD 241] :=
  ModEq.trans (ModEq.of_dvd dvd_m_241 h) a_mod241


-- STAGE 2--

lemma modeq_descend {k r m d : Nat} (h : k ≡ r [MOD m]) (hd : d ∣ m) :
    k ≡ r [MOD d] :=
  Nat.Mod.modEq_of_dvd hd h


lemma cover (k : Nat) :
  k ≡ 0 [MOD 2] ∨
  k ≡ 0 [MOD 3] ∨
  k ≡ 1 [MOD 4] ∨
  k ≡ 3 [MOD 8] ∨
  k ≡ 7 [MOD 12] ∨
  k ≡ 23 [MOD 24] := by
  let r := k % 24
  have hr : r < 24 := Nat.mod_lt k (by norm_num)
  have hk : k ≡ r [MOD 24] := (Nat.mod_modEq k 24).symm

  -- 对 r 从 0 到 23 进行暴力分类讨论
  interval_cases r
  -- 下面是 24 个分支的自动化处理
  -- 情况 r = 0: 0 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 1: 1 ≡ 1 [MOD 4]
  · right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 2: 2 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 3: 3 ≡ 0 [MOD 3]
  · right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 4: 4 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 5: 5 ≡ 1 [MOD 4] (注意: 5 % 4 = 1)
  · right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 6: 6 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 7: 7 ≡ 7 [MOD 12]
  · right; right; right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 8: 8 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 9: 9 ≡ 0 [MOD 3]
  · right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 10: 10 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 11: 11 ≡ 3 [MOD 8] (11 % 8 = 3)
  · right; right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 12: 12 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 13: 13 ≡ 1 [MOD 4] (13 % 4 = 1)
  · right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 14: 14 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 15: 15 ≡ 0 [MOD 3]
  · right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 16: 16 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 17: 17 ≡ 1 [MOD 4] (17 % 4 = 1)
  · right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 18: 18 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 19: 19 ≡ 7 [MOD 12] (19 % 12 = 7)
  · right; right; right; right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 20: 20 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 21: 21 ≡ 0 [MOD 3]
  · right; left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 22: 22 ≡ 0 [MOD 2]
  · left; exact modeq_descend hk (by norm_num)
  -- 情况 r = 23: 23 ≡ 23 [MOD 24]
  · right; right; right; right; right; exact hk
