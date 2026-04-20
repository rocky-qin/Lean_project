import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

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
