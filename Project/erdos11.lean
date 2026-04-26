-- Authored by: YANG Ruijia, LIU Rongqin
--

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open BigOperators


-- `p` refers an odd prime
section NeedHp
variable {p : ℕ} (hp : p.Prime ∧ p > 2)
include hp
-- `p` is a Wieferich prime if `p` is a prime and `p² ∣ 2^{p-1} - 1`
def W : Set ℕ :=
  {p | (2 : ZMod (p ^ 2)) ^ (p - 1) = 1}

-- `ord2 (n) := ord_{n}(2)`
noncomputable def ord2 (n : ℕ) : ℕ :=
  orderOf (2 : ZMod n)



lemma ord2_p_div_p_minus_1 : ord2 p ∣ p - 1 := by
  -- This lemma is a useful consequence followed from Fermat's Little Theorem
  have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
    omega
  haveI : Fact p.Prime := ⟨hp.1⟩
  have h_Fermat : (2 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h2_ne_zero
  exact orderOf_dvd_of_pow_eq_one h_Fermat

omit hp in
lemma characterization_ord2_p : ∃ k, 2 ^ (ord2 p) = p*k + 1 := by
  have h_pow_p : (2 : ZMod p) ^ (ord2 p) = (1 : ZMod p) := pow_orderOf_eq_one 2
  have h_pow_p_0 : (2 : ZMod p) ^ (ord2 p) - (1 : ZMod p) = 0 := by
    rw [h_pow_p, sub_self]
  have h_dvd : p ∣ (2 ^ (ord2 p) - 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    simp [h_pow_p_0]
  obtain ⟨k, hk⟩ := h_dvd
  use k
  apply Nat.eq_add_of_sub_eq
  · exact Nat.one_le_pow (ord2 p) 2 (by norm_num)
  · exact hk

lemma ord2_p2_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := by
  -- An division property which is useful in the final argument
  have h_div : ord2 (p) ∣ ord2 (p^2) := by
    let f : ZMod (p^2) →+* ZMod p := ZMod.castHom (show p ∣ p^2 by norm_num) (ZMod p)
    have hf : f 2  = 2 := map_natCast f 2
    have h_pow_p2 : (2 : ZMod (p^2)) ^ ord2 (p^2) = (1 : ZMod (p^2)) :=
      pow_orderOf_eq_one 2
    have h_apply_f : f (2 ^ ord2 (p^2)) = f 1 := congr_arg f h_pow_p2
    rw [map_pow, map_one] at h_apply_f
    have h_pow_p : (2 : ZMod p) ^ ord2 (p^2) = (1 : ZMod p) := by
      rw [hf] at h_apply_f; assumption
    exact orderOf_dvd_of_pow_eq_one h_pow_p
  -- We will use this property to conclude `h_div'`
  have h_pow : (2 : ZMod (p^2)) ^ (p * ord2 p) = (1 : ZMod (p^2)) := by
    obtain ⟨k, hk⟩ := characterization_ord2_p
    rw [pow_mul']; rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by rfl]
    rw [← Nat.cast_pow]; rw [hk]; push_cast
    rw [add_pow]; rw [Finset.sum_range_succ'] -- expand `(↑p * ↑k + 1) ^ p` using Binomial Theorem
    simp only [Nat.choose_zero_right, pow_zero, one_pow, mul_one, Nat.cast_one]
    simp only [add_eq_right]
    apply Finset.sum_eq_zero
    intro i _
    cases i with
    | zero =>
      simp only [Nat.zero_add, Nat.choose_one_right, pow_one]
      calc ↑p * ↑k * ↑p
        _ = (p : ZMod (p^2)) ^ 2 * ↑k := by ring
        _ = ↑(p^2) * ↑k := by rw [← Nat.cast_pow]
        _ = 0 * k := by rw [ZMod.natCast_self]
        _ = 0 := by ring
    | succ j =>
      have h_zero : (p * k : ZMod (p^2)) ^ 2 = 0 := by
        calc (↑p * ↑k) ^ 2
            _ = (p : ZMod (p^2)) ^ 2 * (k : ZMod (p^2)) ^ 2 := mul_pow _ _ _
            _ = ↑(p^2) * ↑k ^ 2 := by rw [← Nat.cast_pow]
            _ = 0 * ↑k ^ 2 := by rw [ZMod.natCast_self]
            _ = 0 := by ring
      calc (↑p * ↑k : ZMod (p^2)) ^ (j + 1 + 1) * ↑(p.choose (j + 1 + 1))
          _ = ↑(p.choose (j + 1 + 1)) * ((↑p * ↑k) ^ 2 * (↑p * ↑k) ^ j) := by ring
          _ = ↑(p.choose (j + 1 + 1)) * (0 * (↑p * ↑k) ^ j) := by rw [h_zero]
          _ = 0 := by ring
  -- Now, we have enough info to conclude that ther are only two possibilities for `ord2 (p^2)`
  have h_div_p_1 : ord2 p ∣ p - 1 := ord2_p_div_p_minus_1 hp
  have h_div' : ord2 (p^2) ∣ (p * ord2 p) := orderOf_dvd_of_pow_eq_one h_pow
  obtain ⟨k, hk⟩ := h_div
  rw [hk] at h_div'
  rw [mul_comm (ord2 p) k] at h_div'
  have h_ord_pos : 0 < ord2 p := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero, zero_dvd_iff] at h_div_p_1
    omega
  have h_k_div_p : k ∣ p := Nat.dvd_of_mul_dvd_mul_right h_ord_pos h_div'
  rcases (Nat.dvd_prime hp.1).mp h_k_div_p with rfl | rfl
  · left; rw [hk, mul_comm, one_mul]
  · right; rw [hk, mul_comm]



lemma nonW_primes_ord2_relation (hp_nonW : p ∉ W) : ord2 (p^2) = p * ord2 (p) := by
  have h_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := ord2_p2_branch hp
  have h_div_p_1 : ord2 p ∣ p - 1 := ord2_p_div_p_minus_1 hp
  -- The final discussion for two branches
  rcases h_branch with h_eq | h_eq
  · exfalso
    apply hp_nonW
    change (2 : ZMod (p^2)) ^ (p - 1) = 1
    rw [← h_eq] at h_div_p_1
    exact orderOf_dvd_iff_pow_eq_one.mp h_div_p_1
  · exact h_eq

lemma W_primes_ord2_relation (hp_W : p ∈ W) : ord2 (p^2) = ord2 (p) := by
  have h_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := ord2_p2_branch hp
  rcases h_branch with h_eq | h_eq
  · exact h_eq
  · exfalso
    have h_pW : (2 : ZMod (p^2)) ^ (p - 1) = 1 := hp_W
    -- By definition, we have `ord2 (p^2) ∣ p - 1`
    have h_div : ord2 (p^2) ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr h_pW
    rw [h_eq] at h_div
    -- This implies p * ord2 p ∣ p - 1, hence p ∣ p - 1
    rw [mul_comm] at h_div
    have h_p_dvd : p ∣ p - 1 := dvd_of_mul_left_dvd h_div
    -- But p cannot divide p - 1, contradiction
    have h_p_gt_1 : 1 < p := by omega
    have h_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt h_p_gt_1
    have h_le : p ≤ p - 1 := Nat.le_of_dvd h_sub_pos h_p_dvd
    omega
end NeedHp


def P (r : ℕ) : Set ℕ :=
  {p | (p ∉ W) ∧ (ord2 p = r) ∧ p.Prime ∧ p > 2}
/- We first show that such set is finite so that we may
  write it as a ascending list p₁ < ⋯ < pₘ.
  that is pr is finite set
-/

/-
  (2 Zmod p) ^ r = 1     2 ^ r mod p = 1     2^r ≥ 1     2^r - 1 mod p = 0
  finally p ∣ 2 ^r -1
-/

lemma dvd_of_ord2_eq (p r : ℕ) (h : ord2 p = r) : p ∣ 2^r - 1 := by
  have h1 : (2 : ZMod p) ^ r = 1 := by
    have h2 : orderOf (2 : ZMod p) = r := h
    rw [← h2]
    exact pow_orderOf_eq_one (2 : ZMod p)
  have h3 : ((2^r : ℕ) : ZMod p ) = 1 := by
    simpa
  have h4 : (2^r : ℕ) ≥ 1 := by
    apply Nat.one_le_pow
    exact Nat.zero_lt_two
  have h5 : ((2^r - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub h4]
    rw [h3]
    simp
  have h6 : p ∣ (2^r - 1 :ℕ) := by
    rw[← ZMod.natCast_eq_zero_iff]
    exact h5
  exact h6

lemma P_subset (r : ℕ) : P r ⊆ {p : ℕ | p ∣ 2^r - 1} := by
  intro p hp
  have h7 : ord2 p = r := hp.2.1
  exact dvd_of_ord2_eq p r  h7

lemma P_r_is_finite (r : ℕ) (hr : r ≥ 1) : (P r).Finite := by
  have h1 : P r ⊆ {p : ℕ | p ∣ 2^r - 1} := by apply P_subset r
  have h2 : (2^r - 1 : ℕ) > 0 := by
    have h3 : 2^r ≥ 2 := by
      have h4 : 2^r ≥ 2^1 := by exact Nat.le_pow hr
      omega
    omega
  have h3 : {p : ℕ | p ∣ 2^r - 1} = (Nat.divisors (2^r - 1) : Set ℕ) := by
    ext p  -- A = B ↔ ∀ p, p∈A ↔ p∈B
    simp
    omega
  rw [h3] at h1
  apply Set.Finite.subset -- two conditions :    finite and subset
  · exact Finset.finite_toSet (Nat.divisors (2^r - 1))
  · exact h1

noncomputable def P_list (r : ℕ) (h_Pfin : (P r).Finite) : List ℕ :=
  h_Pfin.toFinset.sort (· ≤ ·)

/-
  For each `pⱼ` in P_r, we have `ord2 (pⱼ^2) = pr` and `ord2 pⱼ = r`.
  Then `2^r ≡ 1 mod pⱼ`, and `2^{pⱼ-1} ≡ 1 mod pⱼ` by Fermat's little thm.
  Thus, we have `r ∣ pⱼ-1` i.e. `pⱼ ≡ 1 mod r`.
  Hence `pⱼ ≥ jr+1`.
-/
lemma lowerBound_of_p_in_P_r (r : ℕ) (hr : r ≥ 1) (h_Pfin : (P r).Finite) :
  ∀ (j : ℕ) (hj : j < (P_list r h_Pfin).length),
    (P_list r h_Pfin).get ⟨j, hj⟩ ≥ (j+1)*r + 1  -- `j` starts from 0
    := by
  sorry

/-
  Since `pⱼ ∣ 2^r - 1` for each j and `pⱼ` are distinct primes, they
  are distinct prime factors of `2^r - 1`.
  Using FTA, we see `∏ pⱼ ≤ 2^r - 1 < 2^r`.
-/
lemma upperBound_of_prod_in_P_r (r : ℕ) (hr : r ≥ 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).prod < 2^r := by
  sorry

/-
  Combining the above two bounds, we get `∏ (jr+1) < 2^r`.
  Ignoring the 1, it follows that `rᵐm! < 2^r`.
  Taking logrithm, we have `m < {r · log 2}/{log r}` for `r > 1`.
  And for `r = 1`, the set `P r` is empty hence `m = 0`.
-/


lemma upperBound_of_m_by_r (r : ℕ) (hr : r > 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).length < (r * Real.log 2) / (Real.log r) := by
  -- 1 define m and L more easy to write
  let m := (P_list r h_Pfin).length
  let L := P_list r h_Pfin
  -- we need a map to use list product and something else
  let K : List ℕ := (List.range m).map (fun j ↦ (j+1)*r)
  have h_len_val : K.length = m := by
    simp [K, m]
-- 1 L.length = K.length = m
  have h_len : L.length = K.length := by
    simp [K, m]
    rfl
-- 2. ∀ j < m, L[j] ≥ K[j]
  have h_ge_one : r ≥ 1 := by linarith
  have h_elem : ∀ j (hj : j < m),
      L.get ⟨j, by simpa [m] using hj⟩ ≥ K.get ⟨j, by (rw [h_len_val] ; exact hj)⟩ := by
    intro j hj
    -- K.get to (j+1)*r
    have h_K_get : K.get ⟨j, by (rw [h_len_val] ; exact hj)⟩ = (j + 1) * r := by
      simp [K, List.getElem_map, List.getElem_range]
    have h_p_lower : L.get ⟨j, by simpa [m] using hj⟩ ≥ (j + 1) * r + 1 :=
      lowerBound_of_p_in_P_r r h_ge_one h_Pfin j hj
    linarith
  -- 3. L.prod ≥ K.prod
  have h_forall : List.Forall₂ (fun (x1 x2 : ℕ) => x1 ≤ x2) K L := by
    exact List.forall₂_of_length_eq_of_get h_len_val fun i h₁ ↦ h_elem i
  have h_prod1 : K.prod ≤ L.prod := by
    exact List.Forall₂.prod_le_prod' h_forall
  have h_prod1' : L.prod ≥ K.prod := h_prod1
  -- 4. K.prod = m.factorial * r ^ m
  have h_prod2 : K.prod = m.factorial * r ^ m := by
    -- List.prod to Finset.prod
    have h1 : K.prod = ∏ j ∈ Finset.range m, ((j + 1) * r) := by
      exact
        Eq.symm
          (Nat.add_zero
            (List.foldr (fun x1 x2 ↦ x1 * x2) 1 (List.map (fun j ↦ (j + 1) * r) (List.range m))))
    rw [h1]
    -- ∏ (j+1)*r = (∏ j+1) * (∏ r)
    have h2 : ∏ j ∈ Finset.range m, ((j + 1) * r) =
    (∏ j ∈ Finset.range m, (j + 1)) * (∏ j ∈ Finset.range m, r) := by
      rw [Finset.prod_mul_distrib]
    rw [h2]
    -- ∏ j ∈ range m, (j+1) = m.factorial
    have h3 : (∏ j ∈ Finset.range m, (j + 1)) = m.factorial := by
      induction m with
      | zero => exact Finset.prod_range_add_one_eq_factorial 0
      | succ m ih =>
        exact Finset.prod_range_add_one_eq_factorial (m + 1)
    rw [h3]
    -- ∏ j ∈ range m, r = r ^ m
    have h4 : (∏ j ∈ Finset.range m, r) = r ^ m := by
      simp [Finset.prod_const]
    rw [h4]
  -- 5. L.prod ≥ m.factorial * r ^ m
  have h_prod_lower : L.prod ≥ m.factorial * r ^ m := by
    rw [h_prod2] at h_prod1
    exact h_prod1
  -- 6. m! * r^m < 2^r
  have h_ge_one : r ≥ 1 := by linarith
  have h_mixed : m.factorial * r ^ m < 2 ^ r := by
    have h_upper := upperBound_of_prod_in_P_r r h_ge_one h_Pfin
    exact Nat.lt_of_le_of_lt h_prod_lower h_upper
  -- 7. to real number
  have h_real : (↑(m.factorial) * ↑r ^ m : ℝ) < (↑2 ^ r : ℝ) := by
    exact_mod_cast h_mixed
  -- 8. log
  have h_pos1 : (0 : ℝ) < (↑(m.factorial) * (↑r : ℝ) ^ m) := by positivity
  have h_pos2 : (0 : ℝ) < (↑2 : ℝ) ^ r := by positivity
  -- use Real.log_lt_log
  have h_log : Real.log ((↑(m.factorial) * (↑r : ℝ) ^ m)) < Real.log ((↑2 : ℝ) ^ r) := by
    apply Real.log_lt_log
    · exact h_pos1
    · exact h_real
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h_log
  -- 9. log(m!) ≥ 0
  have h_log_fact : 0 ≤ Real.log (↑m.factorial : ℝ) := by
    exact Real.log_natCast_nonneg m.factorial
  have h_core : (↑m : ℝ) * Real.log (↑r : ℝ) < (↑r : ℝ) * Real.log 2 := by
    linarith
  -- 11. divide log r
  have h_log_r : 0 < Real.log (↑r : ℝ) := Real.log_pos (by exact_mod_cast hr)
  -- lt_div_iff₀
  exact (lt_div_iff₀ h_log_r).mpr h_core

/-
  The contribution to the series can be divided into each `P r`, that is
    `∑_{p ∉ W} {1 / ord2 (p^2)} = ∑_{r ≥ 2} { ∑_{p ∈ P r} {1 / ord2 (p^2)} }`.
-/

lemma divideContribution_into_r :
    ∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), (1 : ℝ) / (ord2 (p ^ 2)) =
    ∑' (r : ℕ), ∑' (p : {p // p ∈ P r}), (1 : ℝ) / (ord2 (p ^ 2))
    := by
  let f p := (1 : ℝ) / ord2 (p^2) -- for convinient
  -- left set == right set
  have h1 : {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} = ⋃ (r : ℕ), P r := by
    ext p
    simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_iUnion]  -- p ∧ p > 2 ∧ p ∉ W  iff  ∃ r, p ∈ P r
    constructor
    · intro h
      have h_p_notin_W : p ∉ W := h.right.right
      have h_p_prime : p.Prime := h.1
      have h_p_gt_2 : p > 2 := h.2.1
      let r : ℕ := ord2 p
      have h_ord_eq : ord2 p = r := by rfl
      have h_P_iff : ∀ (q : ℕ), q ∈ P r ↔ (q ∉ W) ∧ (ord2 q = r) ∧ q.Prime ∧ q > 2 := by
        intro q
        simp [P]
      have h : p ∈ P r ↔ (p ∉ W) ∧ (ord2 p = r) ∧ p.Prime ∧ p > 2 := h_P_iff p
      have h_in_Pr : p ∈ P r := ⟨h_p_notin_W, h_ord_eq, h_p_prime, h_p_gt_2⟩
      have h_main : ∃ (r : ℕ), p ∈ P r := by exact Exists.intro r h_in_Pr
      exact h_main

    · intro h
      cases h with
      | intro r hr
      have h_p_notin_W : p ∉ W := hr.left
      have h_p_prime : p.Prime := hr.2.2.1
      have h_p_gt_2 : p > 2 := hr.2.2.2
      have h_main : p.Prime ∧ p > 2 ∧ p ∉ W := ⟨h_p_prime, h_p_gt_2, h_p_notin_W⟩
      exact h_main
-- pairwise disjoint P r1 and P r2
  have h_disj :  Pairwise (fun (r1 r2 : ℕ) ↦ Disjoint (P r1) (P r2)) := by
    intro r1 r2 hne
    rw [Set.disjoint_left]
    intro p hp1 hp2
    -- ord2 p = r1 and ord2 p = r2
    have h1 : ∀ (q : ℕ), q ∈ P r1 ↔ (q ∉ W) ∧ (ord2 q = r1) ∧ q.Prime ∧ q > 2 := by
      intro q
      simp [P]
    have h2 : ∀ (q : ℕ), q ∈ P r2 ↔ (q ∉ W) ∧ (ord2 q = r2) ∧ q.Prime ∧ q > 2 := by
      intro q
      simp [P]
    have eq1 : ord2 p = r1 := (h1 p).mp hp1 |>.2.1
    have eq2 : ord2 p = r2 := (h2 p).mp hp2 |>.2.1
    rw [eq1] at eq2
    exact hne eq2
-- we use indicator to put every sum in N to avoid type dismatch
  have h_left : (∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), f p) =
  ∑' (p : ℕ), Set.indicator {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f p := by
    have h_tsum_subtype : ∀ (s : Set ℕ) (g : ℕ → ℝ), (∑' (x : {x // x ∈ s}), g (x : ℕ)) =
    ∑' (x : ℕ), Set.indicator s g x := by
      intro s g
      simpa [Set.indicator] using tsum_subtype s g
    exact h_tsum_subtype {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f
  have h_right : ∀ (r : ℕ), (∑' (p : {p // p ∈ P r}), f (p : ℕ)) =
  ∑' (p : ℕ), Set.indicator (P r) f p := by
    intro r
    have h_tsum_subtype : ∀ (s : Set ℕ) (g : ℕ → ℝ), (∑' (x : {x // x ∈ s}), g (x : ℕ)) =
    ∑' (x : ℕ), Set.indicator s g x := by
      intro s g
      simpa [Set.indicator] using tsum_subtype s g
    exact h_tsum_subtype (P r) f
  -- now by h1 we have proven that two sets are equal hence there sum are equal
  have h_main1 : (∑' (p : ℕ), Set.indicator {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f p) =
  ∑' (p : ℕ), Set.indicator (⋃ (r : ℕ), P r) f p := by
    rw [h1]
  have h_main3 : (∑' (r : ℕ), ∑' (p : ℕ), Set.indicator (P r) f p) =
    ∑' (r : ℕ), ∑' (p : {p // p ∈ P r}), f p := by
    apply tsum_congr
    intro r
    exact (h_right r).symm
  have h_fun_eq : Set.indicator (⋃ (r : ℕ), P r) f = ∑' (r : ℕ), Set.indicator (P r) f := by
    have h : Set.indicator (⋃ (r : ℕ), P r) f = ∑' (r : ℕ), Set.indicator (P r) f := by
      apply?
    exact h
  have h_step1 : (∑' (p : ℕ), (Set.indicator (⋃ (r : ℕ), P r) f) p) =
    ∑' (p : ℕ), (∑' (r : ℕ), Set.indicator (P r) f p) := by
    congr
    apply?
  have h_main2 : (∑' (p : ℕ), (∑' (r : ℕ), Set.indicator (P r) f p)) =
    ∑' (r : ℕ), ∑' (p : ℕ), Set.indicator (P r) f p := by
    have h_nonneg : ∀ (p r : ℕ), 0 ≤ Set.indicator (P r) f p := by
      intro p r
      simp [Set.indicator]
      <;> split_ifs <;> positivity
    apply?
  rw [h_left, h_main1, h_step1, h_main2, h_main3]



-- The n-th harmonic number
def H (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (1 / (i + 1) : ℚ)

/-
  For each contribution, we have
    `∑_{p ∈ P r} {1 / ord2 (p^2)} = ∑_{p ∈ P r} {1 / pr} ≤ ∑ {1 / (jr+1)r}`
  using the __lowerBound_of_p_in_P_r__.
  Ignoring the 1, we get `∑_{p ∈ P r} {1 / ord2 (p^2)} ≤ 1/r² H m`.
  Then, apply __upperBound_of_m_by_r__, we get
    `∑_{p ∈ P r} {1 / ord2 (p^2)} ≤ 1/r² H ⌊{r · log 2}/{log r}⌋`.
-/
lemma upperBound_of_each_contribution (r : ℕ) (hr : r > 1) (h_Pfin : (P r).Finite) :
    ∑ p ∈ h_Pfin.toFinset, (1 : ℝ) / (ord2 (p^2))
    ≤ (1 : ℝ)/(r^2) * H (Nat.floor ((r * Real.log 2)/(Real.log r))) := by
  let s := h_Pfin.toFinset
  let L := P_list r h_Pfin
  have hL_toFinset : L.toFinset = s := by
    simp [L, P_list, s]
  have hL_nodup : L.Nodup := by apply?
  -- H is strictly increasing
  have h_H_mono : ∀ (m n : ℕ), m ≤ n → (H m : ℝ) ≤ (H n : ℝ) := by
    intro m n hmn
    have h₁ : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.mpr hmn
    have h₂ : ∀ i ∈ Finset.range n, (i ∉ Finset.range m) → 0 ≤ (1 : ℝ) / ((i : ℝ) + 1) := by
      intro i _ _
      have h_pos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      exact one_div_nonneg.mpr (by linarith)
    simpa [H] using Finset.sum_le_sum_of_subset_of_nonneg h₁ h₂
  -- 1/ord2(p^2) = 1/(p*r)
  have h_main₁ : ∀ p ∈ s, (1 : ℝ) / (ord2 (p^2)) = (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
    intro p hp
    have h_p_in_Pr : p ∈ P r := by exact (Set.Finite.mem_toFinset h_Pfin).mp hp
    have h_notW : p ∉ W := h_p_in_Pr.1
    have h_ord_eq : ord2 p = r := h_p_in_Pr.2.1
    have h_prime : p.Prime := h_p_in_Pr.2.2.1
    have h_gt2 : p > 2 := h_p_in_Pr.2.2.2
    have h_ord2_p2_eq : ord2 (p^2) = p * ord2 p := nonW_primes_ord2_relation ⟨h_prime, h_gt2⟩ h_notW
    have h_ord2_p2_eq' : ord2 (p^2) = p * r := by
      rw [h_ord2_p2_eq, h_ord_eq]
    have h_cast_mul : ((p * r : ℕ) : ℝ) = (p : ℝ) * (r : ℝ) := by exact Nat.cast_mul p r
    have h_final : (1 : ℝ) / (ord2 (p^2) : ℝ) = (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
      have h₁ : (ord2 (p^2) : ℝ) = ((p * r : ℕ) : ℝ) := by
        exact_mod_cast h_ord2_p2_eq'
      rw [h₁, h_cast_mul]
    exact h_final
  -- simplify
  have h_main₂ : ∑ p ∈ s, (1 : ℝ) / (ord2 (p^2)) = ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_main₁ p hp
  -- the sum of the set is the sum of the list
  have h_main₃₁ : ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) * (r : ℝ)) = (L.map (fun p ↦ (1 : ℝ) / ((p : ℝ) * (r : ℝ)))).sum := by
    apply?




/-
  Now, using __divideContribution_into_r__, we have that
    `∑_{p ∉ W} {1 / ord2 (p^2)} ≤ ∑ {1/r² H ⌊{r · log 2}/{log r}⌋}`.
-/
lemma upperBound_integrate_all_contributions :
    ∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), (1 : ℝ) / (ord2 (p ^ 2))
    ≤ ∑' (r : ℕ), (1 : ℝ)/(r^2) * H (Nat.floor ((r * Real.log 2)/(Real.log r))) := by
  sorry


-- theorem ReciprocalOrderSeries_of_nonW_primes_converges :
--     Summable ( fun (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}) => (1 : ℝ) / (ord2 (p^2)) ) := by
--   sorry
