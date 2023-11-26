import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

-- Exercise 1
lemma sum_squared_eq_sum_cubes
  {n : ℕ}
  : (∑ x in Finset.range (n + 1), x) ^ 2
    = (∑ x in Finset.range (n + 1), x ^ 3) :=
by
  induction' n with n ih
  · ring_nf
    simp only [Nat.zero_eq, add_zero, Finset.range_one, Finset.sum_singleton, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow']
  · rw [Finset.range_succ,
        Finset.sum_insert Finset.not_mem_range_self,
        Finset.sum_insert Finset.not_mem_range_self]
    rw [add_sq]
    let S := ∑ x in Finset.range (n + 1), x
    have hS : S = ∑ x in Finset.range (n + 1), x := rfl
    nth_rewrite 2 [←hS]

    have bigger (n : ℕ) : 1 ≤ n + 1 := by
      simp only [le_add_iff_nonneg_left, zero_le]

    rw [Finset.sum_range_id]
    zify [bigger]
    push_cast
    have hring (n : ℤ):
      (n + 1) ^ 2 + 2 * (n + 1) * ((n + 1) * (n + 1 - 1) / 2)
      = (n + 1) ^ 3 := by

      have htwodvd : 2 ∣ ((n + 1) * (n + 1 - 1)) := by
        rw [add_sub_cancel, mul_comm]
        exact even_iff_two_dvd.1 (Int.even_mul_succ_self n)

      qify [htwodvd, bigger]
      push_cast
      ring_nf
    zify at ih
    rw [hring n, ih]

-- Exercise 2
lemma six_dvd_n_cubed_minus_n
  {n : ℕ}
  : 6 ∣ (n ^ 3 - n) :=
by
  have gt_pow3 (n : ℕ) : n ≤ n ^ 3 := by
    apply Nat.le_self_pow
    simp
  zify [gt_pow3 n]
  push_cast
  -- Alternatively, Nat.twoStepInduction
  induction' n using Nat.caseStrongInductionOn with n ih
  · exact dvd_zero 6
  · by_cases hp : n ≤ 3
    -- TODO find more efficient way
    · rw [Nat.succ_eq_add_one]
      simp at hp
      rcases hp with _ | hp
      · ring_nf
        have : (60 : ℤ) = 6 * 10 := by ring
        simp_rw [this, dvd_mul_right]
      · rcases hp with _ | hp
        · ring_nf
          have : (24 : ℤ) = 6 * 4 := by ring
          simp_rw [this, dvd_mul_right]
        · rcases hp with _ | hp
          · ring_nf
            exact Int.dvd_refl 6
          · simp at hp
            rw [hp]
            exact dvd_zero 6
    let k : ℕ := n - 3
    have hk : Nat.succ n = k + 4 := by
      zify [le_of_not_le hp]
      ring_nf
    rw [hk]
    push_cast (config := { zeta := false })
    have hring (k : ℤ) :
      (k + 4) ^ 3 - (k + 4)
      = (k ^ 3 - k) + 6 * (2 * k ^ 2 + 8 * k + 10) := by
      ring_nf
    rw [hring k]
    rcases ih k (by simp) with ⟨m, hm⟩
    rw [hm, ←mul_add]
    simp only [ge_iff_le, dvd_mul_right]

-- Exercise 3
lemma binomial_theorem
  {x y n : ℕ}
  : (x + y) ^ n
    = ∑ k in Finset.range (n + 1),
        Nat.choose n k * x^(n - k) * y^k :=
by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ,
        Nat.succ_eq_add_one,
        Nat.choose_self,
        Nat.sub_self,
        pow_zero,
        mul_one,
        one_mul,
        Finset.sum_range_succ',
        Nat.choose_zero_right,
        one_mul,
        Nat.sub_zero,
        pow_zero,
        mul_one]
    simp_rw [Nat.choose_succ_succ']


    -- qify
    -- ring_nf
