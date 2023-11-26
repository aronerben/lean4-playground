import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- Exercise 1
-- 2.)
lemma idx_set_union
  {α β : Type}
  {I J : Set α}
  {A : α → Set β}
  (hsub : J ⊆ I)
  : (⋃ j ∈ J, A j) ⊆ (⋃ i ∈ I, A i) :=
by
  intros x hx
  simp only [Set.mem_iUnion, exists_prop]
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨j, ⟨hj, hxj⟩⟩
  use j
  constructor
  exact hsub hj
  exact hxj

lemma idx_set_not_inter
  : ∃ α : Type,
    ∃ β : Type,
    ∃ J : Set α,
    ∃ I : Set α,
    ∃ A : α → Set β,
      (J ⊆ I) ∧ (¬((⋂ j ∈ J, A j) ⊆ (⋂ i ∈ I, A i))) :=
by
  use ℕ
  use ℕ
  use {1}
  use {1, 2}
  let A := λ n : ℕ => ({0, n} : Set ℕ)
  use A
  simp only [Set.mem_singleton_iff, OfNat.one_ne_ofNat, Set.singleton_subset_iff,
    Set.mem_insert_iff, or_false, Set.iInter_iInter_eq_left, Set.iInter_iInter_eq_or_left,
    Set.subset_inter_iff, not_false_eq_true, Set.insert_subset_insert_iff, Set.subset_singleton_iff,
    imp_self, forall_const, forall_eq, and_false, and_self]

-- 3.)
lemma idx_set_inter_rev
  {α β : Type}
  {I J : Set α}
  {A : α → Set β}
  (hsub : J ⊆ I)
  : (⋂ i ∈ I, A i) ⊆ (⋂ j ∈ J, A j) :=
by
  simp only [Set.subset_iInter_iff]
  intros x hx b hb
  simp at hb
  specialize hb x
  exact hb (hsub hx)

-- Exercise 2
-- 1.)
lemma sq_diophantine
  (x y : ℝ)
  : (x ^ 2 + 5 * y = y ^ 2 + 5 * x) → ((x = y) ∨ (x + y = 5)) :=
by
  intro h
  apply_fun (λ eq => eq - 5 * y - y ^ 2) at h
  ring_nf at h
  rw [sq_sub_sq, ←mul_sub_right_distrib, mul_comm] at h
  rw [mul_eq_mul_left_iff, sub_eq_zero, or_comm] at h
  exact h
