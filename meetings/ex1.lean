import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Std.Data.Int.Lemmas
import Mathlib.Data.Real.Sqrt

-- Exercise 1
-- 1.)
-- Infinite

-- 2.)
lemma sqrt17 : {x : ℝ | x^2 = 17} = {Real.sqrt 17, -Real.sqrt 17} :=
by
  ext x
  simp
  constructor
  · intro hsq
    apply_fun (λ eq => Real.sqrt eq) at hsq
    rw [Real.sqrt_sq_eq_abs] at hsq
    exact eq_or_eq_neg_of_abs_eq hsq
  · intro hor
    rcases hor with (hpos | hneg)
    · rw [hpos]
      exact Real.sq_sqrt (by norm_num)
    · rw [hneg, neg_sq]
      exact Real.sq_sqrt (by norm_num)

-- 3.)
set_option trace.aesop true
lemma lt24
  : {x : ℤ | |3 * x| < 24 } = {-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} :=
by
  ext x
  constructor
  · intro hlt
    simp only [Set.mem_setOf_eq] at hlt
    rw [abs_lt] at hlt
    rcases hlt with ⟨hlt, hlt'⟩
    -- refine Set.mem_toFinset.mp ?h.mp.intro.a
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, or_self]
    by_contra hne
    repeat rw [not_or] at hne
    rcases hne with ⟨m7, m6, m5, m4, m3, m2, m1, z, p1, p2, p3, p4, p5, p6, p7⟩
    have threedvd : ((3 : ℤ) ∣ 24) := by
      have : (24 : ℤ) = 3 * 8 := by ring_nf
      rw [this]
      simp only [dvd_mul_right]
    rw [mul_comm, ←Int.lt_ediv_iff_mul_lt 3 (by simp) threedvd] at hlt'
    have lt8 : x < 8 := by
      exact hlt'
    have gt8 : -8 < x := by
      sorry
    sorry
    -- apply?
  · intro hor
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff, or_self] at hor
    simp only [Set.mem_setOf_eq]
    rcases hor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    repeat { ring_nf
             simp only [abs_neg, abs_lt]
             constructor
             · norm_num
             · norm_num
           }

-- 4.)
-- 5.)

-- Exercise 3
-- 1.)
lemma circle_area_subset_square_area
  : {p : (ℝ × ℝ) | p.1^2 + p.2^2 < 1} ⊆ (Set.Icc (-1) 1) ×ˢ (Set.Icc (-1) 1) :=
by
  intros p hmem
  simp at *
  have h : p.1 ^ 2 ≤ 1 ∧ p.2 ^ 2 ≤ 1 := by
    have p1nonneg := sq_nonneg (p.1)
    have p2nonneg := sq_nonneg (p.2)
    constructor
    · linarith
    · linarith
  simp only [sq_le_one_iff_abs_le_one, abs_le] at h
  exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

-- 2.)
lemma square_area_not_subset_circle_area
  : ¬(Set.Icc (-1) 1) ×ˢ (Set.Icc (-1) 1) ⊆ {p : (ℝ × ℝ) | p.1^2 + p.2^2 < 1} :=
by
  intro sub
  simp at *
  have hel : ((-1, -1) : ℝ × ℝ) ∈ Set.Icc (-1, -1) (1, 1) := by
    simp
  specialize sub hel
  simp at sub
  linarith

-- 3.)
def heterogeneous_subset
  {α β : Type}
  (s : Set α)
  (t : Set β)
  [Coe α β]
  : Prop :=
  ∀ x ∈ s, ↑x ∈ t

instance : Coe ℕ ℝ where
  coe := Real.natCast.natCast

lemma nat_subset_real
  : heterogeneous_subset (Set.univ : Set ℕ) (Set.univ : Set ℝ) :=
by
  intro n _
  simp only [Set.mem_univ]

-- Exercise 4
-- i)
def even_up_to (i : ℕ) : Set ℕ := {m : ℕ | m ≤ 2 * i ∧ Even m}

-- 1.)
lemma union_even_up_to
  : ⋃ j ∈ (Set.univ : Set ℕ), even_up_to j = {m : ℕ | Even m} := by
  simp
  simp_rw [even_up_to, Set.ext_iff]
  intro x
  constructor
  · simp
  · simp
    intro heven
    constructor
    · use x
      linarith
    · exact heven

-- 2.)
lemma inter_even_up_to
  : ⋂ j ∈ (Set.univ : Set ℕ), even_up_to j = Set.singleton 0 := by
  simp
  simp_rw [even_up_to, Set.ext_iff]
  intro x
  constructor
  · simp
    intro imp
    specialize imp 0
    simp at imp
    rcases imp with ⟨hle, _⟩
    exact Set.mem_singleton_of_eq hle
  · simp
    intros mem i
    have mem' := Set.eq_of_mem_singleton mem
    constructor
    · rw [mem']
      linarith
    · rw [mem']
      simp

-- ii)
-- def rectangle (α : ℝ) : Set (ℝ × ℝ) := Set.Icc (α, 1) (0, α)
def rectangle (α : ℝ) : Set (ℝ × ℝ) := Set.Icc α 1 ×ˢ Set.Icc 0 α


-- 1.)
-- Is this possible?
-- lemma union_rectangles
--   : ⋃ α ∈ (Set.Icc 0 1 : Set ℝ), rectangle α = triangle_here_via_topology? :=
-- by
--   sorry

-- 2.)
lemma inter_rectangles
  : ⋂ α ∈ (Set.Icc 0 1 : Set ℝ), rectangle α = Set.singleton (1, 0) :=
by
  simp only [ge_iff_le, zero_le_one, not_true, gt_iff_lt, Set.mem_Icc]
  simp_rw [rectangle, Set.ext_iff]
  intro x
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.Icc_prod_Icc, Prod.mk_le_mk, not_and, Prod.mk_lt_mk, Set.mem_iInter, Set.mem_Icc, and_imp]
  constructor
  · intro imp
    have h1 := imp 0
    have h2 := imp 1
    simp [Prod.le_def] at *
    have hx1 : x.1 = 1 := by
      linarith
    have hx2 : x.2 = 0 := by
      linarith
    exact Set.mem_singleton_of_eq (Prod.ext hx1 hx2)
  · intros mem i hle0i hlei1
    have mem' := Set.eq_of_mem_singleton mem
    constructor
    · rw [mem']
      simp [Prod.le_def]
      exact hlei1
    · rw [mem']
      simp
      exact hle0i

-- Exercise 5
