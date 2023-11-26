import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Dynamics.PeriodicPts

open BigOperators

-- Exercise 1
def equiv_rel (x : ℤ) (y : ℤ) : Prop := Even (x^2 + y^2)

instance equiv_inst : Equivalence (equiv_rel) where
 refl := by
  simp [equiv_rel]
 symm := by
  intros x y eq
  simp [equiv_rel, add_comm] at *
  exact eq
 trans := by
  intros x y z eq1 eq2
  simp [equiv_rel, add_comm, Even] at *
  rcases eq1 with ⟨a, ha⟩
  rcases eq2 with ⟨b, hb⟩
  rw [add_comm] at ha
  apply_fun (λ e => e - x ^ 2) at ha
  ring_nf at ha
  rw [ha] at hb
  apply_fun (λ e => e + x ^ 2 - 2 * b ) at hb
  ring_nf at hb
  rw [←hb]
  use (a + z^2 - b)
  ring_nf

lemma equiv_if_evens
  {x y : ℤ}
  : Even x → Even y → (equiv_rel x y) :=
by
  intros ex ey
  simp [equiv_rel, Even] at *
  rcases ex with ⟨a, ha⟩
  rcases ey with ⟨b, hb⟩
  rw [ha, hb]
  use (2 * a ^ 2 + 2 * b ^ 2)
  ring_nf

lemma equiv_if_odds
  {x y : ℤ}
  : Odd x → Odd y → (equiv_rel x y) :=
by
  intros ex ey
  simp [equiv_rel, Odd, Even] at *
  rcases ex with ⟨a, ha⟩
  rcases ey with ⟨b, hb⟩
  rw [ha, hb]
  ring_nf
  use (1 + 2 * a + 2 * a ^ 2 + 2 * b + 2 * b ^ 2)
  ring_nf

lemma nequiv_if_diff_parity
  {x y : ℤ}
  : Odd x → Even y → ¬(equiv_rel x y) :=
by
  intros ex ey equiv
  simp [equiv_rel, Odd, Even] at *
  rcases ex with ⟨a, ha⟩
  rcases ey with ⟨b, hb⟩
  rcases equiv with ⟨e, he⟩
  rw [ha, hb] at he
  ring_nf at he
  symm at he
  rw [mul_comm] at he
  have two_dvd := dvd_of_mul_right_eq e he
  have hring :
    1 + a * 4 + a ^ 2 * 4 + b ^ 2 * 4
    = 2 * (2 * a + 2 * a ^ 2 + 2 * b ^ 2) + 1 := by
    ring_nf
  rw [hring] at two_dvd
  exact Int.two_not_dvd_two_mul_add_one _ two_dvd

lemma nequiv_if_diff_parity'
  {x y : ℤ}
  : Even x → Odd y → ¬(equiv_rel x y) :=
by
  intros ex ey equiv
  have nequiv := nequiv_if_diff_parity ey ex
  exact nequiv (equiv_inst.symm equiv)

--  Exercise 2
def is_function
  {α β : Type}
  (f : Set (α × β)) : Prop :=
  f ⊆ ((Set.univ : Set α) ×ˢ (Set.univ : Set β)) ∧ ∀ x : α, ∃! y, (x, y) ∈ f
-- 1.)

-- 2.)
def lin_rel : Set (ℤ × ℤ) := {p : (ℤ × ℤ) | p.1 + 3 * p.2 = 4}

lemma lin_rel_is_not_function
  : ¬is_function lin_rel :=
by
  intro is_fn
  rw [is_function] at is_fn
  rw [lin_rel, Set.subset_def] at is_fn
  rcases is_fn with ⟨rel_sub, rel_uniq⟩
  simp at *
  specialize rel_uniq 3
  rw [ExistsUnique] at rel_uniq
  rcases rel_uniq with ⟨y, ⟨hl, _⟩⟩
  apply_fun (λ e => e - 3) at hl
  ring_nf at hl
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at hl
  rcases hl with (hl | hr)
  · linarith
  · linarith

-- 3.)
def sq_rel : Set (ℝ × ℝ) := {(x ^ 2, x) | x : ℝ}

lemma sq_rel_is_not_function
  : ¬is_function sq_rel :=
by
  intro is_fn
  rw [is_function] at is_fn
  rw [sq_rel, Set.subset_def] at is_fn
  rcases is_fn with ⟨rel_sub, rel_uniq⟩
  simp at *
  specialize rel_uniq 4
  rw [ExistsUnique] at rel_uniq
  rcases rel_uniq with ⟨y, ⟨_, hrel⟩⟩
  have htwo := hrel (2) (by ring_nf)
  have hmtwo := hrel (-2) (by ring_nf)
  rw [←htwo] at hmtwo
  linarith

-- Exercise 3
def pair_fn (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + p.2, 2 * p.1 + p.2)

lemma pair_fn_injective :
  Function.Injective pair_fn :=
by
  intros p q eq
  simp [pair_fn] at eq
  rcases eq with ⟨hl, hr⟩
  rw [Prod.eq_iff_fst_eq_snd_eq]
  apply_fun (λ e => e - (p.1 + p.2)) at hr
  nth_rewrite 2 [hl] at hr
  ring_nf at hr
  rw [hr] at hl
  apply_fun (λ e => e - q.1) at hl
  ring_nf at hl
  exact ⟨hr, hl⟩

lemma pair_fn_surjective :
  Function.Surjective pair_fn :=
by
  intro p
  simp [pair_fn]
-- a + b = p.1 => a = p.1 - b => a + (2 * p.1 - p.2) = p.1 => a = -p.1 + p.2
-- 2 * a + b = p.2 => 2 * p.1 - 2 * b + b = p.2 => 2 * p.1 - p.2 = b
  use (-p.1 + p.2)
  use (2 * p.1 - p.2)
  ring_nf

-- Exercise 4
-- 1.)
def fn (x : ℝ) : ℝ := x ^ 2 + 3

lemma image_fn
  : Set.image fn (Set.Icc 3 5) = Set.Icc 12 28 :=
by
  ext x
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_image, Set.mem_Icc, fn]
  constructor
  · intro hex
    rcases hex with ⟨y, ⟨⟨h3le, h5ge⟩ , hfy⟩⟩
    constructor
    · nlinarith
    · nlinarith
  · intro hlege
    rcases hlege with ⟨h12ge, h28le⟩
    use (Real.sqrt (x - 3))
    constructor
    · constructor
      · refine Real.le_sqrt_of_sq_le ?h.left.left.h
        linarith
      · refine Real.sqrt_le_iff.mpr ?h.left.right.a
        constructor
        · nlinarith
        · nlinarith
    · rw [Real.sq_sqrt]
      · nlinarith
      · nlinarith

lemma preimage_fn
  : Set.preimage fn (Set.Icc 12 19) = (Set.Icc 3 4) ∪ (Set.Icc (-4) (-3)) :=
by
  ext x
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_preimage, Set.mem_Icc, neg_le_neg_iff,
    neg_lt_neg_iff, Set.mem_union, fn]
  constructor
  · intro hlege
    rcases hlege with ⟨h12le, h19ge⟩
    have heq12 : (12 : ℝ) = (3^2) + 3 := by ring
    rw [heq12, add_le_add_iff_right, sq_le_sq, abs_of_pos (by simp), le_abs, le_neg] at h12le
    have heq19 : (19 : ℝ) = (4^2) + 3 := by ring
    have lt04 : (0 : ℝ) < 4 := by simp
    rw [heq19, add_le_add_iff_right, sq_le_sq, abs_of_pos lt04, abs_le] at h19ge
    rcases h12le with (h3le | hm3ge)
    · left
      exact ⟨h3le, h19ge.2⟩
    · right
      exact ⟨h19ge.1, hm3ge⟩
  · intro hlege
    rcases hlege with (⟨h3le, h4ge⟩ | ⟨hm4le, hm3ge⟩)
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith

-- 2.)
lemma inter_image_fun_inter_subset
  {α β : Type}
  {X Y : Set α}
  {f : α → β}
  : (Set.image f (X ∩ Y)) ⊆ (Set.image f X) ∩ (Set.image f Y) :=
by
  -- exact Set.image_inter_subset f X Y
  simp only [Set.subset_inter_iff, Set.image_subset_iff, Set.subset_def]
  simp [Set.subset_def]
  intros a b bmemX bmemY img
  constructor
  · use b
  · use b

-- 3.)
lemma inter_image_fun_inter_not_eq
  : ∃ α : Type,
    ∃ β : Type,
    ∃ f : α → β,
    ∃ X : Set α,
    ∃ Y : Set α,
      (Set.image f (X ∩ Y)) ≠ (Set.image f X) ∩ (Set.image f Y) :=
by
  use (ℤ)
  use (ℤ)
  use (λ _ => 0)
  use ({1} : Set ℤ)
  use ({2} : Set ℤ)
  simp only [Set.inter_singleton_nonempty, Set.image_singleton, Set.inter_self, ne_eq]
  intro heq
  rw [Set.inter_def] at heq
  simp at heq
  have hf {a : ℤ} : (a = 1 ∧ a = 2) = False := by
    simp_all only [eq_iff_iff, iff_false, not_and, OfNat.one_ne_ofNat, not_false_eq_true, implies_true]
  simp_rw [hf] at heq
  simp at heq
  symm at heq
  exact Set.singleton_ne_empty 0 heq

set_option trace.aesop true
-- Exercise 5
-- 1.)
noncomputable def bij_fun (x : ℝ) : {x : ℝ // x > Real.sqrt 2} where
  val := Real.exp x + Real.sqrt 2
  property := by
    simp
    exact Real.exp_pos x

lemma bijective_fn
  : Function.Bijective bij_fun :=
by
  rw [Function.Bijective, Function.Injective, Function.Surjective]
  simp only [Subtype.forall, ge_iff_le]
  constructor
  · intros a b heq
    simp_rw [bij_fun] at heq
    apply_fun(λ e => Real.log (e - Real.sqrt 2)) at heq
    simp only [add_sub_cancel, Real.log_exp] at heq
    exact heq
  · intros x hle
    simp_rw [bij_fun]
    use (Real.log (x - Real.sqrt 2))
    simp only [Subtype.mk.injEq]
    rw [Real.exp_log (by linarith)]
    ring_nf

-- 2.)
def A : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.1 ≤ p.2}

lemma two_pow_three_pow_unique_factorization'
  {m n q p : ℕ}
  (h₁ : p ≤ m) (h₂ : q ≤ n)
  : 2 ^ m * 3 ^ n = 2 ^ p * 3 ^ q → m = p ∧ n = q :=
by
  intro hfac
  have hdvd3 : 3 ^ q ∣ 2 ^ m * 3 ^ n := by
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 h₂) (2 ^ m)
  rw [←Nat.div_eq_iff_eq_mul_left (by simp) hdvd3,
      Nat.mul_div_assoc (2^m)
        (by rw [pow_dvd_pow_iff (by simp) (by simp)]; exact h₂),
      Nat.pow_div h₂ (by simp)] at hfac
  rw [mul_comm, ←one_mul (2^p)] at hfac
  have hdvd2 : 2 ^ p ∣ 3 ^ (n - q) * 2 ^ m := by
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 h₁) (3 ^ (n - q))
  rw [←Nat.div_eq_iff_eq_mul_left (by simp) hdvd2,
      Nat.mul_div_assoc (3^(n-q))
        (by rw [pow_dvd_pow_iff (by simp) (by simp)]; exact h₁),
      Nat.pow_div h₁ (by simp)] at hfac
  rw [mul_eq_one_iff' (Nat.one_le_pow' (n - q) 2) (Nat.one_le_two_pow (m - p))] at hfac
  rcases hfac with ⟨h3, h2⟩
  ring_nf at *
  apply_fun (λ e => Nat.log 2 e) at h2
  rw [Nat.log_pow (by simp)] at h2
  simp at h2
  have heq₁ : m = p := by
    linarith
  apply_fun (λ e => Nat.log 3 e) at h3
  rw [Nat.log_pow (by simp)] at h3
  simp at h3
  have heq₂ : n = q := by
    linarith
  exact ⟨heq₁, heq₂⟩

lemma two_pow_three_pow_unique_factorization
    {m n q p : ℕ} (h : 2 ^ m * 3 ^ n = 2 ^ p * 3 ^ q) : m = p ∧ n = q := by
  apply_fun Nat.factorization at h
  rw [Nat.factorization_mul, Nat.factorization_mul] at h
  · simp_rw [Nat.factorization_pow] at h
    constructor
    · replace h := FunLike.congr_fun h 2
      have : ¬ 2 ∣ 3 := by norm_num
      simp_rw [Finsupp.add_apply, Finsupp.smul_apply, Nat.prime_two.factorization_self,
        nsmul_one, Nat.factorization_eq_zero_of_not_dvd this, smul_zero, add_zero] at h
      exact h
    · replace h := FunLike.congr_fun h 3
      have : ¬ 3 ∣ 2 := Nat.not_dvd_of_pos_of_lt (by simp) (by simp)
      simp_rw [Finsupp.add_apply, Finsupp.smul_apply, Nat.prime_three.factorization_self,
        nsmul_one, Nat.factorization_eq_zero_of_not_dvd this, smul_zero, zero_add] at h
      exact h
  all_goals positivity

lemma countably_infinite
  : Set.Infinite A ∧ Set.Countable A :=
by
  constructor
  · let f (n : ℕ) : ℕ × ℕ := (n, n + 1)
    have inj_f : Function.Injective f := by
      intros a b heq
      simp only [f] at heq
      simp only [Prod.mk.inj_iff] at heq
      exact heq.1
    have hf : ∀ (x : ℕ), f x ∈ A := by
      intro x
      simp only [A, f]
      simp only [Set.mem_setOf_eq, le_add_iff_nonneg_right, zero_le]
    exact Set.infinite_of_injective_forall_mem inj_f hf
  · rw [Set.countable_iff_exists_injective]
    let f (n : A) : ℕ  := 2^n.val.1 * 3^n.val.2
    have inj_f : Function.Injective f := by
      intros a b heq
      simp only [f] at heq
      have unique_fac := two_pow_three_pow_unique_factorization heq
      rw [←Prod.eq_iff_fst_eq_snd_eq] at unique_fac
      exact SetCoe.ext unique_fac
    use f

def next (p : ℕ × ℕ) : ℕ × ℕ :=
  ite (p.1 = p.2) (0, p.2 + 1) (p.1 + 1, p.2)

lemma next_apply : next = λ p => ite (p.1 = p.2) (0, p.2 + 1) (p.1 + 1, p.2) := rfl

def enumerator (n : ℕ) : ℕ × ℕ := (next^[n]) (0, 0)

lemma enumerator_apply : enumerator = λ n => (next^[n]) (0, 0) := rfl

lemma iterate_monotone_eq_zero
  {α : Type} [Preorder α]
  {f : α → α} {x : α}
  {n : ℕ}
  (hper : Function.periodicPts f = ∅)
  : f^[n] x = x → n = 0 :=
by
  intro eq
  simp_rw [Function.periodicPts, Function.IsPeriodicPt, Function.IsFixedPt] at hper
  rw [Set.ext_iff] at hper
  simp at hper
  specialize hper x
  specialize hper n
  by_cases h : 0 < n
  · exact absurd eq (hper h)
  · simp only [not_lt, nonpos_iff_eq_zero] at h
    exact h

lemma aperiodic_next
  : Function.periodicPts next = ∅ :=
by
  simp_rw [Function.periodicPts, Function.IsPeriodicPt, Function.IsFixedPt]
  ext x
  simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro n hlt heq
  simp_rw [next_apply] at heq
  induction' n with n ih
  · simp only [Nat.zero_eq, lt_self_iff_false] at hlt
  · simp at *

  -- rw [Prod.eq_iff_fst_eq_snd_eq] at heq
  -- rcases heq with ⟨heq1, heq2⟩

  -- induction' n with n ih
  -- · simp only at *
  -- · intro heq
  --   simp at *
  --   split

lemma enumerator_bijective
  : Function.Bijective enumerator :=
by
  simp_rw [Function.Bijective, enumerator_apply]
  constructor
  · intros a b heq
    simp only at heq
    rw [Function.iterate_eq_iterate_iff_of_lt_minimalPeriod] at heq
    · exact heq
    · rw [Function.minimalPeriod]
      simp
      split
      · rw [Nat.lt_find_iff sorry a]
      · have foo := Function.iterate_cancel sorry heq
        -- simp at foo
        rw [←Function.IsFixedPt] at foo
        rw [←Function.IsPeriodicPt] at foo

    -- induction' a with a ih
    -- · simp at heq
    --   simp_rw [next] at heq
    --   induction' b with b ih'
    --   · rfl
    --   · simp at *


-- Exercise 6
def equal_card
  (α β : Type)
  : Prop :=
  ∃ f : α → β, Function.Bijective f

instance equiv_inst_equal_card : Equivalence (equal_card) where
 refl := by
  intro t
  use id
  exact Function.bijective_id
 symm := by
  simp_rw [equal_card]
  intros a b eq
  rcases eq with ⟨f, hf⟩
  rw [Function.bijective_iff_has_inverse] at hf
  rcases hf with ⟨g, ⟨hleft, hright⟩⟩
  have hleft' := Function.RightInverse.leftInverse hright
  have hright' := Function.LeftInverse.rightInverse hleft
  have bij_inv
    : ∃ f, Function.LeftInverse f g ∧ Function.RightInverse f g
      := ⟨f, ⟨hleft', hright'⟩⟩
  rw [←Function.bijective_iff_has_inverse] at bij_inv
  use g
 trans := by
  simp_rw [equal_card]
  intros a b c eq1 eq2
  rcases eq1 with ⟨f, hf⟩
  rcases eq2 with ⟨g, hg⟩
  use (g ∘ f)
  exact Function.Bijective.comp hg hf
