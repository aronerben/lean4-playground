import Mathlib.Tactic
import Mathlib.Tactic.Basic

-- Exercise 1
-- a)
lemma prod_bin_real_uncountable
  : ¬(Set.Countable (({0, 1} : Set ℕ) ×ˢ (Set.univ : Set ℝ)))  :=
by
  intro hcnt
  have hun : ({0, 1} : Set ℕ) = {0} ∪ {1} := by
    rw [Set.union_comm, Set.union_singleton]
  rw [hun] at hcnt
  simp_rw
    [Set.union_prod,
     Set.countable_union,
     Set.countable_iff_exists_injective] at hcnt
  rcases hcnt with ⟨⟨f, finj⟩⟩

  let g : ↑(Set.univ : Set ℝ) → ({0} ×ˢ (Set.univ : Set ℝ))
    := λ r => ⟨((0 : ℕ), r), by simp⟩
  have ginj : Function.Injective g := by
    intro a b heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and] at heq
    exact SetCoe.ext heq

  let fg : ↑(Set.univ : Set ℝ) → ℕ := f ∘ g
  have fginj := Function.Injective.comp finj ginj

  exact Cardinal.not_countable_real (Set.countable_iff_exists_injective.mpr ⟨fg, fginj⟩)

  -- b)
def Countably_Infinite {α : Type} (s : Set α) : Prop := Set.Countable s ∧ Set.Infinite s
def Uncountable {α : Type} (s : Set α) : Prop := ¬(Set.Countable s) ∧ (Set.Infinite s)

lemma uncountable_minus_countably_infinite_uncountable
  {α : Type}
  {A B : Set α}
  (hsub : A ⊆ B)
  (hcntiA : Countably_Infinite A)
  (hucnt : Uncountable B)
  : Uncountable (B \ A) :=
by
  rcases hcntiA with ⟨hcntA⟩
  constructor
  · intro hcntmin
    have hcntB := Set.Countable.union hcntA hcntmin
    rw [Set.union_diff_cancel hsub] at hcntB
    exact hucnt.1 hcntB
  · by_contra hninf
    rw [@Set.not_infinite] at hninf
    have hcnt := Set.Finite.countable hninf
    have hcntB := Set.Countable.union hcntA hcnt
    rw [Set.union_diff_cancel hsub] at hcntB
    exact hucnt.1 hcntB

-- Exercise 2
def indicator : Set (ℝ → ({0, 1} : Set ℕ)) := Set.univ

lemma indicator_card_gt_real_card
  : Cardinal.mk indicator > Cardinal.mk (Set.univ : Set ℝ) :=
by
  simp only [Cardinal.mk_univ, indicator]
  rw [←Cardinal.power_def, Cardinal.mk_insert (by simp), Cardinal.mk_singleton]
  ring_nf
  exact Cardinal.cantor (Cardinal.mk ℝ)

inductive binary : Type
  | zero : binary
  | one : binary

lemma binary_zero_eq_iff_one_eq
  {a b : binary}
  (hb : b = binary.one ↔ a = binary.one)
  : b = binary.zero ↔ a = binary.zero :=
by
  cases b
  · simp only [false_iff, forall_true_left] at *
    cases a
    · simp only
    · simp only [not_true_eq_false] at *
  · simp at *
    cases a
    · simp only at *
    · simp only [not_false_eq_true]

lemma binary_ne_one_eq_zero
  {b : binary}
  (hb : ¬b = binary.one)
  : b = binary.zero :=
by
  cases b
  · simp only
  · simp only [not_true_eq_false] at *

def indicator' : Set (ℝ → binary) := Set.univ

lemma indicator_card_eq_powerset_card_bij
  : ∃ f : indicator' → (𝒫 (Set.univ : Set ℝ)), Function.Bijective f :=
by
  let f : indicator' → (𝒫 (Set.univ : Set ℝ)) := by
    rw [indicator']
    rintro ⟨fn, _⟩
    exact {
      val := Set.preimage fn {binary.one}
      property := by simp only [Set.powerset_univ, Set.mem_univ]
    }
  use f
  constructor
  · rintro ⟨fa, _⟩ ⟨fb, _⟩ heq
    simp only [Set.powerset_univ] at f
    simp only [eq_mpr_eq_cast, cast_eq, Subtype.mk.injEq] at heq
    rw [Set.ext_iff] at heq
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at heq
    have heqv : fa = fb := by
      ext x
      specialize heq x
      have hzero_iff := binary_zero_eq_iff_one_eq heq
      by_cases heqfa : fa x = binary.one
      · have heqfbzero := heq.mp heqfa
        rw [←heqfbzero] at heqfa
        exact heqfa
      · have heqfazero := binary_ne_one_eq_zero heqfa
        have heqfbone := hzero_iff.mp heqfazero
        rw [←heqfbone] at heqfazero
        exact heqfazero
    exact SetCoe.ext heqv
  · intro pw
    let a : ↑indicator' := by
      rw [indicator']
      constructor
      · simp only [Set.mem_univ]
      · intro x
        simp at pw
        have real_set := pw.1
        haveI := Classical.dec (x ∈ real_set)
        exact (ite (x ∈ real_set) binary.one binary.zero)
    use a
    simp only [eq_mpr_eq_cast, cast_eq, eq_mp_eq_cast, Set.powerset_univ, set_coe_cast]
    apply Subtype.eq
    simp only [Set.powerset_univ, set_coe_cast, Set.ext_iff]
    intro x
    simp only [Set.powerset_univ, set_coe_cast, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hite
      split_ifs at hite with hi
      · simp only [Set.powerset_univ, set_coe_cast] at hi
        exact hi
    · intro el
      split_ifs with hi
      · rfl
      · simp only [Set.powerset_univ, set_coe_cast] at hi
        exact hi el

-- Exercise 3
lemma power_nat_nat_card_eq_power_nat
  : Cardinal.mk (𝒫 (Set.univ : Set (ℕ × ℕ))) = Cardinal.mk (𝒫 (Set.univ : Set ℕ)) :=
by
  simp only [Cardinal.mk_powerset,
             Cardinal.mk_univ,
             Cardinal.mk_eq_aleph0,
             Cardinal.two_power_aleph0]

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

lemma power_nat_nat_card_eq_power_nat_csb
  : ∃ fg : (𝒫 (Set.univ : Set (ℕ × ℕ))) → (𝒫 (Set.univ : Set ℕ)), Function.Bijective fg :=
by
  let f : (𝒫 (Set.univ : Set (ℕ × ℕ))) → (𝒫 (Set.univ : Set ℕ)) := by
    intro a_set_of_nxn
    exact {
      val := {2^x.1 * 3^x.2 | x ∈ a_set_of_nxn.val}
      property := by simp only [Set.powerset_univ, Set.mem_univ]
    }
  have hf : Function.Injective f := by
    rintro ⟨p, _⟩ ⟨q, _⟩ heq
    simp only [f, Prod.exists, Subtype.mk.injEq, Set.ext_iff, Set.mem_setOf_eq] at heq
    rw [Subtype.mk.injEq, Set.ext_iff]
    intro x
    let uniq := 2^x.1 * 3^x.2
    specialize heq uniq
    rcases heq with ⟨pimpq, qimpp⟩
    constructor
    · intro hmemp
      have ⟨a, ⟨b, ⟨hmemq, heqfac⟩⟩⟩
        := pimpq ⟨x.1, ⟨x.2, by simp only [Prod.mk.eta,and_true]; exact hmemp⟩⟩
      simp_rw [uniq] at heqfac
      have ⟨heq1, heq2⟩ := two_pow_three_pow_unique_factorization heqfac
      rw [heq1, heq2] at hmemq
      exact hmemq
    · intro hmemq
      have ⟨a, ⟨b, ⟨hmemp, heqfac⟩⟩⟩
        := qimpp ⟨x.1, ⟨x.2, by simp only [Prod.mk.eta,and_true]; exact hmemq⟩⟩
      simp_rw [uniq] at heqfac
      have ⟨heq1, heq2⟩ := two_pow_three_pow_unique_factorization heqfac
      rw [heq1, heq2] at hmemp
      exact hmemp

  let g : (𝒫 (Set.univ : Set ℕ)) → (𝒫 (Set.univ : Set (ℕ × ℕ))) := by
    intro a_set_of_n
    have a_set_of_nxn : Set (ℕ × ℕ) := a_set_of_n.val ×ˢ a_set_of_n.val
    exact { val := a_set_of_nxn, property := by simp }
  have hg : Function.Injective g := by
    intros a b heq
    simp only [g, Subtype.mk.injEq, Set.prod_eq_prod_iff] at heq
    rcases heq with (coe_eq | ⟨ha, hb⟩)
    · exact SetCoe.ext coe_eq.1
    · simp only [or_self] at ha
      simp only [or_self] at hb
      rw [←hb] at ha
      exact SetCoe.ext ha

  exact Function.Embedding.schroeder_bernstein hf hg
