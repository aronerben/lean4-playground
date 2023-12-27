import Mathlib.Tactic
import Mathlib.Tactic.Basic

-- Exercise 1
def Countably_Infinite {α : Type} (s : Set α) : Prop := Set.Countable s ∧ Set.Infinite s
def Uncountable {α : Type} (s : Set α) : Prop := ¬(Set.Countable s) ∧ (Set.Infinite s)
-- a)
lemma prod_bin_real_uncountable
  : Uncountable (({0, 1} : Set ℕ) ×ˢ (Set.univ : Set ℝ))  :=
by
  have hucnt
    : ¬(Set.Countable (({0, 1} : Set ℕ) ×ˢ (Set.univ : Set ℝ))) := by
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
  constructor
  · exact hucnt
  · have hncnt {α : Type} {s : Set α}
      : ¬Set.Countable s → Set.Infinite s := by
      contrapose
      simp only [Set.mem_singleton_iff, Set.not_infinite, not_not, Set.Finite.countable]
      exact Set.Finite.countable
    exact hncnt hucnt

-- b)
lemma uncountable_minus_countably_infinite_uncountable
  {α : Type}
  {A B : Set α}
  (hsub : A ⊆ B)
  (hcntiA : Countably_Infinite A)
  (hucnt : Uncountable B)
  : Uncountable (B \ A) :=
by
  rcases hcntiA with ⟨hcntA, _⟩
  constructor
  · intro hcntmin
    have hcntB := Set.Countable.union hcntA hcntmin
    rw [Set.union_diff_cancel hsub] at hcntB
    exact hucnt.1 hcntB
  · intro hfin
    have hcnt := Set.Finite.countable hfin
    have hcntB := Set.Countable.union hcntA hcnt
    rw [Set.union_diff_cancel hsub] at hcntB
    exact hucnt.1 hcntB

-- Exercise 2
def binary' : Set ℕ := {0, 1}

def indicator : Set (ℝ → (binary')) := Set.univ

lemma indicator_card_gt_real_card
  : Cardinal.mk indicator > Cardinal.mk (Set.univ : Set ℝ) :=
by
  simp only [Cardinal.mk_univ, indicator]
  rw [binary', ←Cardinal.power_def, Cardinal.mk_insert (by simp), Cardinal.mk_singleton]
  ring_nf
  exact Cardinal.cantor (Cardinal.mk ℝ)

lemma binary'_zero_eq_iff_one_eq
  {b : binary'}
  (hb : ¬b.val = 1)
  : b.val = 0 :=
by
  rcases b with ⟨hv, hp⟩
  dsimp only at *
  rw [binary'] at hp
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hp
  rcases hp with (h0 | h1)
  · exact h0
  · exfalso
    exact hb h1

-- Alternatively
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
  · simp only [true_iff, false_iff] at *
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
        simp only [Set.powerset_univ] at pw
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

-- Exercise 4
axiom α : Type
axiom N0 : Set α
axiom S : N0 → N0

axiom z : N0
axiom p1 : ∀ n : N0, S n ≠ z
axiom p2 : Function.Injective S
axiom p3 : ∀ A : Set ↑N0,
            z ∈ A
            ∧ (∀ n : N0, n ∈ A → (S n) ∈ A)
            → A = N0

-- Example
lemma every_nonzero_nat_successor
  (n : N0)
  : n ≠ z → ∃ m : N0, n = S m :=
by
  intro hne
  let A := {n : N0 | n ≠ z → ∃ m : N0, n = S m}
  have hzmem : z ∈ A := by
    simp only [ne_eq, Subtype.exists, Set.mem_setOf_eq, not_true_eq_false, IsEmpty.forall_iff]
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n _
    simp only [ne_eq, Subtype.exists, Set.mem_setOf_eq]
    intro _
    use n
    simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq n
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  rcases heq hne with ⟨a, ⟨h, heq⟩⟩
  use { val := a, property := h }

axiom plus : N0 × N0 → N0
axiom zplus : ∀ x : N0, plus (x, z) = x
axiom splus : ∀ x y : N0, plus (x, (S y)) = S (plus (x, y))

axiom mul : N0 × N0 → N0
axiom zmul : ∀ x : N0, mul (x, z) = z
axiom smul : ∀ x y : N0, mul (x, (S y)) = plus (mul (x, y), x)

-- a)
lemma zero_plus_x_eq_eq
  (x : N0)
  : plus (z, x) = x :=
by
  let A := {b : N0 | plus (z, b) = b}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    exact zplus z
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    rw [splus, hel]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq x
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

-- b)
-- Helper
lemma succ_plus_eq_succ_plus
  (x y : N0)
  : plus ((S x), y) = S (plus (x, y)) :=
by
  let A := {y : N0 | plus ((S x), y) = S (plus (x, y))}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    simp [zplus]
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    rw [splus, hel, ←splus]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq y
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

lemma succ_plus_n_eq_succ_n_plus
  (x y : N0)
  : plus ((S y), x) = S (plus (x, y)) :=
by
  let A := {x : N0 | plus ((S y), x) = S (plus (x, y))}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    rw [zplus, zero_plus_x_eq_eq]
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    rw [splus, hel, succ_plus_eq_succ_plus]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq x
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

-- c)
lemma zero_mul_eq_zero
  (x : N0)
  : mul (z, x) = z :=
by
  let A := {x : N0 | mul (z, x) = z}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    rw [zmul]
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    rw [smul, hel, zero_plus_x_eq_eq]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq x
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

-- d)
lemma succ_zero_mul_eq_self
  (x : N0)
  : mul (S z, x) = x :=
by
  let A := {x : N0 | mul (S z, x) = x}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    rw [zmul]
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    rw [smul, hel, splus, zplus]
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq x
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

-- Generic recursor on my axioms
lemma generic_recursor
  {motive : N0 → Prop}
  (hz : motive z)
  (hs : ∀ n : N0, motive n → motive (S n))
  (x : N0)
  : motive x :=
by
  let A := {x : N0 | motive x}
  have hzmem : z ∈ A := by
    simp only [Set.mem_setOf_eq]
    exact hz
  have hind : (∀ n : N0, n ∈ A → (S n) ∈ A) := by
    intros n hel
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hel
    specialize hs n
    exact hs hel
  have heq := p3 A ⟨hzmem, hind⟩
  simp [A, Set.ext_iff] at heq
  specialize heq x
  simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, iff_true] at heq
  exact heq

lemma succ_zero_mul_eq_self'
  : ∀ x, mul (S z, x) = x :=
by
  apply generic_recursor
  · rw [zmul]
  · intros x hi
    rw [smul, hi, splus, zplus]

lemma succ_plus_n_eq_succ_n_plus'
  : ∀ x y, plus ((S y), x) = S (plus (x, y)) :=
by
  apply generic_recursor
  · intro y
    rw [zplus, zero_plus_x_eq_eq]
  · intros n hi y
    rw [splus, hi, succ_plus_eq_succ_plus]
