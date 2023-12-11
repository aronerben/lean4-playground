import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Card

-- Exercise 1
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

axiom plus : N0 × N0 → N0
axiom zplus : ∀ x : N0, plus (x, z) = x
axiom splus : ∀ x y : N0, plus (x, (S y)) = S (plus (x, y))

axiom mul : N0 × N0 → N0
axiom zmul : ∀ x : N0, mul (x, z) = z
axiom smul : ∀ x y : N0, mul (x, (S y)) = plus (mul (x, y), x)

axiom exp : N0 × N0 → N0
axiom zexp : ∀ m : N0, exp (m, z) = S z
axiom sexp : ∀ m n : N0, exp (m, (S n)) = mul (exp (m, n), m)

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

-- a)
-- Helpers
----- Already proved
lemma zero_plus_x_eq_eq
  : ∀ x, plus (z, x) = x :=
by
  apply generic_recursor
  · exact zplus z
  · intros n hi
    rw [splus, hi]
----- Already proved

lemma plus_assoc
  : ∀ c a b, plus (a, plus (b, c)) = plus (plus (a, b), c) :=
by
  apply generic_recursor
  · intro a b
    rw [zplus, zplus]
  · intro c hi a b
    specialize hi a b
    rw [splus, splus, hi, splus]

lemma mul_distrib_add
  : ∀ c a b, mul (a, plus (b, c)) = plus (mul (a, b), mul (a, c)) :=
by
  apply generic_recursor
  · intro a b
    rw [zplus, zmul, zplus]
  · intro c hi a b
    specialize hi a b
    rw [splus, smul, smul, hi, plus_assoc]

lemma mul_assoc'
  : ∀ c a b, mul (mul (a, b), c) = mul (a, mul (b, c)) :=
by
  apply generic_recursor
  · intro a b
    rw [zmul, zmul, zmul]
  · intro c hi a b
    specialize hi a b
    rw [smul, smul, hi, mul_distrib_add]

lemma exp_add_eq_mul_exp_exp
  : ∀ r m n, exp (m, (plus (n, r))) = mul (exp (m, n), exp (m, r)) :=
by
  apply generic_recursor
  · intros m n
    rw [zplus, zexp, smul, zmul, zero_plus_x_eq_eq]
  · intros n hi m r
    specialize hi m r
    rw [splus, sexp, sexp, hi, mul_assoc']

-- b)
lemma exp_assoc
  : ∀ r m n, exp ((exp (m, n)), r) = exp (m, mul (n, r)) :=
by
  apply generic_recursor
  · intros m n
    rw [zexp, zmul, zexp]
  · intros r hi m n
    specialize hi m n
    rw [smul, sexp, exp_add_eq_mul_exp_exp, hi]

-- c)
-- Helpers
----- Already proved
lemma succ_zero_mul_eq_self'
  : ∀ x, mul (S z, x) = x :=
by
  apply generic_recursor
  · rw [zmul]
  · intros x hi
    rw [smul, hi, splus, zplus]

lemma zero_mul_eq_zero
  : ∀ x, mul (z, x) = z :=
by
  apply generic_recursor
  · rw [zmul]
  · intro x hi
    rw [smul, hi, zero_plus_x_eq_eq]

lemma succ_plus_eq_succ_plus
  : ∀ b a, plus ((S a), b) = S (plus (a, b)) :=
by
  apply generic_recursor
  · intro a
    rw [zplus, zplus]
  · intro b hi a
    specialize hi a
    rw [splus, hi, ←splus]
----- Already proved
lemma plus_comm
  : ∀ a b, plus (a, b) = plus (b, a) :=
by
  apply generic_recursor
  · intro a
    rw [zplus, zero_plus_x_eq_eq]
  · intro a hi b
    specialize hi b
    rw [splus, succ_plus_eq_succ_plus, hi]

lemma muls
  : ∀ b a, mul (S a, b) = plus (mul (a, b), b) :=
by
  apply generic_recursor
  · intro a
    rw [zmul, zmul, zplus]
  · intro b hi a
    specialize hi a
    rw [smul, smul, hi, splus, splus, ←plus_assoc, plus_comm b, plus_assoc]

lemma mul_comm'
  : ∀ a b, mul (a, b) = mul (b, a) :=
by
  apply generic_recursor
  · intro a
    rw [zmul, zero_mul_eq_zero]
  · intro a hi b
    specialize hi b
    rw [smul, muls, hi]

lemma exp_distrib_mul
  : ∀ r m n, exp (mul (m, n), r) = mul (exp (m, r), exp (n, r)) :=
by
  apply generic_recursor
  · intro m n
    rw [zexp, zexp, zexp, succ_zero_mul_eq_self']
  · intro r hi m n
    specialize hi m n
    rw [sexp, sexp, sexp, hi, ←mul_assoc', mul_assoc' m, mul_comm' _ m, ←mul_assoc', ←mul_assoc']

-- Exercise 2
inductive Strand : Type where
  | strand : Strand

abbrev Hair := List Strand

structure Person where
  hair : Hair

-- a)
def Bald (person : Person) : Prop := person.hair = ∅

def add_one_hair (person : Person) : Person := ⟨Strand.strand :: person.hair⟩

axiom add_one_hair_still_bald
  {person : Person}
  : Bald person → Bald (add_one_hair person)

lemma all_people_bald
  : ∀ person : Person, Bald (person) :=
by
  intro person
  rw [Bald]
  induction' person.hair with _ h ih
  · rfl
  · have baldie := add_one_hair_still_bald ih
    rw [add_one_hair, Bald] at baldie
    exact baldie

-- b)
-- Won't work, need more base cases => Strong induction
-- lemma all_people_same_hair_amount
--   : ∀ people : Finset Person,
--       Set.ncard {List.length p.hair | p ∈ people} = 1
--       ∨ Set.ncard {List.length p.hair | p ∈ people} = 0 :=
-- by
--   intro people
--   let n := Finset.card people
--   induction' n with n ih
--   · right
--     have : n = 0 := sorry
--     simp_rw [n] at this
--     rw [Finset.card_eq_zero] at this
--     rw [this]
--     simp only [Finset.not_mem_empty, false_and, exists_false, Set.setOf_false, Set.ncard_empty]
--   · left
--     sorry

-- Exercise 3
def ℕplus := {n : ℕ // n ≠ 0}

instance : Mul ℕplus where
  mul a b :=
    { val := a.val * b.val,
      property := by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨a.property, b.property⟩
    }

lemma ℕplus.mul_def (a b : ℕplus)
  : a * b =
    { val := a.val * b.val,
      property := by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨a.property, b.property⟩
    }
 := rfl

instance : Semigroup ℕplus where
  mul_assoc := by
    intros a b c
    rw [Subtype.ext_iff]
    exact Nat.mul_assoc a.val b.val c.val

instance : Dvd ℕplus where
  dvd a b := ∃ c, b = a * c

def R3 (a b : ℕplus) : Prop := a ∣ b

lemma dvd_iff_nat_dvd
  {a b : ℕplus}
  : R3 a b ↔ a.val ∣ b.val :=
by
  constructor
  · intro hdvd
    rcases hdvd with ⟨c, hc⟩
    use c.val
    rw [ℕplus.mul_def] at hc
    apply_fun Subtype.val at hc
    exact hc
  · intro hdvd
    rcases hdvd with ⟨c, hc⟩
    have hb := b.property
    rw [hc, mul_ne_zero_iff] at hb
    let lc : ℕplus := ⟨c, hb.2⟩
    use lc
    rw [Subtype.ext_iff]
    exact hc

instance : DecidableRel R3 :=
  λ a b : ℕplus => decidable_of_iff' (a.val ∣ b.val) dvd_iff_nat_dvd

instance {n : ℕ} : OfNat ℕplus n where
  ofNat := match n with
  -- NEVER USE 0 LITERAL FOR THIS TYPE
    | 0 => ⟨1, by linarith⟩
    | i + 1 => ⟨i + 1, by linarith⟩

-- #eval R3 3 6

def PartialOrder'
  {α : Type}
  (rel : α → α → Prop)
  : Prop :=
  ∀ a b c : α, (rel a b → rel b c → rel a c)
  ∧ (rel a b → rel b a → a = b)

def WeakOrder
  {α : Type}
  (rel : α → α → Prop)
  : Prop :=
  PartialOrder' rel
  ∧ ∀ a b : α, rel a b ∨ rel b a

def Trichotomy (a b c : Prop) : Prop :=
(¬a ∧ ¬b ∧ c) ∨ (¬a ∧ b ∧ ¬c) ∨ (a ∧ ¬b ∧ ¬c)


-- TODO FIX THIS
-- > is not included as a strict order
def StrictOrder
  {α : Type}
  (rel : α → α → Prop)
  : Prop :=
  ∀ a b c : α, (rel a b → rel b c → rel a c)
  ∧ Trichotomy (rel a b) (rel b a) (a = b)

  -- ∀ a b : α, rel a b ↔ WeakOrder rel ∧ rel a b ∧ a ≠ b

  -- ∀ a b c : α, (rel a b → rel b c → rel a c)
  -- ∧ (rel a b ∨ rel b a ∨ a = b)

  -- WeakOrder rel ∧ ∀ a b : α, rel a b ∧ a ≠ b

lemma r3_not_weak_order
  : ¬WeakOrder R3 :=
by
  intro hwo
  simp_rw [WeakOrder, PartialOrder', R3] at hwo
  have hf := hwo.2 2 3
  rcases hf with (hdvd3 | hdvd2)
  · rw [dvd_def] at hdvd3
    rcases hdvd3 with ⟨c, hc⟩
    rw [Subtype.ext_iff] at hc
    have hdvd : ∃ c : ℕ, (3 : ℕ) = 2 * c := ⟨c.val, hc⟩
    rw [←dvd_def] at hdvd
    contradiction
  · rw [dvd_def] at hdvd2
    rcases hdvd2 with ⟨c, hc⟩
    rw [Subtype.ext_iff] at hc
    have hdvd : ∃ c : ℕ, (2 : ℕ) = 3 * c := ⟨c.val, hc⟩
    rw [←dvd_def] at hdvd
    contradiction

lemma r3_not_strict_order
  : ¬StrictOrder R3 :=
by
  intro hso
  rw [StrictOrder] at hso
  specialize hso 2 3 1
  rcases hso with ⟨_, (⟨_, _, heq⟩ | ⟨_, hdvd3, _⟩ | ⟨hdvd2, _, _⟩)⟩
  · rw [←Subtype.coe_inj] at heq
    contradiction
  · contradiction
  · contradiction

lemma r3_partial_order
  : PartialOrder' R3 :=
by
  intros hpo b c
  simp [R3]
  constructor
  · intro hdvdb hdvdc
    rw [dvd_def] at hdvdb
    rw [dvd_def] at hdvdc
    rw [dvd_def]
    rcases hdvdb with ⟨k, hk⟩
    rcases hdvdc with ⟨l, hl⟩
    rw [Subtype.ext_iff] at hk
    rw [Subtype.ext_iff] at hl
    use (k * l)
    rw [Subtype.ext_iff]
    simp_rw [hl, ℕplus.mul_def]
    simp only [ne_eq]
    simp_rw [hk, ℕplus.mul_def]
    exact Nat.mul_assoc hpo.val k.val l.val
  · intro hdvdb hdvdhpo
    rw [dvd_def] at hdvdb
    rw [dvd_def] at hdvdhpo
    rcases hdvdb with ⟨k, hk⟩
    rcases hdvdhpo with ⟨l, hl⟩
    rw [Subtype.ext_iff, ℕplus.mul_def] at hk
    simp at hk
    rw [Subtype.ext_iff, ℕplus.mul_def] at hl
    simp at hl
    rw [Subtype.ext_iff]
    rw [hk] at hl
    symm at hl
    rw [Nat.mul_assoc, Nat.mul_right_eq_self_iff (Nat.zero_lt_of_ne_zero hpo.property), mul_eq_one] at hl
    rw [hl.1] at hk
    simp at hk
    symm
    exact hk

-- Exercise 4
def VeryDiv : Set ℕ := {1, 2, 6, 30, 210}

def R4 (a b : VeryDiv) : Prop := a.val ∣ b.val

lemma r4_weak_order
  : WeakOrder R4 :=
by
  simp only [WeakOrder, PartialOrder', R4]
  constructor
  · intros a b c
    constructor
    · exact Nat.dvd_trans
    · simp_rw [←SetCoe.ext_iff]
      exact Nat.dvd_antisymm
  · intros a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp_rw [VeryDiv] at *
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at *
    aesop
    · left; use 3
    · left; use 15
    · left; use 105
    · right; use 3
    · right; use 15
    · right; use 105
    · left; use 5
    · left; use 35
    · right; use 5
    · right; use 35
    · left; use 7
    · right; use 7

lemma r4_not_strict_order
  : ¬StrictOrder R4 :=
by
  intro hso
  simp_rw [StrictOrder, VeryDiv] at hso
  have hf := hso ⟨1, by tauto⟩ ⟨1, by tauto⟩ ⟨1, by tauto⟩
  simp_rw [R4] at hf
  rw [Trichotomy] at hf
  contradiction

-- Exercise 5
class CWeakOrder {α : Type u} (rel : α → α → Prop) : Prop where
  trans : ∀ {a b c : α}, rel a b → rel b c → rel a c
  total : ∀ {a b : α}, rel a b ∨ rel b a
  antisymm : ∀ {a b : α}, rel a b → rel b a → a = b

class CStrictOrder {α : Type u} (rel : α → α → Prop) : Prop where
  trans : ∀ {a b c : α}, rel a b → rel b c → rel a c
  trich : ∀ (a b : α), Trichotomy (rel a b) (rel b a) (a = b)

def R5
  {α : Type}
  (S : α → α → Prop)
  (T : α → α → Prop)
  [CStrictOrder S]
  [CStrictOrder T]
  [DecidableRel S]
  [DecidableRel T]
  [DecidableEq α]
  (p q : α × α)
  : Prop :=
  S p.1 q.1 ∨ (p.1 = q.1 ∧ T p.2 q.2)

instance
  {α : Type}
  {S : α → α → Prop} {T : α → α → Prop}
  [CStrictOrder S] [CStrictOrder T]
  [DecidableRel S] [DecidableRel T]
  [DecidableEq α]
  : DecidableRel (R5 S T) :=
by
  intro a b
  rw [R5]
  rw [←Prod.lex_iff]
  revert a b
  exact Prod.Lex.decidable S T

instance : CStrictOrder Nat.lt where
  trans := Nat.lt_trans
  trich := by
    intro a b
    rw [Trichotomy]
    have hltG (a b : ℕ) : a < b ↔ a ≠ b ∧ ¬b < a := by
      constructor
      · intro hlt
        constructor
        · exact Nat.ne_of_lt hlt
        · exact Nat.lt_asymm hlt
      · rintro ⟨hne, hlt⟩
        simp only [not_lt] at hlt
        exact Nat.lt_of_le_of_ne hlt hne
    have heqG (a b : ℕ) : a = b ↔ ¬b < a ∧ ¬a < b := by
      constructor
      · intro heq
        constructor
        · exact Eq.not_gt heq
        · exact Eq.not_gt (id heq.symm)
      · rintro ⟨hlt1, hlt2⟩
        simp only [ne_eq, not_lt] at hlt1 hlt2
        exact Nat.le_antisymm hlt1 hlt2
    rcases Nat.lt_trichotomy a b with (hlta | heq | hltb)
    · right
      right
      have hand := (hltG a b).mp hlta
      exact ⟨hlta, and_comm.mp hand⟩
    · left
      have hand := (heqG a b).mp heq
      rw [←and_assoc]
      exact ⟨and_comm.mp hand, heq⟩
    · right
      left
      have hand := (hltG b a).mp hltb
      rw [←and_assoc, and_comm, eq_comm, ←and_assoc]
      exact ⟨hand, hltb⟩

instance : DecidableRel Nat.lt := Nat.decLt

-- #eval R5 (Nat.lt) (Nat.lt) (1, 2) (2, 3)

lemma r5_strict_order
  {α : Type}
  (S : α → α → Prop)
  (T : α → α → Prop)
  [hS : CStrictOrder S]
  [hT : CStrictOrder T]
  [DecidableRel S]
  [DecidableRel T]
  [DecidableEq α]
  : StrictOrder (R5 S T) :=
by
  intro p q j
  simp_rw [R5]
  constructor
  · intros h1 h2
    rcases h1 with (hSp | ⟨heqp, hTp⟩)
    · rcases h2 with (hSq | ⟨heqq, hTq⟩)
      · left
        exact hS.trans hSp hSq
      · rw [heqq] at hSp
        left
        exact hSp
    · rcases h2 with (hSq | ⟨heqq, hTq⟩)
      · rw [heqp]
        left
        exact hSq
      · right
        constructor
        · rw [←heqp] at heqq
          exact heqq
        · exact hT.trans hTp hTq
  · have foo := hS.trich p.1 q.1
    have fool := hT.trich p.2 q.2
    rw [Trichotomy] at *
    -- Aesop magic
    rename_i inst inst_1 inst_2
    unhygienic with_reducible aesop_destruct_products
    simp_all only [Prod.mk.injEq, not_and]
    unhygienic aesop_cases foo <;> [(unhygienic aesop_cases fool <;> [skip; (unhygienic aesop_cases h_1)]);
      (unhygienic aesop_cases fool <;> [(unhygienic aesop_cases h);
          (unhygienic aesop_cases h <;> [(unhygienic aesop_cases h_1); (unhygienic aesop_cases h_1)])])]
    · simp_all only [true_and, and_self, and_true, not_true_eq_false, forall_true_left, and_false, or_self, or_false]
      unhygienic with_reducible aesop_destruct_products
      aesop_subst [right_2, right]
      simp_all only [not_false_eq_true, or_self]
    · simp_all only [and_false, or_false, and_self, or_true, not_true_eq_false, not_false_eq_true, forall_true_left,
        and_true, false_or]
      unhygienic with_reducible aesop_destruct_products
      aesop_subst right_2
      simp_all only [not_false_eq_true]
    · simp_all only [and_self, or_true, not_true_eq_false, and_false, or_false, not_false_eq_true, forall_true_left,
        and_true, false_and, true_and, false_or]
      unhygienic with_reducible aesop_destruct_products
      aesop_subst right_2
      simp_all only [not_false_eq_true]
    ·
      simp_all only [false_and, or_self, not_false_eq_true, true_or, not_true_eq_false, and_true, and_self, and_false,
        IsEmpty.forall_iff, or_false, or_true]
    · simp_all only [false_and, or_false, not_true_eq_false, false_or, not_and, and_true, and_false, and_self,
        IsEmpty.forall_iff, true_and]
      intro a
      aesop_subst a
      simp_all only [not_true_eq_false, and_false]
    ·
      simp_all only [and_self, or_self, not_false_eq_true, and_true, true_or, not_true_eq_false, and_false,
        IsEmpty.forall_iff, or_false, or_true]
    ·
      simp_all only [and_true, or_self, not_false_eq_true, and_false, or_false, not_true_eq_false, and_self,
        IsEmpty.forall_iff, or_true]
    · simp_all only [and_self, or_false, not_true_eq_false, and_true, false_or, and_false, IsEmpty.forall_iff,
        false_and, true_and]
      unhygienic with_reducible aesop_destruct_products
      apply Aesop.BuiltinRules.not_intro
      intro a
      aesop_subst a
      simp_all only
    ·
      simp_all only [and_true, or_false, not_true_eq_false, and_false, or_self, not_false_eq_true, and_self,
        IsEmpty.forall_iff, or_true]

lemma r5_not_weak_order
  {α : Type}
  (S : α → α → Prop)
  (T : α → α → Prop)
  [hS : CStrictOrder S]
  [hT : CStrictOrder T]
  [hn : Nonempty α]
  [DecidableRel S]
  [DecidableRel T]
  [DecidableEq α]
  : ¬WeakOrder (R5 S T) :=
by
  intro hwo
  rw [WeakOrder] at hwo
  have hf := hwo.2
  have p : α × α := Classical.choice Prod.Nonempty
  specialize hf p p
  simp [R5] at hf
  rcases hf with (hS1 | hT1)
  · rcases hS.trich p.1 p.1 with (hS2 | hS3 | hS4)
    · exact hS2.left hS1
    · exact hS3.left hS1
    · have := hS4.right.right
      contradiction
  · rcases hT.trich p.2 p.2 with (hT2 | hT3 | hT4)
    · exact hT2.left hT1
    · exact hT3.left hT1
    · have := hT4.right.right
      contradiction
