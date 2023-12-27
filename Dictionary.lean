import Mathlib.Tactic
import Mathlib.Tactic.Basic

@[simp]
def IsOrdered {α : Type} [LE α] : List α → Prop :=
  List.Pairwise LE.le

structure OrderedList (α : Type) [LE α] where
  val : List α
  ordered : IsOrdered val

instance {α : Type} [LE α]
  : Membership α (OrderedList α)
:= ⟨λ a xs => a ∈ xs.val⟩

instance {α : Type} [LE α] [Repr α]
  : Repr (OrderedList α) where
  reprPrec
    | ⟨l, _⟩ => l.repr

#reduce ((⟨[1,2,3,3,3,4], List.pwFilter_eq_self.mp rfl⟩) : OrderedList Nat)
#check ((⟨[0,19,30,201], List.pwFilter_eq_self.mp rfl⟩) : OrderedList Nat)
#eval ((⟨[0,19,30,201], List.pwFilter_eq_self.mp rfl⟩) : OrderedList Nat)

lemma cons_le_is_ordered
  {α : Type} [LE α]
  {a : α}
  {xs : List α}
  (h : IsOrdered xs)
  (hle : ∀ (x : α), x ∈ xs → a ≤ x)
  : IsOrdered (a :: xs) :=
by
  simp only [IsOrdered, List.pairwise_cons] at *
  exact ⟨hle, h⟩

def ocons
  {α : Type} [LE α]
  (a : α)
  (xs : OrderedList α)
  (hle : ∀ (x : α), x ∈ xs → a ≤ x)
  : OrderedList α
:= ⟨a :: xs.val, cons_le_is_ordered xs.ordered hle⟩

#eval ocons 0 (⟨[2,3,4], List.pwFilter_eq_self.mp rfl⟩ : OrderedList ℕ) (by exact fun x _ => Nat.zero_le x)

def insert'
  {α : Type} [hp : LE α]
  (a : α)
  (l : List α)
  [DecidableRel hp.le]
  : List α
:= match l with
  | [] => [a]
  | x :: xs =>
      if a ≤ x
      then a :: x :: xs
      else x :: (insert' a xs)

#eval insert' 4 [3, 3, 4, 5, 9]

lemma insert_mem
  {α : Type} [hp : LE α]
  [DecidableRel hp.le]
  {x a : α}
  {l : List α}
  : x ∈ insert' a l ↔ x = a ∨ x ∈ l :=
by
  constructor
  · intro hel
    induction' l with y ys ih
    · rw [insert', List.mem_singleton] at hel
      left
      exact hel
    · rw [insert'] at hel
      split_ifs at hel
      · simp only [List.mem_cons] at hel
        simp only [List.mem_cons]
        exact hel
      · simp only [List.mem_cons] at hel
        simp only [List.mem_cons]
        rcases hel with (heq | hmem)
        · right
          left
          exact heq
        · rcases ih hmem with (heq' | hmem')
          · left
            exact heq'
          · right
            right
            exact hmem'
  · intro hor
    induction' l with y ys ih
    · rw [insert', List.mem_singleton]
      rcases hor with (heq | hmem)
      · exact heq
      · simp only [List.not_mem_nil] at hmem
    · rw [insert']
      split_ifs
      · simp only [List.mem_cons]
        rcases hor with (heq | hmem)
        · left
          exact heq
        · right
          simp only [List.mem_cons] at hmem
          exact hmem
      · simp only [List.mem_cons]
        rcases hor with (heq | hmem)
        · right
          exact ih (Or.inl heq)
        · simp only [List.mem_cons] at hmem
          rcases hmem with (heq' | hmem')
          · left
            exact heq'
          · right
            exact ih (Or.inr hmem')

lemma ordered_insert_is_ordered
  {α : Type} [hl : LinearOrder α]
  [DecidableRel hl.le]
  {a : α}
  {l : List α}
  (ordered : IsOrdered l)
  : IsOrdered (insert' a l) :=
by
  simp at *
  induction' l with x xs ih
  · rw [insert', List.pairwise_cons]
    constructor
    · intros y hy
      simp only [List.find?_nil, List.not_mem_nil] at hy
    · exact ordered
  · rw [insert']
    split_ifs with h
    · rw [List.pairwise_cons]
      constructor
      · intro y hy
        rw [List.mem_cons] at hy
        rcases hy with (heq | hmem)
        · rw [heq]
          exact h
        · rw [List.pairwise_cons] at ordered
          have hle := ordered.1 y hmem
          exact ge_trans hle h
      · exact ordered
    · rw [List.pairwise_cons]
      rw [List.pairwise_cons] at ordered
      constructor
      · intros y hy
        rw [insert_mem] at hy
        rcases hy with (heq | hmem)
        · rw [heq]
          rw [not_le] at h
          exact le_of_lt h
        · exact ordered.1 y hmem
      · exact ih ordered.2

def oinsert
  {α : Type} [hl : LinearOrder α]
  (a : α)
  (l : OrderedList α)
  [DecidableRel hl.le]
  : OrderedList α
:= ⟨insert' a l.val, ordered_insert_is_ordered l.ordered⟩

#eval oinsert (-2) (⟨[2,3,5,6], List.pwFilter_eq_self.mp rfl⟩ : OrderedList ℤ)

#eval oinsert 100 (⟨[3,6,9], List.pwFilter_eq_self.mp rfl⟩ : OrderedList ℕ)

def append
  {α : Type} [hl : LinearOrder α]
  (xs : OrderedList α)
  (ys : OrderedList α)
  [DecidableRel hl.le]
  : OrderedList α
:=
  match xs with
  | ⟨[], _⟩ => ys
  | ⟨x :: xs, ordered⟩ => oinsert x (append ⟨xs, List.Pairwise.of_cons ordered⟩ ys)

#eval append ((⟨[3, 6, 9], List.pwFilter_eq_self.mp rfl⟩) : OrderedList Nat) ((⟨[0, 1, 5, 7, 10], List.pwFilter_eq_self.mp rfl⟩) : OrderedList Nat)

def OrderedList.head
  {α : Type} [LE α]
  (xs : OrderedList α) (hnemp : xs.val ≠ []) : α :=
  xs.val.head hnemp

-- #check ocons 1 onil
-- #eval ocons 1 snil

-- syntax (name := sortedNotation) "S[" term,* "]" : term

-- macro_rules
--   | `(S[$term:term, $terms:term,*]) => `(scons $term S[$terms,*])
--   | `(S[$term:term]) => `(scons $term S[])
--   | `(S[]) => `(snil)

-- /-- Unexpander for the `S[x, y, ...]` notation. -/
-- @[app_unexpander scons]
-- def sconsUnexpander : Lean.PrettyPrinter.Unexpander
--   | `($_ $term S[$term2, $terms,*]) => `(S[$term, $term2, $terms,*])
--   | `($_ $term S[$term2]) => `(S[$term, $term2])
--   | `($_ $term S[]) => `(S[$term])
--   | _ => throw ()

-- /-- Unexpander for the `![]` notation. -/
-- @[app_unexpander snil]
-- def snilUnexpander : Lean.PrettyPrinter.Unexpander
--   | _ => `(S[])

-- #check S[2,1,2,3]


def dictionary_sort
  {α : Type}
  [LT α]
  (p q : List α)
  : Prop :=
  match p, q with
  -- Lists fully match
  | [], [] => False
  -- First list shorter
  | [], _ => True
  -- Second list shorter
  | _, [] => False
  | a :: p', b :: q' =>  a < b ∨ (a = b ∧ (dictionary_sort p' q'))
