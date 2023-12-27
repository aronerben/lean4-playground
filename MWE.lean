import Mathlib.Tactic

@[simp]
def IsOrdered {α : Type} [LE α] : List α → Prop :=
  List.Pairwise LE.le

structure OrderedList (α : Type) [LE α] where
  val : List α
  ordered : IsOrdered val

@[simp]
instance [LE α]
  : Membership α (OrderedList α)
:= ⟨λ a xs => a ∈ xs.val⟩

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

def oinsert
  {α : Type} [hp : LE α]
  (a : α)
  (l : OrderedList α)
  [DecidableRel hp.le]
  : OrderedList α
:= match l with
  | ⟨[], _⟩ => ⟨[a], List.pairwise_singleton LE.le a⟩
  | ⟨x :: xs, ordered⟩ =>
      if hle : ∀ (x : α), x ∈ l → a ≤ x
      then ocons a l hle
      else ocons x (oinsert a ⟨xs, List.Pairwise.of_cons ordered⟩)
        (sorry)

def insert
  {α : Type} [hp : LE α]
  (a : α)
  (l : List α)
  [DecidableRel hp.le]
  : List α
:= match l with
  | [] => [a]
  | x :: xs =>
      if hle : ∀ (x : α), x ∈ l → a ≤ x
      then a :: x :: xs
      else  x :: (insert a xs)



mutual
inductive OrderedList' (α : Type) [LE α] where
| onil' : OrderedList' α
| ocons' (x : α) (xs : OrderedList' α) : less x xs → OrderedList' α

def less
  {α : Type} [LE α]
  (x : α)
  (xs : OrderedList' α) :=
  match xs with
  | OrderedList'.onil' => True
  | OrderedList'.ocons' y ys _ => x ≤ y
end
