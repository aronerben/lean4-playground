import Mathlib.Tactic

def hello := "world"

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n 
  { simp? }
  { simp }

def has_unique_right_inverse 
  {α : Type*} {β : Type*} 
  (f : α → β) 
  : Prop 
:= ∃! (g : β → α), ∀ (b : β), f (g b) = b

def injective 
  {α : Type*} {β : Type*} 
  (f : α → β) 
  : Prop 
:= ∀ (a₁ a₂ : α), f a₁ = f a₂ → a₁ = a₂

def surjective 
  {α : Type*} {β : Type*} 
  (f : α → β) 
  : Prop 
:= ∀ (b : β), ∃ (a : α), f a = b

def bijective 
  {α : Type*} {β : Type*} 
  (f : α → β) 
  : Prop 
:= injective f ∧ surjective f 

lemma bijective_if_unique_right_inverse
  {α : Type*} {β : Type*} (f : α → β) (h : has_unique_right_inverse f)
  : bijective f := by
  rw [bijective]
  rw [has_unique_right_inverse] at h
  constructor
  -- unique right inverse → injective
  { rw [injective]
    intros a₁ a₂ funxt
    rcases h with ⟨rinv, hinv, hunique⟩ 
    dsimp at hunique
    
    specialize hunique rinv
    have foo1 := hinv (f a₁)
    have foo2 := hinv (f a₂)

    -- rcases h with
    -- | intro rinv h_inv_unique =>
    --   cases h_inv_unique with
    --   | intro hinv hunique => 
    --     dsimp at hinv
    --     dsimp at hunique






  }
  {  }

