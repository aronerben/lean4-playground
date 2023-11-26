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
:= surjective f ∧ injective f 

open Classical

lemma bijective_if_unique_right_inverse
  {α : Type*} {β : Type*} (f : α → β) 
  (h_unique_rinv : has_unique_right_inverse f)
  (h_nonempty : Nonempty β)
  : bijective f := by
  rw [bijective]
  rw [has_unique_right_inverse] at h_unique_rinv
  rcases h_unique_rinv with ⟨rinv, h_rinv, h_unique⟩ 
  have surj : surjective f := by 
    rw [surjective]
    intro b
    constructor
    exact h_rinv b
  constructor
  { exact surj }
  -- unique right inverse → injective
  { rw [injective]
    intros a₁ a₂ h_funext
    dsimp at h_unique
    rw [surjective] at surj
    by_contra neq




    have h_left_inv : ∃ linv : β → α, ∀ a : α, linv (f a) = f (rinv b) := by
      have foo : ∃ b : β, f (rinv b) = b := by
        exact Exists.intro (f (rinv (f a₁))) (h_rinv (f (rinv (f a₁))))
      have moo := choose foo
      have moot := choose_spec foo

      use by
        intro b
        have foo := choose (surj b)
        have foot := choose_spec (surj b)
        exact foo
      simp



    -- have h_left_inv : ∃ linv : β → α, ∀ a : α, linv (f a) = a := by
    --   have foo : ∃ b : β, f (rinv b) = b := by
    --     exact Exists.intro (f (rinv (f a₁))) (h_rinv (f (rinv (f a₁))))
    --   have moo := choose foo
    --   have moot := choose_spec foo

    --   use by
    --     intro b
    --     have foo := choose (surj b)
    --     have foot := choose_spec (surj b)
    --     exact foo
    --   simp


        
        
      


        


    -- have h_left_inv : ∃ linv : β → α, ∀ a : α, linv (f a) = a := by
    --   have image : ∀ b : β, ∃ (a : α), f a = b := by
    --     intro b
    --     constructor
    --     exact h_rinv b
    --   let left_inv : β → α := by
    --     intro b
    --     have x := image b
    --     exact Classical.choose x
    --   use left_inv
    --   simp
    --   intro a

    --   have foot : ∃ ai : α, ai = a := by
    --     use a
    --   have bla := Classical.choose_spec foot


      -- have foo := λ b : β => Classical.choose_spec (image b)
      -- let lam := λ b : β => Classical.choose (image b)
      -- use lam
      -- intro a
      -- simp
      -- specialize foo (f a)


    -- have image : ∀ b : β, ∃! (a : α), f a = b := by
    --   intro b
    --   constructor
    --   constructor
    --   { simp
    --     exact h_rinv b
    --   }
    --   { simp
    --     intros a h_eq
    --     have foo := h_rinv b
    --     rw [←h_eq]
    --     -- this is just left inv proof...
    --   }

    -- have image_a₁ := image (f a₁)
    -- rcases image_a₁ with ⟨a, h_funext_generic, h_a_unique⟩ 
    -- simp at h_a_unique
    -- have a₁_eq_a := h_a_unique a₁
    -- have a₂_eq_a := h_a_unique a₂
    -- simp at a₁_eq_a
    -- specialize a₂_eq_a h_funext.symm
    -- rw [←a₁_eq_a] at a₂_eq_a
    -- exact a₂_eq_a.symm

    -- have left_inv : ∀ a : α, rinv (f a) = a := by
    --   intro a


       
    -- rcases left_inv with ⟨linv, hlinv⟩
    -- have hlinva₁ := hlinv a₁
    -- have hlinva₂ := hlinv a₂
    -- rw [funxt] at hlinva₁
    -- rw [hlinva₁] at hlinva₂
    -- exact hlinva₂

    -- have left_inv := λ b : β 
    --   => (if ex : ∃ (a : α), f a = b 
    --       then ex.choose 
    --       else (Classical.choice hvoid)) 
    -- have image : ∀ b : β, ∃ (a : α), f a = b := sorry
    -- have choice_p := λ b : β => Classical.choose_spec (image b)
    -- simp at choice_p



    -- specialize hunique rinv
    -- have foo1 := hrinv (f a₁)
    -- have foo2 := hrinv (f a₂)

    -- rcases h with
    -- | intro rinv h_inv_unique =>
    --   cases h_inv_unique with
    --   | intro hinv hunique => 
    --     dsimp at hinv
    --     dsimp at hunique






  }
  {  }
