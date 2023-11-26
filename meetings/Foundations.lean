import Mathlib.Tactic
import Mathlib.Tactic.Basic

lemma distrib 
  {p : Prop} {q : Prop} {R : Prop} 
  : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=   
by
  tauto

lemma not_and_iff_or_not
  {p : Prop} {q : Prop} {r : Prop} 
  : ¬(p ∧ q) ↔ ¬p ∨ ¬q  :=   
by
  constructor
  { intro hnand
    by_cases p 
    { exact Or.inr λ hq => hnand ⟨h, hq⟩}
    { left
      exact h
    }
  }
  { 
    intros hnor hand
    rcases hand with ⟨hp, hq⟩  
    cases hnor with
      | inl hnp => exact hnp hp
      | inr hnq => exact hnq hq
  }

lemma not_or_iff_and_not
  {p : Prop} {q : Prop} {r : Prop} 
  : ¬(p ∨ q) ↔ ¬p ∧ ¬q  :=   
by
  constructor
  { intro hnor
    constructor
    { intro hp
      exact hnor (Or.inl hp)
    }
    { intro hq
      exact hnor (Or.inr hq)
    }
  }
  { 
    intros hnand hor
    rcases hnand with ⟨hnp, hnq⟩  
    cases hor with
      | inl hp => exact hnp hp
      | inr hq => exact hnq hq
  }