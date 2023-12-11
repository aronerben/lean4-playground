import Mathlib.Tactic

def S (n : ℕ) := Fin n → Fin n

#check S 6

def σ : S 6 := λ x => Fin.succ x

def τ : S 3 := ![0,1,2]

def full_cycle
  {n : ℕ} (σ : S n)
  : Prop := ∀ x : Fin n, σ^[n] x = x

lemma full_cycle_sigma
  : full_cycle σ :=
by
  rw [full_cycle]
  intro x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  simp only [σ]
  simp
  ring_nf



#reduce (7 : Fin 6)
