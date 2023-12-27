import Mathlib.Tactic

-- TODO use ℕ+
def S (n : ℕ) := Fin n → Fin n

#check S 6

def σ : S 6 := λ x => Fin.succ x

def τ : S 3 := ![0,1,2]

def full_cycle
  {n : ℕ} (σ : S n)
  : Prop := ∀ x : Fin n, σ^[n - 1] x = x

#reduce σ^[5] 1

lemma full_cycle_sigma
  : full_cycle σ :=
by
  rw [full_cycle]
  intro x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  simp only [σ]
  aesop
  repeat rw [@Fin.val_succ]
  simp only [Fin.coe_ofNat_eq_mod]
  simp
  -- simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.cast_add, Nat.cast_one]
  -- rw?
  ring_nf
  exact rfl



#reduce (7 : Fin 6)
