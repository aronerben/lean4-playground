import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Data.Matrix.Basic

-- class VectorSpace
--   (K : Type u) (V : Type v)
--   [Field K] [AddCommGroup V]
--   : Type (max u v) where
--   smul : K → V → V
--   smul_assoc : ∀ (a b : K) (v : V), smul (a * b) v = smul a (smul b v)
--   one_smul : ∀ (v : V), smul 1 v = v
--   left_distrib : ∀ (a : K) (u v : V), smul a (u + v) = smul a u + smul a v
--   right_distrib : ∀ (a b : K) (v : V), smul (a + b) v = smul a v + smul b v

-- infixr:73 " • " => VectorSpace.smul

-- instance : VectorSpace ℝ ℝ where
--   smul := (·*·)
--   smul_assoc := mul_assoc
--   one_smul := one_mul
--   left_distrib := left_distrib
--   right_distrib := right_distrib


open BigOperators
-- variable
--   [Semiring R] [AddCommMonoid M] [Module R M]
--   (b : Basis ι R M)
--   (i : ι)
--   (a : R)
--   (w : M)
-- #check b.repr w
-- #check b.1 w i
-- #check b i

lemma foo'
  {R M ι : Type}
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [Fintype ι]
  (b : Basis ι R M)
  : ∀ (w : M), ∃ (a : ι → R), w = ∑ i, a i • b i :=
by
  intro w
  use b.repr w
  symm
  exact Basis.sum_repr b w


theorem Submodule.Quotient.mk_sum
  {R M ι : Type}
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  (U : Submodule R M)
  (s : Finset ι)
  {f : ι → M}
  : ((Submodule.Quotient.mk (Finset.sum s f)) : M ⧸ U)
    = Finset.sum s fun i : ι => (Submodule.Quotient.mk (f i) : M ⧸ U) := by
  change (mkQ U (Finset.sum s f)) = Finset.sum s fun i : ι => Submodule.mkQ U (f i)
  apply map_sum

lemma basis_is_spanning_set_for_quot_space
  {R M ι : Type}
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [Fintype ι]
  (U : Submodule R M)
  (b : Basis ι R M)
  (wq : M ⧸ U)
  : ∃ (a : ι → R),
      ∑ i, a i • Submodule.Quotient.mk (b i) = wq :=
by
  -- Could use rintro ⟨v⟩ to get rid of the quotient if in ∀, then not need hv
  simp_rw [←Submodule.Quotient.mk_smul]
  -- Incredible shortcut
  have ⟨v, hv⟩ := Submodule.Quotient.mk_surjective U wq
  rw [←hv]
  use b.repr v
  rw [←Submodule.Quotient.mk_sum, Basis.sum_repr b v]

def A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

def similar
  {n : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ)
  (B : Matrix (Fin n) (Fin n) ℝ)
  -- : Prop := ∃ S : GL (Fin n) ℝ, (S * A) * S⁻¹ = B
  : Prop := ∃ S : Matrix (Fin n) (Fin n) ℝ, (S * A) * S⁻¹ = B

lemma foo
  : (0 : Matrix (Fin 2) (Fin 2) ℝ) i j = 0 := by
  exact rfl

lemma A_sq_eq : A * A = 0 := by
  simp [A]
  ext i j
  change Matrix.of ![0, ![0, 0]] i j = 0
  ring_nf
  rw [Matrix.of]
  simp
  -- exact?

lemma similar_iff
  (A' : Matrix (Fin 2) (Fin 2) ℝ)
  : similar A A' ↔ A'^2 = 0 ∧ A' ≠ 0 :=
by
  constructor
  · intro hsim
    rw [similar] at hsim
    rcases hsim with ⟨S, hS⟩
    -- have bar := S.val
    -- have : Invertible S := by
    --   exact Units.invertible bar
    rw [←hS]
    constructor
    · rw [sq]
      -- have foo : S * A * S⁻¹ * (S * A * S⁻¹) = S * A * (S⁻¹ * S) * A * S⁻¹ := by
      --   simp [Matrix.mul_assoc]
      -- rw [foo]
      haveI : Invertible S := by sorry
      rw [Matrix.inv_mul_of_invertible S]
      simp only [mul_one]
      simp [A, sq]
      simp only


    · sorry
  · sorry


  -- { intro h
  --   rcases h with ⟨S, hS⟩
  --   split
  --   { rw [←hS, Matrix.mul_assoc, Matrix.mul_inv_self, Matrix.one_mul, Matrix.mul_zero] }
  --   { intro hA'
  --     rw [hA', Matrix.zero_mul] at hS
  --     exact zero_ne_one hS } }
  -- { rintro ⟨hA', hA'0⟩
  --   use !![![1, 0], ![0, 0]]
  --   rw [Matrix.mul_assoc, Matrix.mul_inv_self, Matrix.one_mul, hA', Matrix.zero_mul] }
