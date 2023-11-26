import Mathlib.Tactic

open BigOperators

open Submodule Quotient Set

lemma basis_is_spanning_set_for_quot_space
    {R M ι : Type}
    [Ring R]
    [AddCommGroup M]
    [Module R M]
    [Fintype ι]
    (U : Submodule R M)
    (b : Basis ι R M)
    (wq : M ⧸ U) : ∃ (a : ι → R),
    ∑ i, a i • Submodule.Quotient.mk (b i) = wq := by
  have : span R (range (mkQ U ∘ b : ι → M ⧸ U)) = ⊤  := by
    rw [range_comp, span_image, b.span_eq, Submodule.map_top, range_mkQ]
  exact (mem_span_range_iff_exists_fun R).mp (eq_top_iff'.mp this wq)

example [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (b : Basis ι R M) (U : Submodule R M) : ∀ x : M ⧸ U, ∃ (a : ι →₀ R), ∑ i, a i • Submodule.Quotient.mk (b i) = x := by
  rintro ⟨v⟩
  use b.repr v
  change ∑ i, Submodule.mkQ U (b.repr v i • b i) = Submodule.mkQ U v
  rw [← map_sum, Basis.sum_repr]

example [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (b : Basis ι R M) (U : Submodule R M) : ∀ x : M ⧸ U, ∃ (a : ι →₀ R), ∑ i, a i • Submodule.Quotient.mk (b i) = x := by
  intro x
  have ⟨v, hv⟩ := Submodule.mkQ_surjective U x
  use b.repr v
  simp_rw [← Submodule.mkQ_apply, ← map_smul, ← map_sum, Basis.sum_repr]
  exact hv
