import HolomorphicAnosov.Paper.Ghys.NativeComplexLineNormalization

namespace HolomorphicAnosov

/-! This file gives complex-linear model equivalences with `ℂ` for families of rank-one complex
vector spaces. -/

/-- Each fibre of a family of rank-one complex vector spaces admits a complex-linear equivalence
with `ℂ`. -/
theorem native_complex_line_model_equivs
    {M : Type*} [TopologicalSpace M]
    {V : ∀ _x : M, Type*}
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
    (hRank : ∀ x, Module.finrank ℂ (V x) = 1) :
    ∀ x, Nonempty (V x ≃ₗ[ℂ] ℂ) := by
  intro x
  exact exists_complex_line_equiv_of_finrank_one (V x) (hRank x)

end HolomorphicAnosov
