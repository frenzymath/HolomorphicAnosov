import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic

/-! An intertwining complex linear equivalence transports eigenvalues between operators. (Zhang,
Theorem 1.2, §3, p. 11) -/

universe u v
namespace HolomorphicAnosov.Theorem12UniverseSpectralScratch

/-- If a complex linear equivalence intertwines `f` and `g`, every eigenvalue of `f` is an
eigenvalue of `g`. -/
theorem hasEigenvalue_of_intertwining
    {P : Type u} {Q : Type v} [AddCommGroup P] [AddCommGroup Q]
    [Module ℂ P] [Module ℂ Q]
    (E : P ≃ₗ[ℂ] Q) (f : P →ₗ[ℂ] P) (g : Q →ₗ[ℂ] Q)
    (hintertwine : ∀ x, E (f x) = g (E x)) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue f μ) : Module.End.HasEigenvalue g μ := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := E x)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · rw [← hintertwine, hx.apply_eq_smul]
    exact E.map_smul μ x
  · intro heq
    exact hx.2 (E.injective (heq.trans (map_zero E).symm))

end HolomorphicAnosov.Theorem12UniverseSpectralScratch
