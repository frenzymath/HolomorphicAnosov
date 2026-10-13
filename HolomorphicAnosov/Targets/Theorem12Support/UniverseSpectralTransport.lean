import HolomorphicAnosov.Targets.Theorem12Support.UniverseSpectralTransport.hasEigenvalue_of_intertwining
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Conjugation by a real continuous linear equivalence preserves the eigenvalues of the
complexified operator. In particular, it preserves exclusion of eigenvalues of modulus one.
(Zhang, Theorem 1.2) -/

noncomputable section
open TensorProduct

universe u v

namespace HolomorphicAnosov.Theorem12UniverseSpectralScratch

variable {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W]

/-- The complex scalar extension of `e` intertwines the complexifications of `R` and `e ∘ R ∘ e⁻¹`. -/
theorem conjugate_baseChange_intertwines (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V)
    (z : ℂ ⊗[ℝ] V) :
    e.toLinearEquiv.baseChange ℝ ℂ V W (R.toLinearMap.baseChange ℂ z) =
      ((e.symm.trans R).trans e).toLinearMap.baseChange ℂ
        (e.toLinearEquiv.baseChange ℝ ℂ V W z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul]
    congr 1
    exact (congrArg e (congrArg R (e.symm_apply_apply x))).symm
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The complexifications of `R` and its real conjugate have the same eigenvalues. -/
theorem hasEigenvalue_conjugate_baseChange_iff
    (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V) (μ : ℂ) :
    Module.End.HasEigenvalue (((e.symm.trans R).trans e).toLinearMap.baseChange ℂ) μ ↔
      Module.End.HasEigenvalue (R.toLinearMap.baseChange ℂ) μ := by
  let E := e.toLinearEquiv.baseChange ℝ ℂ V W
  let f := R.toLinearMap.baseChange ℂ
  let g := ((e.symm.trans R).trans e).toLinearMap.baseChange ℂ
  have hfg : ∀ x, E (f x) = g (E x) := conjugate_baseChange_intertwines e R
  constructor
  · apply hasEigenvalue_of_intertwining E.symm g f
    intro y
    apply E.injective
    rw [E.apply_symm_apply, hfg, E.apply_symm_apply]
  · exact hasEigenvalue_of_intertwining E f g hfg μ

/-- If the complexification of `R` has no eigenvalue of modulus one, the complexification of its
real conjugate has the same property. -/
theorem hyperbolic_conjugate_baseChange
    (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue (R.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    ∀ μ : ℂ,
      Module.End.HasEigenvalue (((e.symm.trans R).trans e).toLinearMap.baseChange ℂ) μ →
        ‖μ‖ ≠ 1 := by
  intro μ hμ
  exact hhyper μ ((hasEigenvalue_conjugate_baseChange_iff e R μ).mp hμ)


end HolomorphicAnosov.Theorem12UniverseSpectralScratch
