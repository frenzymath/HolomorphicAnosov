import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- Two pairs of smooth ambient vector fields with equal local germs have equal covariant
derivatives at the marked point. (Andrews, p.74) -/
theorem covariantDerivative_extension_independent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (cov : CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (U : Opens M) (p : U)
    (X X' Y Y' : ContMDiffSection 𝓘(ℝ, E) E ∞
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (hX : ∀ᶠ q in 𝓝 p, X q.1 = X' q.1)
    (hY : ∀ᶠ q in 𝓝 p, Y q.1 = Y' q.1) :
    cov (fun q ↦ Y q) p.1 (X p.1) = cov (fun q ↦ Y' q) p.1 (X' p.1) := by
  have hY' : ∀ᶠ q in 𝓝 p.1, Y q = Y' q := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p]
    exact hY
  have hc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((Y.contMDiff p.1).mdifferentiableAt (by simp))
    ((Y'.contMDiff p.1).mdifferentiableAt (by simp))
    Filter.univ_mem hY'
  rw [hc, Filter.EventuallyEq.eq_of_nhds hX]


end
end HolomorphicAnosov
