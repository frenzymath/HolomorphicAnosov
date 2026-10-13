import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Tangency survives the point-preserving smooth carrier transport. -/
theorem carrier_tangent_image_g15 {r : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (ι : L → M) (hι : ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ ι) (S : Set M)
    [TopologicalSpace S] [ChartedSpace (Fin r → ℝ) S]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ S]
    (e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) L S ∞)
    (he : ∀ z : L, (e z).val = ι z) (P : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (hP : ∀ z : L, LinearMap.range
      (mfderiv 𝓘(ℝ, Fin r → ℝ) I ι z).toLinearMap = P (ι z)) :
    ContMDiff 𝓘(ℝ, Fin r → ℝ) I ∞ (Subtype.val : S → M) ∧
      ∀ z : S, LinearMap.range
        (mfderiv 𝓘(ℝ, Fin r → ℝ) I (Subtype.val : S → M) z).toLinearMap = P z.val := by
  have hpoint (z : S) : ι (e.symm z) = z.val := by
    simpa using (he (e.symm z)).symm
  have hfun : (Subtype.val : S → M) = ι ∘ e.symm := funext (fun z ↦ (hpoint z).symm)
  constructor
  · rw [hfun]
    exact hι.comp e.symm.contMDiff
  · intro z
    rw [hfun, mfderiv_comp z (hι.mdifferentiable (by simp)).mdifferentiableAt
      (e.symm.contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
    change LinearMap.range ((mfderiv 𝓘(ℝ, Fin r → ℝ) I ι (e.symm z)).toLinearMap.comp
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) e.symm z).toLinearMap) = _
    have hs : Function.Surjective
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) e.symm z) := by
      exact (e.symm.mfderivToContinuousLinearEquiv (by simp) z).surjective
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs), hP]
    rfl


end HolomorphicAnosov
