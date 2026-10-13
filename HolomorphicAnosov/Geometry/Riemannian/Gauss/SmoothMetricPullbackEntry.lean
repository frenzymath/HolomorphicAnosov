import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! The entries of a smooth pullback Riemannian metric are smooth. -/

open Set Bundle IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- The metric pairing of the differential images of two fixed coordinate vectors is smooth on the
open domain of a smooth map. (Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews, §10.1 and
Prop. 10.3.1, pp.95–98) -/
theorem gauss_smooth_metric_pullback_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {s : Set E} (hs : IsOpen s) (ψ : E → M)
    (hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ s) (v w : E) :
    ContDiffOn ℝ ∞ (fun z ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z w)) s := by
  have hv (a : E) : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ (⟨ψ z, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z a⟩ :
        TangentBundle 𝓘(ℝ, E) M)) s := by
    have ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun z : E ↦ (⟨z, a⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
      intro z
      exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    have ht := hψ.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      hs.uniqueMDiffOn
    have hc := ht.comp ha.contMDiffOn (fun z hz ↦ hz)
    apply hc.congr
    intro z hz
    simp only [tangentMapWithin, Function.comp_apply]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hz)]
  rw [← contMDiffOn_iff_contDiffOn]
  have h := (g.contMDiff.comp_contMDiffOn hψ).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) (hv v) (hv w)
  intro z hz
  simpa using (contMDiffWithinAt_totalSpace.mp (h z hz)).2

end HolomorphicAnosov
