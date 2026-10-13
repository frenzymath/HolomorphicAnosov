import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle

import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicDirectionalDerivative
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicKernelFrameOn
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ExistsNativeHolomorphicFrame

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- A holomorphic scalar function with nonzero differential at a point admits a holomorphic frame
spanning its differential kernel on an open neighbourhood of that point (Demailly, II Prop. 3.6,
p.86). -/
theorem localHolomorphicSubmersionKernel {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (n + 1)) X]
    [IsManifold (complexModel (n + 1)) ∞ X]
    {U : Set X} (hU : IsOpen U) {q : X → ℂ}
    (hq : ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q U)
    {x : X} (hx : x ∈ U) (hqx : mfderiv (complexModel (n + 1)) 𝓘(ℂ) q x ≠ 0) :
    ∃ (W : Set X) (s : Fin n → (y : X) → TangentSpace (complexModel (n + 1)) y),
      x ∈ W ∧ W ⊆ U ∧ IsHolomorphicTangentFrame W s ∧ ∀ y ∈ W,
        Submodule.span ℂ (Set.range (fun i ↦ s i y)) =
          LinearMap.ker (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap := by
  classical
  obtain ⟨V, e, hV, hxV, he, hb⟩ := existsNativeHolomorphicFrame (d := n + 1) x
  obtain ⟨b, hb0⟩ := hb x hxV
  obtain ⟨j, hj⟩ : ∃ j, mfderiv (complexModel (n + 1)) 𝓘(ℂ) q x (e j x) ≠ 0 := by
    by_contra! H
    apply hqx
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simpa only [hb0, ContinuousLinearMap.coe_coe, zero_apply,
      LinearMap.zero_apply] using H j
  let a : X → ℂ := fun y ↦ mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y (e j y)
  have ha := holomorphicDirectionalDerivative (hU.inter hV)
    (hq.mono Set.inter_subset_left) _ ((he j).mono Set.inter_subset_right)
  have haj : a x ≠ 0 := hj
  have haev : ∀ᶠ y in nhds x, a y ≠ 0 :=
    (ha.continuousOn.continuousAt ((hU.inter hV).mem_nhds ⟨hx, hxV⟩)).eventually_ne haj
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem ((hU.inter hV).mem_nhds ⟨hx, hxV⟩) haev)
  have hWU : W ⊆ U := fun y hy ↦ (hWsub hy).1.1
  have hWV : W ⊆ V := fun y hy ↦ (hWsub hy).1.2
  obtain ⟨s, hs, hspan⟩ := holomorphicKernelFrameOn hWopen (hq.mono hWU) e
    (fun i ↦ (he i).mono hWV) (fun y hy ↦ hb y (hWV hy)) j
    (fun y hy ↦ (hWsub hy).2)
  exact ⟨W, s, hxW, hWU, hs, hspan⟩



end HolomorphicAnosov
