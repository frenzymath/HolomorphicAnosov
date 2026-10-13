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

import HolomorphicAnosov.Geometry.Manifold.VectorBundle.LocalHolomorphicSubmersionKernel

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- A family of tangent subspaces locally equal to the differential kernels of holomorphic scalar
submersions is a rank-`n` holomorphic tangent subbundle (Demailly, II Prop. 3.6, p.86). -/
theorem holomorphicSubbundleOfLocalSubmersions {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (n + 1)) X]
    [IsManifold (complexModel (n + 1)) ∞ X]
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel (n + 1)) x))
    (h : ∀ x : X, ∃ (U : Set X) (q : X → ℂ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q U ∧
      mfderiv (complexModel (n + 1)) 𝓘(ℂ) q x ≠ 0 ∧
      ∀ y ∈ U, LinearMap.ker (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap = P y) :
    IsHolomorphicTangentSubbundle n P := by
  intro x
  obtain ⟨U, q, hU, hx, hq, hqx, hk⟩ := h x
  obtain ⟨W, s, hxW, hWU, hs, hspan⟩ := localHolomorphicSubmersionKernel hU hq hx hqx
  exact ⟨W, s, hxW, hs, fun y hy ↦ (hspan y hy).trans (hk y (hWU hy))⟩



end HolomorphicAnosov
