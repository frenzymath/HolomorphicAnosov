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


namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- If a complex-linear scalar map vanishes on the real summand `U` and is injective on its
complement `S`, its complex kernel corresponds to `U` under `complexTangentToReal`. -/
theorem originalRealKernelIdentification {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X)
    (S U : Submodule ℝ (TangentSpace (realModel d) x)) (hSU : IsCompl S U)
    (L : TangentSpace (complexModel d) x →ₗ[ℂ] ℂ)
    (hU : ∀ v ∈ U, L ((complexTangentToReal d x).symm v) = 0)
    (hS : ∀ v ∈ S, L ((complexTangentToReal d x).symm v) = 0 → v = 0) :
    ((LinearMap.ker L).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = U := by
  apply le_antisymm
  · rintro v ⟨z, hz, rfl⟩
    have hv : complexTangentToReal d x z ∈ S ⊔ U := by
      rw [hSU.sup_eq_top]
      trivial
    obtain ⟨s, hs, u, hu, hsum⟩ := Submodule.mem_sup.mp hv
    have heq : L ((complexTangentToReal d x).symm s) +
        L ((complexTangentToReal d x).symm u) = 0 := by
      rw [← map_add, ← map_add, hsum, ContinuousLinearEquiv.symm_apply_apply]
      exact hz
    have hs0 := hS s hs (by simpa [hU u hu] using heq)
    rw [hs0, zero_add] at hsum
    exact hsum ▸ hu
  · intro v hv
    exact ⟨(complexTangentToReal d x).symm v, hU v hv,
      (complexTangentToReal d x).apply_symm_apply v⟩



end HolomorphicAnosov
