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

import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicSubbundleOfLocalSubmersions
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.OriginalRealKernelIdentification

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- Local holomorphic scalar submersions whose differentials annihilate the unstable
fibres and are injective on the stable fibres define a rank-`n` holomorphic tangent subbundle
whose realification is the unstable distribution. (Demailly, II, Prop. 3.6, p.86) -/
theorem originalUnstableHolomorphicOfLocalSubmersions {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (n + 1)) X]
    [IsManifold (complexModel (n + 1)) ∞ X]
    (f : Biholomorph (n + 1) (n + 1) X X) (a : AnosovDatum f)
    (h : ∀ x : X, ∃ (W : Set X) (q : X → ℂ), IsOpen W ∧ x ∈ W ∧
      ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q W ∧
      mfderiv (complexModel (n + 1)) 𝓘(ℂ) q x ≠ 0 ∧
      ∀ y ∈ W,
        (∀ v ∈ a.splitting.unstable.toDistribution y,
          mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y
            ((complexTangentToReal (n + 1) y).symm v) = 0) ∧
        (∀ v ∈ a.splitting.stable.toDistribution y,
          mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y
            ((complexTangentToReal (n + 1) y).symm v) = 0 → v = 0)) :
    ∃ P : (x : X) → Submodule ℂ (TangentSpace (complexModel (n + 1)) x),
      IsHolomorphicTangentSubbundle n P ∧
      ∀ x, ((P x).restrictScalars ℝ).map
        (complexTangentToReal (n + 1) x).toLinearEquiv.toLinearMap =
          a.splitting.unstable.toDistribution x := by
  classical
  choose W q hW hx hq hn hsplit using h
  let K := fun x y ↦ LinearMap.ker
    (mfderiv (complexModel (n + 1)) 𝓘(ℂ) (q x) y).toLinearMap
  have hreal : ∀ x y, y ∈ W x → ((K x y).restrictScalars ℝ).map
      (complexTangentToReal (n + 1) y).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution y := by
    intro x y hy
    let L := (tangentSpaceCastModel 𝓘(ℂ) (q x y)).toLinearEquiv.toLinearMap.comp
      (mfderiv (complexModel (n + 1)) 𝓘(ℂ) (q x) y).toLinearMap
    have hk : LinearMap.ker L = K x y := by
      ext v
      exact (tangentSpaceCastModel 𝓘(ℂ) (q x y)).map_eq_zero_iff
    rw [← hk]
    apply originalRealKernelIdentification y _ _ (a.splitting.isCompl y) L
    · intro v hv
      exact (tangentSpaceCastModel 𝓘(ℂ) (q x y)).map_eq_zero_iff.mpr
        ((hsplit x y hy).1 v hv)
    · intro v hv hz
      exact (hsplit x y hy).2 v hv
        ((tangentSpaceCastModel 𝓘(ℂ) (q x y)).map_eq_zero_iff.mp hz)
  refine ⟨fun x ↦ K x x, ?_, fun x ↦ hreal x x (hx x)⟩
  apply holomorphicSubbundleOfLocalSubmersions
  intro x
  refine ⟨W x, q x, hW x, hx x, hq x, hn x, ?_⟩
  intro y hy
  apply Submodule.restrictScalars_injective ℝ ℂ
  apply Submodule.map_injective_of_injective (complexTangentToReal (n + 1) y).injective
  exact (hreal x y hy).trans (hreal y y (hx y)).symm



end HolomorphicAnosov
