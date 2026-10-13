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

import HolomorphicAnosov.Linear.RankOneKernelFrame
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicDirectionalDerivative

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- A holomorphic tangent frame with a nowhere-zero directional derivative in one component
determines a holomorphic frame spanning the kernel of the scalar differential (Demailly, II
Prop. 3.6, p.86). -/
theorem holomorphicKernelFrameOn {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (n + 1)) X]
    [IsManifold (complexModel (n + 1)) ∞ X]
    {U : Set X} (hU : IsOpen U) {q : X → ℂ}
    (hq : ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ q U)
    (e : Fin (n + 1) → (y : X) → TangentSpace (complexModel (n + 1)) y)
    (he : ∀ i, ContMDiffOn (complexModel (n + 1)) (complexModel (n + 1)).tangent ∞
      (fun y ↦ (⟨y, e i y⟩ : TangentBundle (complexModel (n + 1)) X)) U)
    (hb : ∀ y ∈ U, ∃ b : Module.Basis (Fin (n + 1)) ℂ
      (TangentSpace (complexModel (n + 1)) y), ∀ i, b i = e i y)
    (j : Fin (n + 1))
    (hj : ∀ y ∈ U, mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y (e j y) ≠ 0) :
    ∃ s : Fin n → (y : X) → TangentSpace (complexModel (n + 1)) y,
      IsHolomorphicTangentFrame U s ∧ ∀ y ∈ U,
        Submodule.span ℂ (Set.range (fun i ↦ s i y)) =
          LinearMap.ker (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap := by
  classical
  let L := fun y ↦ (tangentSpaceCastModel 𝓘(ℂ) (q y)).toLinearEquiv.toLinearMap.comp
    (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap
  let a : Fin (n + 1) → X → ℂ := fun i y ↦ L y (e i y)
  have ha : ∀ i, ContMDiffOn (complexModel (n + 1)) 𝓘(ℂ) ∞ (a i) U := by
    intro i
    exact holomorphicDirectionalDerivative hU hq _ (he i)
  have hja : ∀ y ∈ U, a j y ≠ 0 := by
    intro y hy
    exact fun h ↦ hj y hy ((tangentSpaceCastModel 𝓘(ℂ) (q y)).map_eq_zero_iff.mp h)
  have hker : ∀ y, LinearMap.ker (L y) =
      LinearMap.ker (mfderiv (complexModel (n + 1)) 𝓘(ℂ) q y).toLinearMap := by
    intro y
    ext v
    exact (tangentSpaceCastModel 𝓘(ℂ) (q y)).map_eq_zero_iff
  let v := fun (i : {i : Fin (n + 1) // i ≠ j}) y ↦
    e i.val y - (a i.val y / a j y) • e j y
  let t := finSuccAboveEquiv j
  refine ⟨fun i y ↦ v (t i) y, ⟨hU, ?_, ?_⟩, ?_⟩
  · intro i
    exact (he (t i).val).sub_section
      (((ha (t i).val).div₀ (ha j) hja).smul_section (he j))
  · intro y hy
    obtain ⟨b, hb⟩ := hb y hy
    have hk := rankOneKernelFrame b (L y) j (by simpa only [hb] using hja y hy)
    have hv : LinearIndependent ℂ (fun i ↦ v i y) := by simpa only [v, a, hb, ContinuousLinearMap.coe_coe] using hk.1
    exact hv.comp t t.injective
  · intro y hy
    obtain ⟨b, hb⟩ := hb y hy
    have hk := rankOneKernelFrame b (L y) j (by simpa only [hb] using hja y hy)
    have hr : Set.range (fun i ↦ v (t i) y) = Set.range (fun i ↦ v i y) :=
      by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨t i, rfl⟩
        · rintro ⟨i, rfl⟩
          obtain ⟨k, rfl⟩ := t.surjective i
          exact ⟨k, rfl⟩
    rw [hr]
    rw [← hker y]
    simpa only [v, a, hb] using hk.2



end HolomorphicAnosov
