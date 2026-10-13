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

/-- The directional derivative of a holomorphic scalar function along a holomorphic tangent section
is holomorphic on their open domain (Demailly, II §3.6, p.86). -/
theorem holomorphicDirectionalDerivative {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : Set X} (hU : IsOpen U) {q : X → ℂ}
    (hq : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q U)
    (s : (y : X) → TangentSpace (complexModel d) y)
    (hs : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, s y⟩ : TangentBundle (complexModel d) X)) U) :
    ContMDiffOn (complexModel d) 𝓘(ℂ) ∞
      (fun y ↦ mfderiv (complexModel d) 𝓘(ℂ) q y (s y)) U := by
  have ht := hq.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hc := ht.comp hs (fun y hy ↦ hy)
  have hp := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ)).comp_contMDiffOn hc
  apply hp.congr
  intro y hy
  change mfderiv (complexModel d) 𝓘(ℂ) q y (s y) =
    mfderivWithin (complexModel d) 𝓘(ℂ) q U y (s y)
  exact congrArg (fun L ↦ L (s y))
    (mfderivWithin_of_isOpen (I := complexModel d) (I' := 𝓘(ℂ)) (f := q) hU hy).symm



end HolomorphicAnosov
