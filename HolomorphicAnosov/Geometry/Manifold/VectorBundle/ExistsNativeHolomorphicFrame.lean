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

/-- The complex tangent bundle has a holomorphic frame on a neighbourhood of each point (Demailly,
II (3.4)–(3.5), p.85). -/
theorem existsNativeHolomorphicFrame {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (x : X) :
    ∃ (W : Set X) (s : Fin d → (y : X) → TangentSpace (complexModel d) y),
      IsOpen W ∧ x ∈ W ∧
      (∀ i, ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, s i y⟩ : TangentBundle (complexModel d) X)) W) ∧
      ∀ y ∈ W, ∃ b : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) y),
        ∀ i, b i = s i y := by
  classical
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let b := Pi.basisFun ℂ (Fin d)
  refine ⟨e.baseSet, fun i y ↦ e.symm y (b i), e.open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt' x, ?_, ?_⟩
  · intro i
    apply e.contMDiffOn_section_baseSet_iff.mpr
    apply (contMDiffOn_const (c := b i)).congr
    intro y hy
    simp [hy]
  · intro y hy
    refine ⟨b.map (e.linearEquivAt ℂ y hy).symm, ?_⟩
    intro i
    rfl



end HolomorphicAnosov
