import HolomorphicAnosov.Ghys.AffineCompleteDevelopingContinuation
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.CurveScalarIsManifoldComplex

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace


theorem affine_completeness_local_development_bridge
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L] [T2Space L] [SecondCountableTopology L]
    [ConnectedSpace L] [SimplyConnectedSpace L]
    (A : ComplexAffineAtlas L) :
    ∃ D : L → ℂ,
      ∀ c ∈ A.charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y) := by
  obtain ⟨⟨D, hD, _hSmooth, _hLocal⟩, _hUnique⟩ :=
    affine_complete_developing_continuation L A
  exact ⟨D, hD⟩

end HolomorphicAnosov.Ghys
