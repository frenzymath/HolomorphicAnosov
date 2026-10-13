import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.RawChartedSpaceCompTransition

noncomputable section
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- A scalar complex manifold structure on a curve induces the corresponding one-coordinate
product-model manifold structure. (Ghys, Lemma 3.3, p.593) -/
theorem curve_scalar_is_manifold_complex
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    [IsManifold 𝓘(ℂ) ∞ L] :
    IsManifold (complexModel 1) ∞ L := by
  apply isManifold_of_contDiffOn (complexModel 1) ∞ L
  intro e e' he he'
  exact raw_chartedSpace_comp_transition
    e e' he he'

end HolomorphicAnosov.Ghys
