import HolomorphicAnosov.Ghys.AffineProjectiveStructure

/-!
Affine transition compatibility is preserved under biholomorphic transport. (Ghys, Lemma 3.2) -/

noncomputable section
open Set Filter
open scoped Topology _root_.Topology Manifold ContDiff
namespace HolomorphicAnosov.Ghys

universe u v
variable {L : Type u} {L' : Type v}
  [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
  [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']

/-- Composing two charts with the inverse of a biholomorphism preserves their affine transition
germs and their slope and translation coefficients. -/
theorem affineChartsCompatible_transport
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (c d : OpenPartialHomeomorph L ℂ)
    (h : AffineChartsCompatible L c d) :
    AffineChartsCompatible L' (T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c)
      (T.toHomeomorph.symm.toOpenPartialHomeomorph.trans d) := by
  let t := T.toHomeomorph.symm.toOpenPartialHomeomorph
  rintro x hx
  have hcx : T.symm x ∈ c.source := by
    simpa [t] using hx.1
  have hdx : T.symm x ∈ d.source := by
    simpa [t] using hx.2
  obtain ⟨a, ha⟩ := h (T.symm x) ⟨hcx, hdx⟩
  refine ⟨a, ?_⟩
  exact T.symm.continuous.tendsto x ha

end HolomorphicAnosov.Ghys
