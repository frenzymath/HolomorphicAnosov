import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov
open Set

/-- A continuous map injective on a compact closure takes an open region's
frontier onto the frontier of its open image. Continuity and compactness
identify closure images; injectivity permits subtracting the open interiors.
Source: Cairns §4(C), transport of the contact-and-chord frontier. -/
theorem compact_closure_frontier_image (U : Set ℂ) (f : ℂ → ℂ)
    (hc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (hinj : InjOn f (closure U)) (hU : IsOpen U) (hV : IsOpen (f '' U)) :
    f '' frontier U = frontier (f '' U) := by
  rw [hU.frontier_eq,hV.frontier_eq,← image_closure_eq_of_compact_closure U f hc hf]
  exact hinj.image_sdiff_subset subset_closure

end HolomorphicAnosov

