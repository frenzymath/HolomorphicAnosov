import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.PolygonEndpointIntersectionImage

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-!
Named assembly provider for the initial Cairns data.  The source construction
supplies opposite gap bookkeeping and first-contact `StarChoice` witnesses;
this helper packages those witnesses into the `InitialData` structure consumed
by the initial-stage theorem.
-/
theorem cairns_initial_star_choice_assembly
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (g₁ g₂ : CairnsCircleGap)
    (hp₁ : g₁.first = p) (hq₁ : g₁.last = q)
    (_hp₂ : g₂.first = q) (_hq₂ : g₂.last = p)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (s₁ : StarChoice σ a g₁) (s₂ : StarChoice σ a g₂) :
    ∃ d : InitialData σ a p q,
      d.firstGap.first = p ∧ d.firstGap.last = q := by
  let d : InitialData σ a p q :=
    { firstGap := g₁
      first_eq := hp₁
      last_eq := hq₁
      secondGap := g₂
      second_start := hstart
      second_stop := hstop
      firstStar := s₁
      secondStar := s₂ }
  refine ⟨d, ?_⟩
  exact ⟨d.first_eq, d.last_eq⟩

end HolomorphicAnosov.Topology.Plane
