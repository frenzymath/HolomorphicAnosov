import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Visible
import Mathlib.Topology.Compactness.Compact

open Set

namespace HolomorphicAnosov

/-- A visible point of a compact set, viewed from outside, lies on the set's
frontier. This is the elementary first half of Cairns's Case II boundary
identification (1951, §3 p.863): an interior point cannot be visible because a
shorter point on its viewing ray remains in the set. -/
theorem halfSector_visible_mem_frontier
    {K : Set ℂ} {M Q : ℂ} (hK : IsCompact K) (hM : M ∉ K)
    (hQ : Q ∈ K) (hvis : IsVisible ℝ K M Q) : Q ∈ frontier K := by
  have hnotint : Q ∉ interior K := by
    intro hQi
    have hEq : M = Q := hvis.eq_of_mem_interior hQi
    exact hM (hEq ▸ hQ)
  rw [hK.isClosed.frontier_eq]
  exact ⟨hQ, hnotint⟩

end HolomorphicAnosov

