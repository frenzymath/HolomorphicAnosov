import HolomorphicAnosov.Topology.HalfSectorRadialNormalization

namespace HolomorphicAnosov

open Set

/-!
This is the elementary first reduction in Cairns §3 (pp.862--863): an
initial segment of the perpendicular ray supplied by the entrance hypothesis
is contained in the selected complementary sector.  It is split from the
larger front theorem so that the component argument can be reused independently.
-/
theorem halfSectorConvexFront_ray_tail_subset
    (D1 D2 P : ℂ) (β : Set ℂ) (ε : ℝ)
    (_hεpos : 0 < ε) (_hεle : ε ≤ 1)
    (hεray : ∀ t ∈ Set.Ioo (0 : ℝ) ε,
      (D1 + D2) / 2 + t • (P - (D1 + D2) / 2) ∈ β) :
    {z : ℂ | ∃ t : ℝ, 0 < t ∧ t < ε ∧
      z = (D1 + D2) / 2 + t • (P - (D1 + D2) / 2)} ⊆ β := by
  intro z hz
  rcases hz with ⟨t, ht0, htε, rfl⟩
  exact hεray t ⟨ht0, htε⟩

end HolomorphicAnosov
