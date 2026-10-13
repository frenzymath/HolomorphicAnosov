import HolomorphicAnosov.Topology.CompactLocalStrictBound

noncomputable section
open Filter Set
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Two real-valued local eventual bounds on a compact space share one strict positive bound. -/
theorem compact_common_local_strict_bound (b c : X → ℝ)
    (hb : ∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x, b y ≤ q)
    (hc : ∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x, c y ≤ q) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      (∀ x, b x ≤ theta) ∧ (∀ x, c x ≤ theta) := by
  obtain ⟨theta, hpos, hlt, hbound⟩ := compact_local_strict_bound (fun x ↦ max (b x) (c x))
    (fun x ↦ by
      obtain ⟨q, hq, hbx⟩ := hb x
      obtain ⟨r, hr, hcx⟩ := hc x
      refine ⟨max q r, max_lt hq hr, ?_⟩
      filter_upwards [hbx, hcx] with y hyb hyc
      exact max_le_max hyb hyc)
  exact ⟨theta, hpos, hlt, fun x ↦ (le_max_left _ _).trans (hbound x),
    fun x ↦ (le_max_right _ _).trans (hbound x)⟩

end HolomorphicAnosov
