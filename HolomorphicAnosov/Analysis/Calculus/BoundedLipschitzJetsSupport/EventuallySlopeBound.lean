import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.JetClassEquality

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology
variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


omit [NormedSpace ℝ X] in
/-- A strict upper bound on the slope infimum is an eventual slope bound. HPS (3.3), p.28 uses this implication to select small radii. Choose an element of the nonempty bound set below C and enlarge that bound to C. -/
theorem eventually_slope_le (q : BoundedRepresentative X Y) {C : ℝ}
    (hC : representativeSlope X Y q < C) :
    ∀ᶠ x in 𝓝[≠] (0 : X), ‖(q : X → Y) x‖ ≤ C * ‖x‖ := by
  have hn : (slopeBounds X Y q).Nonempty := by
    obtain ⟨_, D, hD, hq⟩ := q.property
    exact ⟨D, hD, hq⟩
  obtain ⟨D, hD, hDC⟩ := exists_lt_of_csInf_lt hn hC
  filter_upwards [hD.2] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right hDC.le (norm_nonneg x))

end HolomorphicAnosov.BoundedLipschitzJets

