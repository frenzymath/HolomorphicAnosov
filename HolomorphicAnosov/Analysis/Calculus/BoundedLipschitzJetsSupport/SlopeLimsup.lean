import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.JetClassEquality

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
/-- The infimum definition agrees with the literal real limsup when the
punctured filter is nonbottom, HPS p. 27. On that filter x is eventually nonzero,
so multiplying/dividing by its positive norm equates the upper-bound sets.
Boundedness makes that set nonempty, while nonnegativity of the ratio makes
every eventual upper bound nonnegative. Thus the two infima are identical.
The zero-domain case is deliberately handled by the preceding definition. -/
theorem representativeSlope_eq_limsup
    [NeBot (𝓝[≠] (0 : X))] (q : BoundedRepresentative X Y) :
    representativeSlope X Y q =
      Filter.limsup (fun x : X => ‖(q : X → Y) x‖ / ‖x‖) (𝓝[≠] (0 : X)) := by
  rw [representativeSlope, Filter.limsup_eq]
  congr 1
  ext C
  change (0 ≤ C ∧ ∀ᶠ x in 𝓝[≠] (0 : X), ‖(q : X → Y) x‖ ≤ C * ‖x‖) ↔
    ∀ᶠ x in 𝓝[≠] (0 : X), ‖(q : X → Y) x‖ / ‖x‖ ≤ C
  have hne : ∀ᶠ x in 𝓝[≠] (0 : X), x ≠ 0 := self_mem_nhdsWithin
  constructor
  · rintro ⟨_, hC⟩
    filter_upwards [hC, hne] with x hx hx0
    exact (div_le_iff₀ (norm_pos_iff.mpr hx0)).mpr hx
  · intro hC
    obtain ⟨x, hx⟩ := hC.exists
    refine ⟨(div_nonneg (norm_nonneg _) (norm_nonneg _)).trans hx, ?_⟩
    filter_upwards [hC, hne] with x hx hx0
    exact (div_le_iff₀ (norm_pos_iff.mpr hx0)).mp hx


end HolomorphicAnosov.BoundedLipschitzJets

