import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableRange

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- HPS Theorem (3.3), p.29: every differentiable jet is represented by a bounded linear operator. The range identity supplies the operator and equality of underlying values gives equality in the subtype. -/
theorem linearJetSubtype_surjective :
    Function.Surjective (linearJetSubtype X Y) := by
  intro j
  have hj : (j : BoundedJet X Y) ∈ LinearMap.range (linearJet X Y) := by
    rw [← differentiableJets_eq_linearJet_range X Y]
    exact j.property
  rcases hj with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  apply Subtype.ext
  exact hL


end HolomorphicAnosov.BoundedLipschitzJets

