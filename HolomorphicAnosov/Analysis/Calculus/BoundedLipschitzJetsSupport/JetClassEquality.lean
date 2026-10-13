import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The quotient identifies exactly the source's little-o differences.
This is the defining submodule-quotient equality, not an extra analytic assumption. -/
theorem jetClass_eq_iff (q r : BoundedRepresentative X Y) :
    jetClass X Y q = jetClass X Y r ↔
      IsLittleORepresentative X Y ((q : X → Y) - (r : X → Y)) :=
  Submodule.Quotient.eq (littleORepresentatives X Y)

/-- Nonnegative eventual upper bounds for the normalized slope, HPS p. 27. -/
def slopeBounds (q : X → Y) : Set ℝ :=
  {C | 0 ≤ C ∧ ∀ᶠ x in 𝓝[≠] (0 : X), ‖q x‖ ≤ C * ‖x‖}

/-- Concrete finite normalized-slope limsup on bounded representatives, HPS p. 27.
The nonnegative-bound convention gives slope zero when X is the zero space. -/
def representativeSlope (q : BoundedRepresentative X Y) : ℝ :=
  sInf (slopeBounds X Y q)


end HolomorphicAnosov.BoundedLipschitzJets

