import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Basic

/-!
# Angular gaps in Cairns's parameter circle

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§4(C), printed pp.864–865, the complementary arcs of the retained contact sets
and the maximal arc in the proof of Lemma 4.1. Angles are real lifts in radians;
division by `2 * Real.pi` gives the normalized length in the original parameter
circle, independently of the embedded curve and of its prescribed target map.
These are concrete definitions, with no existence or shrinking assertion.
-/

namespace HolomorphicAnosov.Topology.Plane

open Set

/-- A proper oriented circular arc, represented by an angular interval shorter
than one full turn. Cairns §4(C), pp.864–865, uses these arcs between contacts.
Representatives differing by a full turn describe the same geometric arc. -/
structure CairnsCircleGap where
  start : ℝ
  stop : ℝ
  start_lt_stop : start < stop
  shorter_than_turn : stop - start < 2 * Real.pi

namespace CairnsCircleGap

/-- The actual open parameter arc, using Mathlib's native unit circle topology. -/
def openArc (g : CairnsCircleGap) : Set Circle := Circle.exp '' Ioo g.start g.stop

/-- The associated closed parameter arc, including its two endpoints. -/
def closedArc (g : CairnsCircleGap) : Set Circle := Circle.exp '' Icc g.start g.stop

/-- The initial endpoint in Cairns's original parameter circle. -/
noncomputable def first (g : CairnsCircleGap) : Circle := Circle.exp g.start

/-- The terminal endpoint in Cairns's original parameter circle. -/
noncomputable def last (g : CairnsCircleGap) : Circle := Circle.exp g.stop

/-- Its affine angular parametrization on the closed unit interval. -/
noncomputable def parameter (g : CairnsCircleGap) (t : Icc (0 : ℝ) 1) : Circle :=
  Circle.exp (g.start + (g.stop - g.start) * (t : ℝ))

/-- Arc length divided by a full turn; this is the mesh quantity in the
parameter of σ, rather than a chord length or a length after applying h. -/
noncomputable def normalizedLength (g : CairnsCircleGap) : ℝ :=
  (g.stop - g.start) / (2 * Real.pi)

/-- The arc is an actual complementary component of the retained set, with
both endpoints retained. No connectedness or finiteness of the retained set
is imposed. The recurrence theorem supplies its closedness and nonemptiness. -/
def IsGapOf (g : CairnsCircleGap) (S : Set Circle) : Prop :=
  g.first ∈ S ∧ g.last ∈ S ∧
    ∃ x ∈ Sᶜ, connectedComponentIn Sᶜ x = g.openArc

/-- The supremum of normalized lengths of the actual residual arcs, with zero
inserted so the empty residual family has mesh zero. The recurrence theorem
proves attainment whenever the residual family is nonempty. -/
noncomputable def mesh (S : Set Circle) : ℝ :=
  sSup (insert 0 (normalizedLength '' {g | g.IsGapOf S}))

end CairnsCircleGap

end HolomorphicAnosov.Topology.Plane
