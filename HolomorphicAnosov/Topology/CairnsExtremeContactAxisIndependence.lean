import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

namespace HolomorphicAnosov

/-- Nonzero horizontal and vertical complex displacements are linearly independent over ℝ. -/
theorem cairns_horizontal_vertical_linearIndependent
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℝ ![(a : ℂ), (b : ℂ) * Complex.I] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have hr := congrArg Complex.re hg
    simp at hr
    exact Or.resolve_right hr ha
  · have hi := congrArg Complex.im hg
    simp at hi
    exact Or.resolve_right hi hb

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- Nonzero vertical and horizontal complex displacements are linearly independent over ℝ. -/
theorem cairns_vertical_horizontal_linearIndependent
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℝ ![(b : ℂ) * Complex.I, (a : ℂ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · have hi := congrArg Complex.im hg
    simp at hi
    exact Or.resolve_right hi hb
  · have hr := congrArg Complex.re hg
    simp at hr
    exact Or.resolve_right hr ha

end HolomorphicAnosov
