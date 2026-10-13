import Mathlib.Basic.Real.Basic

/-!
Public DAG node: `analysis.mashreghi_radial_radius_g3` (definition).
Definition origin: explicit cofinal interior sequence implementing the radial limit asserted in Mashreghi Theorem 4.3, printed p.442. The specific sequence is an implementation choice, not a printed source formula.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
namespace HolomorphicAnosov.MashreghiRadial
/-- The explicit cofinal sequence 1−1/(n+2) inside the unit interval.
This implementation choice supplies the radial-limit construction in
Mashreghi Theorem 4.3, printed p.442 before (4.6); the formula itself is not
printed in that source. Its elementary order and limit facts are local proofs. -/
def radialRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)
end HolomorphicAnosov.MashreghiRadial
