import Mathlib.Analysis.Complex.Basic

/-!
# Closed squares in a uniform complex grid

Source: Conway, Functions of One Complex Variable, second edition (1978),
VIII Proposition 1.1, pp.195–196: closed rectangles of a horizontal/vertical
grid. A uniform square grid indexed by integer pairs is the specialization here.
DAG node: `analysis.complex_grid_square_g19`.
-/

namespace HolomorphicAnosov.Analysis.Complex

/-- The closed square with lower-left corner δ(q₁ + q₂ I) and side length δ.
For positive δ these squares form the uniform axis-parallel grid in Conway
VIII.1.1, pp.195–196. The definition is literal coordinate inequalities;
positivity of δ is imposed by the statements using it. -/
def complexGridSquare (δ : ℝ) (q : ℤ × ℤ) : Set ℂ :=
  {z | δ * (q.1 : ℝ) ≤ z.re ∧ z.re ≤ δ * ((q.1 : ℝ) + 1) ∧
    δ * (q.2 : ℝ) ≤ z.im ∧ z.im ≤ δ * ((q.2 : ℝ) + 1)}

end HolomorphicAnosov.Analysis.Complex
