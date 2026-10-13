import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Campanato (1964), Lemma [2.I], printed pp.140–143: Euclidean polynomial calculus. -/

noncomputable section
namespace HolomorphicAnosov.Analysis.Regularity

/-- The classical real coordinate partial derivative, computed along the standard coordinate line.
Source: Campanato (1964), p. 143, and Mathlib's ordinary real `deriv`.
The vector `EuclideanSpace.single i 1` is the i-th Euclidean unit coordinate vector. -/
def euclideanCoordinatePartial {N : ℕ} (i : Fin N)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  deriv (fun t : ℝ ↦ f (x + t • EuclideanSpace.single i 1)) 0


end HolomorphicAnosov.Analysis.Regularity
