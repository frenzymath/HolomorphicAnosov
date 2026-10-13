import HolomorphicAnosov.Analysis.Regularity.EuclideanPolynomialEval
import HolomorphicAnosov.Analysis.Regularity.EuclideanCoordinatePartial
import Mathlib.Data.List.FinRange

/-! Campanato (1964), Lemma [2.I], printed pp.140–143: Euclidean polynomial calculus. -/

noncomputable section
namespace HolomorphicAnosov.Analysis.Regularity

/-- Classical mixed partial derivative in coordinate order 0, …, N − 1.
Source: Campanato (1964), p. 143; the finite monomial calculation in DAG proof E6.
Each coordinate derivative is iterated β i times. For β = 0 this is evaluation itself;
for polynomials these are the classical mixed partials and are independent of coordinate order. -/
def euclideanPolynomialMixedPartial {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (β : Fin N → ℕ) : EuclideanSpace ℝ (Fin N) → ℝ :=
  (List.finRange N).foldl
    (fun f i ↦ (euclideanCoordinatePartial i)^[β i] f) (euclideanPolynomialEval P)


end HolomorphicAnosov.Analysis.Regularity
