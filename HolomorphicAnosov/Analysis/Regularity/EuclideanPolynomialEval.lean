import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Campanato (1964), Lemma [2.I], printed pp.140–143: Euclidean polynomial calculus. -/

noncomputable section
namespace HolomorphicAnosov.Analysis.Regularity

/-- Evaluation of a real multivariate polynomial on the original Euclidean coordinate model.
Source: Campanato (1964), pp. 140–143, with Mathlib's `MvPolynomial.eval`. -/
def euclideanPolynomialEval {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  MvPolynomial.eval (fun i ↦ x i) P


end HolomorphicAnosov.Analysis.Regularity
