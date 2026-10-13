import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

lemma holderOnWith_of_norm_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (f : E → F) (V : Set E)
    (K r : NNReal)
    (hbound : ∀ x ∈ V, ∀ y ∈ V, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ (r : ℝ)) :
    HolderOnWith K r f V := by
  intro x hx y hy
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm] using hbound x hx y hy

-- Reconstruction uses the actual Euclidean coordinate vectors and operator norm.


end HolomorphicAnosov
