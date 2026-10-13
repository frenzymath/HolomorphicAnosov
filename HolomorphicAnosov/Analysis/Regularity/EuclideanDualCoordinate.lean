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

lemma euclidean_dual_coordinate_sum {N : ℕ}
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    L = ∑ i : Fin N, L (PiLp.single 2 i (1 : ℝ)) •
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) := by
  classical
  ext v
  have hv : v = ∑ i : Fin N, (v i) • PiLp.single 2 i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, mul_comm]



end HolomorphicAnosov
