import Mathlib.Analysis.Distribution.TestFunction

/-!
# euclidean_dbar_first_transpose

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_euclidean_dbar_first_transpose_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The vanishing negative current pairing of the half-sum of real and imaginary test derivatives
equals vanishing of the corresponding half-sum of negative derivative pairings.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Expand the complex-linear functional on scalar multiples and sums. Rewrite
scalar multiplication as multiplication, distribute the negative sign, and reorder the scalar
factors. This is precisely the distributional derivative convention.
-/
theorem euclidean_dbar_first_transpose
    {m : ℕ} (U : Opens (EuclideanSpace ℝ (Fin m)))
    (S : TestFunction U ℂ ⊤ →L[ℂ] ℂ) (i j : Fin m)
    (φ : TestFunction U ℂ ⊤)
    (h : -S ((2 : ℂ)⁻¹ •
      ((TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1) φ : TestFunction U ℂ ⊤) +
       Complex.I • (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single j 1) φ :
         TestFunction U ℂ ⊤))) = 0) :
    (-S (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1) φ) +
      Complex.I * -S (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single j 1) φ)) / 2 = 0 := by
  simpa only [map_smul, map_add, smul_eq_mul, neg_mul, mul_neg, div_eq_mul_inv,
    mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, neg_add_rev, add_comm] using h


end HolomorphicAnosov.Analysis.Distribution
