import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# In every finite-dimensional real Euclidean coordinate space there exists a nonnegative smooth
compactly supported real test on the whole space, supported in the closed unit ball, whose
Lebesgue integral equals one.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, normalized regularizing kernel. DAG node:
`analysis.dbar_helper_exists_normalized_test_mollifier_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
In every finite-dimensional real Euclidean coordinate space there exists a nonnegative smooth
compactly supported real test on the whole space, supported in the closed unit ball, whose
Lebesgue integral equals one.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, normalized regularizing kernel.

Proof/construction: Choose the native smooth bump with inner radius one quarter and outer radius
one half at zero, and divide it by its positive integral using the native normalized-bump
construction. It is smooth, nonnegative, compactly supported, and has integral one. Its closed
support is the closed ball of radius one half, contained in the closed unit ball. This includes
dimension zero.
-/
theorem exists_normalized_test_mollifier (m : ℕ) :
    ∃ ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤,
      (∀ x, 0 ≤ ρ x) ∧
      tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆ Metric.closedBall 0 1 ∧
      (∫ x, ρ x) = 1 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) :=
    ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤ :=
    ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, Set.subset_univ _⟩
  refine ⟨ρ, b.nonneg_normed, ?_, b.integral_normed⟩
  change tsupport (b.normed volume) ⊆ Metric.closedBall 0 1
  rw [b.tsupport_normed_eq]
  exact Metric.closedBall_subset_closedBall (by norm_num [b])


end HolomorphicAnosov.Analysis.Distribution
