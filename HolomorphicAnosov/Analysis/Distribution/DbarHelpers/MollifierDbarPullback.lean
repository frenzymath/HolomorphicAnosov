import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleRe
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Constructions.SumProd

/-!
# mollifier_dbar_pullback

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.
DAG node: `analysis.dbar_helper_mollifier_dbar_pullback_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A smooth Euclidean function obeying the paired real coordinate Cauchy–Riemann equations pulls back
to a function with zero native complex antiholomorphic partial derivatives.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.

Proof/construction: At the point of the inverse-image domain, differentiate the composition with
the coordinate equivalence. The linear chain rule sends the complex real and imaginary unit
directions to the two Euclidean unit directions. Substitute the assumed paired derivative equation
in the native Wirtinger half-sum.
-/
theorem mollifier_dbar_pullback {n : ℕ}
    (Q : Opens (EuclideanSpace ℝ (Fin (n+n))))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Q : Set _))
    (hbar : ∀ x ∈ Q, ∀ j : Fin n,
      ((fderiv ℝ F x) (EuclideanSpace.single (finSumFinEquiv (Sum.inl j)) 1) +
        Complex.I * (fderiv ℝ F x)
          (EuclideanSpace.single (finSumFinEquiv (Sum.inr j)) 1)) / 2 = 0)
    (z : Fin n → ℂ) (hz : complexToOrderedEuclidean n z ∈ Q) (j : Fin n) :
    antiholomorphicPartial (fun x ↦ F (complexToOrderedEuclidean n x)) j z = 0 := by
  have hFd := (hF.contDiffAt (Q.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have he : DifferentiableAt ℝ (complexToOrderedEuclidean n) z :=
    (complexToOrderedEuclidean n).differentiableAt
  have hchain := fderiv_comp z hFd he
  simp only [Function.comp_def] at hchain
  rw [antiholomorphicPartial, hchain]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]
  change ((fderiv ℝ F (complexToOrderedEuclidean n z))
      (complexToOrderedEuclidean n (Pi.single j 1)) +
    Complex.I * (fderiv ℝ F (complexToOrderedEuclidean n z))
      (complexToOrderedEuclidean n (Pi.single j Complex.I))) / 2 = 0
  rw [complexToOrderedEuclidean_single_re, complexToOrderedEuclidean_single_im]
  exact hbar _ hz j


end HolomorphicAnosov.Analysis.Distribution
