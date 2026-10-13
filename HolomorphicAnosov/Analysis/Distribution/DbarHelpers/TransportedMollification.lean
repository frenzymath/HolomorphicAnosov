import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexDistributionDbarEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.EuclideanDbarFirstTranspose
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.InteriorMollifierSmoothFirstDerivative
import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization
import HolomorphicAnosov.Analysis.Distribution.MollifierWeakConvergence
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.Distribution.ScaledMollifierTest
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Constructions.SumProd

/-!
# transported_mollification

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.
DAG node: `analysis.dbar_helper_transported_mollification_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A native complex dbar-closed current transported to ordered Euclidean coordinates has a smooth,
weakly convergent scaled mollifier family whose paired real-coordinate Cauchy–Riemann derivatives
vanish.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.

Proof/construction: Choose each supported mollifier test using the existing support construction
and define the paired scalar function on the strict interior, extending it by zero elsewhere. The
local fixed-support theorem gives smoothness and first derivatives. The transported distribution
equation cancels the two derivative pairings. The existing weak-convergence theorem supplies
convergence on every fixed test; no all-orders mollifier differentiation admission is invoked.
-/
theorem transported_mollification {n : ℕ} (hn : 1 ≤ n)
    (U : Opens (Fin n → ℂ)) (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ j φ, -T (HolomorphicAnosov.scalarDbarTest U j φ) = 0)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin (n+n)))) ℝ ⊤)
    (hρpos : ∀ x, 0 ≤ ρ x)
    (hρsupp : tsupport (ρ : EuclideanSpace ℝ (Fin (n+n)) → ℝ) ⊆ Metric.closedBall 0 1)
    (hρnorm : ∫ x, ρ x = 1) :
    let W := coordDomain (complexToOrderedEuclidean n).symm U
    let S := T.comp (complexTestFromEuclidean U)
    ∃ F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin (n+n)) → ℂ,
      (∀ ε hε, ContDiffOn ℝ ∞ (F ε hε) (mollifierDomain W ε)) ∧
      (∀ ε hε x, x ∈ mollifierDomain W ε → ∀ j : Fin n,
        ((fderiv ℝ (F ε hε) x) (EuclideanSpace.single (finSumFinEquiv (Sum.inl j)) 1) +
          Complex.I * (fderiv ℝ (F ε hε) x)
            (EuclideanSpace.single (finSumFinEquiv (Sum.inr j)) 1)) / 2 = 0) ∧
      (∀ φ : TestFunction W ℂ ⊤,
        Tendsto (fun ε : ℝ ↦ if hε : 0 < ε then
          ∫ x in mollifierDomain W ε, F ε hε x * φ x else 0)
          (𝓝[>] (0 : ℝ)) (𝓝 (S φ))) := by
  dsimp only
  let W := coordDomain (complexToOrderedEuclidean n).symm U
  let S := T.comp (complexTestFromEuclidean U)
  classical
  let κ : ∀ ε : ℝ, 0 < ε → ∀ x, x ∈ mollifierDomain W ε → TestFunction W ℂ ⊤ :=
    fun ε hε x hx ↦ Classical.choose
      (exists_scaled_mollifier_test W ρ hρsupp ε hε x hx.2)
  let F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin (n+n)) → ℂ :=
    fun ε hε x ↦ if hx : x ∈ mollifierDomain W ε then S (κ ε hε x hx) else 0
  have hκ : ∀ ε (hε : 0 < ε) x hx y,
      κ ε hε x hx y = (((ε⁻¹)^(n+n) : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (x-y)) : ℝ) : ℂ) := by
    intro ε hε x hx y
    exact Classical.choose_spec (exists_scaled_mollifier_test W ρ hρsupp ε hε x hx.2) y
  have hF : ∀ ε (hε : 0 < ε) x (hx : x ∈ mollifierDomain W ε),
      F ε hε x = S (κ ε hε x hx) := by
    intro ε hε x hx
    exact dite_eq_left hx
  have hlocal (ε : ℝ) (hε : 0 < ε) :=
    interior_mollifier_smooth_first_derivative (show 0 < n+n by omega)
      W S ρ hρsupp ε hε (κ ε hε) (hκ ε hε) (F ε hε) (hF ε hε)
  refine ⟨F, fun ε hε ↦ (hlocal ε hε).1, ?_, ?_⟩
  · intro ε hε x hx j
    rw [(hlocal ε hε).2 x hx (finSumFinEquiv (Sum.inl j)),
      (hlocal ε hε).2 x hx (finSumFinEquiv (Sum.inr j))]
    apply euclidean_dbar_first_transpose
    exact complex_distribution_dbar_euclidean U T hT j _
  · exact distribution_mollifier_weak_convergence (show 1 ≤ n+n by omega)
      W S ρ hρpos hρsupp hρnorm κ F hκ hF


end HolomorphicAnosov.Analysis.Distribution
