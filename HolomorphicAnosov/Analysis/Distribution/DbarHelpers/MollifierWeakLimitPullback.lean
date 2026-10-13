import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclideanApply
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanSetIntegralTransport
import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization
import Mathlib.Analysis.Distribution.TestFunction

/-!
# mollifier_weak_limit_pullback

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.
DAG node: `analysis.dbar_helper_mollifier_weak_limit_pullback_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Fixed-test weak convergence of a Euclidean regularization implies weak convergence against native
complex tests after coordinate substitution.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.

Proof/construction: Pull the fixed complex test to the Euclidean domain. Transporting it back
gives the original test by inverse cancellation. Apply the assumed weak convergence to this one
fixed test and rewrite each set integral using the measure-preserving coordinate equivalence. The
nonpositive-parameter branch is zero on both sides.
-/
theorem mollifier_weak_limit_pullback {n : ℕ}
    (U : Opens (Fin n → ℂ)) (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin (n+n)) → ℂ)
    (hweak : ∀ φ : TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤,
      Tendsto (fun ε : ℝ ↦ if hε : 0 < ε then
        ∫ x in mollifierDomain (coordDomain (complexToOrderedEuclidean n).symm U) ε,
          F ε hε x * φ x else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (T (complexTestFromEuclidean U φ))))
    (φ : TestFunction U ℂ ⊤) :
    Tendsto (fun ε : ℝ ↦ if hε : 0 < ε then
      ∫ z in ((complexToOrderedEuclidean n) ⁻¹'
        mollifierDomain (coordDomain (complexToOrderedEuclidean n).symm U) ε),
        F ε hε (complexToOrderedEuclidean n z) * φ z else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (T φ)) := by
  let φE := coordPullbackCLM (complexToOrderedEuclidean n).symm U φ
  have htest : complexTestFromEuclidean U φE = φ := by
    ext z
    rw [complexTestFromEuclidean_apply]
    change φ ((complexToOrderedEuclidean n).symm (complexToOrderedEuclidean n z)) = φ z
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hw := hweak φE
  rw [htest] at hw
  convert hw using 1
  funext ε
  split_ifs with hε
  · rw [ordered_euclidean_setIntegral_transport]
    apply integral_congr_ae
    filter_upwards with z
    change F ε hε (complexToOrderedEuclidean n z) * φ z =
      F ε hε (complexToOrderedEuclidean n z) *
        φ ((complexToOrderedEuclidean n).symm (complexToOrderedEuclidean n z))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · rfl


end HolomorphicAnosov.Analysis.Distribution
