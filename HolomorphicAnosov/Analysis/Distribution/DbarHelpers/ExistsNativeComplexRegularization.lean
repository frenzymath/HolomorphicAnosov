import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Exists_normalized_test_mollifier
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MollifierDbarPullback
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MollifierWeakLimitPullback
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.TransportedMollification
import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction

/-!
# exists_native_complex_regularization

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.
DAG node: `analysis.dbar_helper_exists_native_complex_regularization_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Every native dbar-closed complex scalar current has varying open strict-interior domains and
smooth scalar functions on them, all antiholomorphic derivatives zero, whose pairings converge to
the current on each fixed native test.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.

Proof/construction: Choose a nonnegative normalized smooth compactly supported mollifier. Apply
transported mollification. Pull the varying strict-interior domains and functions back through the
ordered real coordinate equivalence, using zero for nonpositive parameters. Smoothness follows by
the chain rule, the native antiholomorphic equation by the coordinate derivative identities, and
fixed-test weak convergence by the proved volume transport. Positive parameters form a punctured
right neighborhood of zero, so the arbitrary nonpositive branch does not affect the limit.
-/
theorem exists_native_complex_regularization {n : ℕ} (hn : 1 ≤ n)
    (U : Opens (Fin n → ℂ)) (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ j φ, -T (HolomorphicAnosov.scalarDbarTest U j φ) = 0) :
    ∃ (Q : ℝ → Opens (Fin n → ℂ)) (f : ℝ → (Fin n → ℂ) → ℂ),
      (∀ ε, (Q ε : Set _) = (complexToOrderedEuclidean n) ⁻¹'
        mollifierDomain (coordDomain (complexToOrderedEuclidean n).symm U) ε) ∧
      (∀ ε, 0 < ε → ContDiffOn ℝ ∞ (f ε) (Q ε : Set _)) ∧
      (∀ ε, 0 < ε → ∀ x ∈ Q ε, ∀ j, antiholomorphicPartial (f ε) j x = 0) ∧
      (∀ φ : TestFunction U ℂ ⊤,
        Tendsto (fun ε ↦ ∫ x in (Q ε : Set _), f ε x * φ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (T φ))) := by
  classical
  obtain ⟨ρ, hpos, hsupp, hnorm⟩ := exists_normalized_test_mollifier (n+n)
  obtain ⟨F, hsm, hbar, hweak⟩ := transported_mollification hn U T hT ρ hpos hsupp hnorm
  let W := coordDomain (complexToOrderedEuclidean n).symm U
  let R : ℝ → Opens (EuclideanSpace ℝ (Fin (n+n))) :=
    fun ε ↦ ⟨mollifierDomain W ε, W.isOpen.inter (isOpen_lt continuous_const Metric.continuous_infEDist)⟩
  let Q : ℝ → Opens (Fin n → ℂ) := fun ε ↦ coordDomain (complexToOrderedEuclidean n) (R ε)
  let f : ℝ → (Fin n → ℂ) → ℂ :=
    fun ε x ↦ if hε : 0 < ε then F ε hε (complexToOrderedEuclidean n x) else 0
  refine ⟨Q, f, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro ε hε
    have hh := (hsm ε hε).comp (complexToOrderedEuclidean n).contDiff.contDiffOn
      (s := (Q ε : Set _)) (fun _ hx ↦ hx)
    simpa only [f, Function.comp_def, dite_eq_left hε] using hh
  · intro ε hε x hx j
    have hh := mollifier_dbar_pullback (R ε) (F ε hε) (hsm ε hε) (hbar ε hε) x hx j
    simpa only [f, Function.comp_def, dite_eq_left hε] using hh
  · intro φ
    have hh := mollifier_weak_limit_pullback U T F hweak φ
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : 0 < ε := hε
    simp only [f, dite_eq_left he]
    rfl


end HolomorphicAnosov.Analysis.Distribution
