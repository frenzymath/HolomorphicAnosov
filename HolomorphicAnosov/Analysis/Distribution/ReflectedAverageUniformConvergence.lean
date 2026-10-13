import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/-- A normalized nonnegative compact kernel approximates any uniformly
continuous vector-valued function uniformly under small translations.

Source: Dyatlov, *Lecture notes for 18.155*, proof of Theorem 6.7, p.73,
the estimate immediately following (6.25). This is the same norm estimate in a
real Banach target, including spaces of real multilinear derivatives.
Proof: uniform continuity gives a radius δ for half the requested tolerance.
For 0 < ε < δ, every z in the kernel support has ‖εz‖ ≤ ε < δ.
Subtract the constant g(y) inside the integral using normalization; the norm
of the integrand is at most ρ(z) times half the tolerance. Integrating gives
the bound uniformly in y. Compact support and continuity justify the integrals. -/
theorem reflected_average_uniform_approximation
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (hρ_norm : ∫ x, ρ x ∂volume = 1)
    (g : EuclideanSpace ℝ (Fin m) → F) (hg : UniformContinuous g) :
    ∀ t : ℝ, 0 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      ‖(∫ z, ρ z • g (y + ε • z)) - g y‖ < t := by
  intro t ht
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hg (t / 2) (half_pos ht)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  intro y
  have hρint : Integrable (ρ : EuclideanSpace ℝ (Fin m) → ℝ) volume :=
    ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  have hgε : Continuous (fun z : EuclideanSpace ℝ (Fin m) => g (y + ε • z)) :=
    hg.continuous.comp (continuous_const.add (continuous_id.const_smul ε))
  have hint : Integrable (fun z => ρ z • g (y + ε • z)) volume :=
    (ρ.continuous.smul hgε).integrable_of_hasCompactSupport
      (ρ.hasCompactSupport.smul_right (f' := fun z => g (y + ε • z)))
  have hid : (∫ z, ρ z • g (y + ε • z)) - g y =
      ∫ z, ρ z • (g (y + ε • z) - g y) := by
    simp_rw [smul_sub]
    rw [integral_sub hint (hρint.smul_const (g y)), integral_smul_const, hρ_norm, one_smul]
  rw [hid]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (hρint.mul_const (t / 2)) ?_) ?_
  · filter_upwards [] with z
    by_cases hz : ρ z = 0
    · simp [hz]
    have hz1 : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        hρ_support (subset_tsupport _ hz)
    have hdist : dist (y + ε • z) y < δ := by
      calc
        dist (y + ε • z) y = ε * ‖z‖ := by
          simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
        _ ≤ ε := by simpa using mul_le_mul_of_nonneg_left hz1 hε.1.le
        _ < δ := hε.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg z)]
    exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa [dist_eq_norm] using hδg hdist))
      (hρ_nonneg z)
  · rw [integral_mul_const, hρ_norm, one_mul]
    exact half_lt_self ht

end HolomorphicAnosov.Analysis.Distribution
