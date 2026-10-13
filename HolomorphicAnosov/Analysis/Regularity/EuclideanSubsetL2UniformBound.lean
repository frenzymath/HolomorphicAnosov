import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounding an L² integral on a Euclidean ball subset

Source: Campanato (1964), Lemma [2.I], pp.140–143, q=2, the integral-to-uniform
bound consequence. Only finite ball volume and integration of the pointwise
bound are needed; the subset may be measurable only in the completed measure.
-/

open MeasureTheory
namespace HolomorphicAnosov.Analysis.Regularity

/-- Source: Campanato (1964), Lemma [2.I], pp.140–143, q=2 consequence.
Integrate |f|²≤M² on E. Finite ball volume bounds volume(E) by ρ^N times the
unit-ball volume. Taking square roots and using positive-radius power laws gives
the displayed bound. This includes zero-dimensional Euclidean space, M=0 and E=∅.
No polynomial or differentiability hypothesis is needed. -/
theorem euclidean_subset_l2_uniform_bound {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (a : EuclideanSpace ℝ (Fin N))
    (ρ : ℝ) (hρ : 0 < ρ) (E : Set (EuclideanSpace ℝ (Fin N)))
    (hE : NullMeasurableSet E volume) (hEB : E ⊆ Metric.ball a ρ)
    (hf : IntegrableOn (fun x ↦ |f x| ^ 2) E volume)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x ∈ E, |f x| ≤ M) :
    Real.sqrt (∫ x in E, |f x| ^ 2) ≤
      M * Real.sqrt (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)) *
        Real.rpow ρ ((N : ℝ) / 2) := by
  have hfinite : volume E < ⊤ :=
    (measure_mono hEB).trans_lt measure_ball_lt_top
  have hvol : volume.real E ≤
      ρ ^ N * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    have hle : volume E ≤ volume (Metric.ball a ρ) := measure_mono hEB
    have hle' := ENNReal.toReal_mono measure_ball_lt_top.ne hle
    change volume.real E ≤ volume.real (Metric.ball a ρ) at hle'
    convert hle' using 1
    simp only [measureReal_def]
    rw [volume.addHaar_ball_of_pos a hρ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le _)]
    simp
  have hi : (∫ x in E, |f x| ^ 2) ≤
      M ^ 2 * (ρ ^ N * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)) := by
    calc
      _ ≤ ∫ _ in E, M ^ 2 := setIntegral_mono_on₀ hf
        (integrableOn_const hfinite.ne) hE (fun x hx ↦ by
          nlinarith [abs_nonneg (f x), hbound x hx])
      _ = M ^ 2 * volume.real E := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hvol (sq_nonneg M)
  calc
    _ ≤ Real.sqrt (M ^ 2 *
        (ρ ^ N * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))) :=
      Real.sqrt_le_sqrt hi
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM,
        Real.sqrt_mul (pow_nonneg hρ.le _)]
      have hsqrt : Real.sqrt (ρ ^ N) = Real.rpow ρ ((N : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
        congr 1
        ring
      rw [hsqrt]
      ring

end HolomorphicAnosov.Analysis.Regularity
