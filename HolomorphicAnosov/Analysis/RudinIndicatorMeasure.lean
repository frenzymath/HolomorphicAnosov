import HolomorphicAnosov.Analysis.RudinComplexRadonNikodymFinite
import HolomorphicAnosov.MeasureTheory.RudinClosedSetAverageAE
import Mathlib.MeasureTheory.VectorMeasure.AddContent
import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

open MeasureTheory
namespace HolomorphicAnosov
/-- Rudin, Real and Complex Analysis, Theorem 6.16, p.127 equation (4).
The indicator classes form a finitely additive L¹-valued content bounded by μ.
Mathlib's dominated-content theorem supplies countable additivity. Compose
with T. A null indicator class has norm zero, giving absolute continuity. -/
theorem rudin_indicator_complex_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Lp ℂ 1 μ →L[ℂ] ℂ) :
    ∃ ν : ComplexMeasure X,
      (∀ s (hs : MeasurableSet s),
        ν s = T (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ))) ∧
      (∀ s, MeasurableSet s → μ s = 0 → ν s = 0) := by
  classical
  let I : Set X → Lp ℂ 1 μ := fun s ↦
    if hs : MeasurableSet s then indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ)
    else 0
  have hbound (s : Set X) : ‖I s‖ₑ ≤ μ s := by
    by_cases hs : MeasurableSet s
    · simpa [I, hs] using
        (enorm_indicatorConstLp_le (μ := μ) (p := 1) (hs := hs)
          (hμs := measure_ne_top μ s) (c := (1 : ℂ)))
    · simp [I, hs]
  let v : VectorMeasure X (Lp ℂ 1 μ) :=
    VectorMeasure.of_additive_of_le_measure I hbound
      (by
        intro s t hs ht hst
        simpa [I, hs, ht, hs.union ht] using
          indicatorConstLp_disjoint_union (μ := μ) (p := 1) hs ht
            (measure_ne_top μ s) (measure_ne_top μ t) hst (1 : ℂ))
      (by intro s hs; simp [I, hs])
  refine ⟨v.mapRange T.toAddMonoidHom T.continuous, ?_, ?_⟩
  · intro s hs
    change T (I s) = _
    simp [I, hs]
  · intro s hs hnull
    have hzero : I s = 0 := enorm_eq_zero.mp (le_antisymm (hnull ▸ hbound s) bot_le)
    change T (I s) = 0
    simp [hzero]
/-- Rudin Theorem 6.16, p.128, equation (5) and Case 1. Radon–Nikodym gives
an integrable measurable density. The operator bound bounds each normalized
set integral by ‖T‖, and Theorem 1.40 gives the same bound almost everywhere. -/
theorem rudin_indicator_bounded_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Lp ℂ 1 μ →L[ℂ] ℂ) :
    ∃ h : X → ℂ, Measurable h ∧ Integrable h μ ∧
      (∀ᵐ x ∂μ, ‖h x‖ ≤ ‖T‖) ∧
      ∀ s (hs : MeasurableSet s),
        T (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ)) = ∫ x in s, h x ∂μ := by
  obtain ⟨ν, hν, hnull⟩ := rudin_indicator_complex_measure μ T
  obtain ⟨h, hm, hi, heq⟩ := rudin_complex_radon_nikodym_finite μ ν hnull
  have hset (s : Set X) (hs : MeasurableSet s) :
      T (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℂ)) = ∫ x in s, h x ∂μ :=
    (hν s hs).symm.trans (heq s hs)
  refine ⟨h, hm, hi, ?_, hset⟩
  have hb := rudin_closed_set_average_ae μ h hm hi (Metric.closedBall 0 ‖T‖)
    Metric.isClosed_closedBall ?_
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  · intro s hs hpos
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ← hset s hs]
    have hn : ‖indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℂ)‖ = μ.real s := by
      simp [norm_indicatorConstLp (p := 1) one_ne_zero ENNReal.one_ne_top]
    have hp : 0 < (μ s).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ s)
    calc
      _ ≤ (μ s).toReal⁻¹ * (‖T‖ * μ.real s) :=
        mul_le_mul_of_nonneg_left
          (by simpa [hn] using
            (T.le_opNorm (indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℂ))))
          (by positivity)
      _ = ‖T‖ := by rw [measureReal_def]; field_simp
end HolomorphicAnosov

