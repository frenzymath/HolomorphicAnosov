import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Lower bounds from a uniform absolute-value sublevel estimate

This is the measurable-set step needed after the compact coefficient-sphere
sublevel argument in Campanato's Lemma [2.I], printed pp. 141--142.  It is
kept separate so that the same measure calculation can be reused by other
finite-dimensional minimization arguments.

The source proof writes the complement of `{|f| ≤ r}` inside `E`, uses the
lower mass of `E`, and bounds the square of `f` there by `r²`.  The exact
conversion between `ENNReal` measure inequalities and real set integrals is
proved as the named theorem below; the displayed statement records all
measurability and finiteness hypotheses needed by that calculation.
-/
noncomputable section
open MeasureTheory

namespace HolomorphicAnosov.Analysis.Regularity

/-- A uniform positive sublevel threshold gives a positive lower bound for
the square integral on every measurable set of prescribed positive mass.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], printed pp. 141--142, the passage from (2.7) to (2.9), with the
set-difference and integral arithmetic written out as an independent helper.
Proof: put U={|f|≤r}. The real measure decomposition of E into E∩U
and E\U gives μ.real(E\U)≥m/2. On E\U the square is at least r².
Integrability on E restricts to E\U, so integral monotonicity bounds its
integral below by r²μ.real(E\U). Nonnegativity bounds this by the integral
on E. The square-integrability premise is essential: without it the
Bochner integral of a nonintegrable function is defined to be zero. -/
theorem setIntegral_sq_lower_of_sublevel_quantitative
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : AEMeasurable f μ)
    (E : Set α) (hE : NullMeasurableSet E μ)
    (hfi : IntegrableOn (fun x ↦ |f x| ^ 2) E μ)
    (m r : ℝ) (_hm : 0 < m) (hr : 0 < r)
    (hmass : m ≤ μ.real E)
    (hsmall : μ {x | |f x| ≤ r} < ENNReal.ofReal (m / 2)) :
    r ^ 2 * (m / 2) ≤ ∫ x in E, |f x| ^ 2 ∂μ := by
  let U := {x | |f x| ≤ r}
  have hU : NullMeasurableSet U μ := (continuous_abs.measurable.comp_aemeasurable hf).nullMeasurable measurableSet_Iic
  have hsmallReal : μ.real U < m / 2 := by
    exact (ENNReal.toReal_lt_of_lt_ofReal hsmall)
  have hsplit := measureReal_inter_add_sdiff₀ (s := E) hU
  have hinter : μ.real (E ∩ U) ≤ μ.real U := measureReal_mono Set.inter_subset_right
  have hmassDiff : m / 2 ≤ μ.real (E \ U) := by linarith
  have hbound : r ^ 2 * μ.real (E \ U) ≤ ∫ x in E \ U, |f x| ^ 2 ∂μ := by
    have h := setIntegral_mono_on₀ (f := fun _ ↦ r ^ 2) (integrableOn_const (measure_ne_top μ _))
      (hfi.mono_set Set.sdiff_subset) (hE.diff hU) (fun x hx ↦ ?_)
    · simpa only [setIntegral_const, smul_eq_mul, mul_comm] using h
    · have hx' : r < |f x| := lt_of_not_ge hx.2
      nlinarith [abs_nonneg (f x)]
  calc
    r ^ 2 * (m / 2) ≤ r ^ 2 * μ.real (E \ U) := mul_le_mul_of_nonneg_left hmassDiff (sq_nonneg r)
    _ ≤ ∫ x in E \ U, |f x| ^ 2 ∂μ := hbound
    _ ≤ ∫ x in E, |f x| ^ 2 ∂μ := setIntegral_mono_set hfi
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg |f x|))
      (Filter.Eventually.of_forall Set.sdiff_subset)

/-- The positive-bound form of the quantitative sublevel estimate above.
The integrability assumption is essential for the totalized Bochner integral. -/
theorem setIntegral_sq_lower_of_sublevel
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : AEMeasurable f μ)
    (E : Set α) (hE : NullMeasurableSet E μ)
    (hfi : IntegrableOn (fun x ↦ |f x| ^ 2) E μ)
    (m r : ℝ) (hm : 0 < m) (hr : 0 < r)
    (hmass : m ≤ μ.real E)
    (hsmall : μ {x | |f x| ≤ r} < ENNReal.ofReal (m / 2)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ ∫ x in E, |f x| ^ 2 ∂μ := by
  refine ⟨r ^ 2 * (m / 2), by positivity, ?_⟩
  exact setIntegral_sq_lower_of_sublevel_quantitative μ f hf E hE hfi m r hm hr hmass hsmall

end HolomorphicAnosov.Analysis.Regularity


