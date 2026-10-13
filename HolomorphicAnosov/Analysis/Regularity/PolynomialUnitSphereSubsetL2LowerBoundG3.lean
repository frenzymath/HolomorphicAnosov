import HolomorphicAnosov.Analysis.Regularity.SetIntegralSquareLowerBoundG3
import HolomorphicAnosov.Analysis.Regularity.PolynomialCoefficientCompactModel
import HolomorphicAnosov.Analysis.Regularity.CompactUniformSublevel
import HolomorphicAnosov.Analysis.Regularity.SublevelSmallOfZeroSetNull
import HolomorphicAnosov.Analysis.Measure.AnalyticZeroSetNull
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Normalized polynomial minimum on measurable subsets

This interface isolates Campanato's finite-dimensional minimization and
Remez-type step (1964, Lemma [2.I], printed pp. 140--142).  The coefficient
model, compact sphere, individual zero-set sublevel estimates, and their
compact uniformization are supplied by the named preceding modules.  The
remaining set-integral lower bound is exposed as a reusable theorem for the
affine-scaling consumer.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HolomorphicAnosov.Analysis.Regularity

/-- Polynomial squares are integrable on every subset of the closed unit ball.
This supplies the Bochner-integrability premise of the sublevel estimate:
polynomial evaluation is continuous, its absolute square is continuous, and
continuous functions are integrable on the compact closed ball. Restriction
to an arbitrary subset preserves integrability. -/
private theorem polynomial_sq_integrableOn_subset_closedBall
    {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {E : Set (EuclideanSpace ℝ (Fin N))}
    (hE : E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) :
    IntegrableOn (fun x ↦ |MvPolynomial.eval (fun i ↦ x i) p| ^ 2) E volume := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin N) ↦
      MvPolynomial.eval (fun i ↦ x i) p) :=
    (AnalyticOnNhd.eval_continuousLinearMap'
      (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) p).continuous
  exact ((hc.abs.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hE

/-- Every bounded-degree normalized real polynomial has a uniformly positive
square integral on every null-measurable subset of the unit ball with fixed
positive volume.  The polynomial is represented through the finite coefficient
model `e` supplied by `polynomial_coefficient_compact_model`.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], printed pp. 140--142, equations (2.3)--(2.11).  The formal proof
chooses the compact coefficient sphere, applies the zero-set sublevel lemma
and compact uniformization, then applies
`setIntegral_sq_lower_of_sublevel_quantitative` to the complement of the uniform sublevel
set. The required square-integrability premise is proved below from
continuity on the compact closed unit ball and restriction to E. Apply the
finite-measure helper to volume restricted to that ball (or to the induced
measure on its compact subtype); restriction identities recover the displayed
integral. Uniformity requires retaining the quantitative bound r²(A/2) from
the measure calculation, not merely choosing each polynomial's positive integral.
The positivity argument uses the real-analytic zero-set-null theorem
already supplied by `AnalyticZeroSetNull`.
-/
theorem polynomial_unitSphere_subset_l2_lower_bound_g3
    (N n : ℕ) (hN : 1 ≤ N) (A : ℝ) (hA : 0 < A)
    (_hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)) :
    ∃ d : ℕ,
      ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
        ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        ∃ c : ℝ, 0 < c ∧
          ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
          ∀ E : Set (EuclideanSpace ℝ (Fin N)),
            NullMeasurableSet E volume →
            E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
            A ≤ volume.real E →
            c ≤ ∫ x in E,
              |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2 := by
  let K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1
  let μ := volume.restrict K
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_ne_top
  have polynomial_bound (p : MvPolynomial (Fin N) ℝ)
      (E : Set (EuclideanSpace ℝ (Fin N))) (hE : NullMeasurableSet E μ)
      (hEK : E ⊆ K) (r : ℝ) (hr : 0 < r) (hmass : A ≤ μ.real E)
      (hsmall : μ {x | |MvPolynomial.eval (fun i ↦ x i) p| ≤ r} <
        ENNReal.ofReal (A / 2)) :
      r ^ 2 * (A / 2) ≤ ∫ x in E, |MvPolynomial.eval (fun i ↦ x i) p| ^ 2 ∂μ := by
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin N) ↦
        MvPolynomial.eval (fun i ↦ x i) p) :=
      (AnalyticOnNhd.eval_continuousLinearMap'
        (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) p).continuous
    exact setIntegral_sq_lower_of_sublevel_quantitative μ _ hc.measurable.aemeasurable E hE
      ((polynomial_sq_integrableOn_subset_closedBall p hEK).mono_measure Measure.restrict_le_self)
      A r hA hr hmass hsmall
  classical
  obtain ⟨d, e, hsphere, T, hT⟩ := polynomial_coefficient_compact_model N n
  let ν : Measure ↥K := volume.comap Subtype.val
  have hK : MeasurableSet K := measurableSet_closedBall
  have : IsFiniteMeasure ν := by
    constructor
    change (volume.comap (Subtype.val : ↥K → EuclideanSpace ℝ (Fin N))) Set.univ < ⊤
    rw [comap_subtype_coe_apply hK]
    simpa only [Set.image_univ, Subtype.range_coe] using
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) 1).measure_lt_top
  have hzero (v : Fin d → ℝ) (hv : v ∈ Metric.sphere (0 : Fin d → ℝ) 1) :
      ν {x | T v x = 0} = 0 := by
    have hv0 : v ≠ 0 := by
      intro h
      simp [h] at hv
    have hp : (e v).val ≠ 0 := by
      intro h
      apply hv0
      apply e.injective
      apply Subtype.ext
      simpa using h
    have hnonzero : ∃ x : EuclideanSpace ℝ (Fin N),
        MvPolynomial.eval (fun i ↦ x i) (e v).val ≠ 0 := by
      by_contra h
      push Not at h
      apply hp
      apply MvPolynomial.funext
      intro x
      simpa using h (WithLp.toLp 2 x)
    have ha := AnalyticOnNhd.eval_continuousLinearMap'
      (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) (e v).val
    have hz : volume {x : EuclideanSpace ℝ (Fin N) |
        MvPolynomial.eval (fun i ↦ x i) (e v).val = 0} = 0 := by
      simpa using HolomorphicAnosov.volume_real_analytic_zero_set hN Set.univ
        (fun x ↦ MvPolynomial.eval (fun i ↦ x i) (e v).val)
        isOpen_univ isConnected_univ ha
        (by simpa using hnonzero)
    rw [show ν = volume.comap (Subtype.val : ↥K → EuclideanSpace ℝ (Fin N)) from rfl,
      comap_subtype_coe_apply hK]
    apply measure_mono_null _ hz
    rintro x ⟨y, hy, rfl⟩
    simpa only [Set.mem_ofPred_eq, hT] using hy
  obtain ⟨r, hr, hsmall⟩ := compact_uniform_sublevel ν
    (T '' Metric.sphere (0 : Fin d → ℝ) 1) (hsphere.image T.continuous)
    (ENNReal.ofReal (A / 2)) (by
      rintro f ⟨v, hv, rfl⟩
      exact exists_measure_sublevel_lt_of_zero_set_null ν (T v)
        (T v).continuous.measurable (hzero v hv) _
        (ENNReal.ofReal_pos.mpr (half_pos hA)))
  refine ⟨d, e, r ^ 2 * (A / 2), by positivity, ?_⟩
  intro v hv E hE hEK hmass
  have hsublevel : μ {x | |MvPolynomial.eval (fun i ↦ x i) (e v).val| ≤ r} <
      ENNReal.ofReal (A / 2) := by
    have hs := hsmall (T v) ⟨v, hv, rfl⟩
    have he : (Subtype.val : ↥K → EuclideanSpace ℝ (Fin N)) ''
        {x | |T v x| ≤ r} =
        {x | |MvPolynomial.eval (fun i ↦ x i) (e v).val| ≤ r} ∩ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, y.property⟩
        simpa only [Set.mem_ofPred_eq, hT] using hy
      · rintro ⟨hx, hxK⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        change |T v ⟨x, hxK⟩| ≤ r
        rw [hT]
        exact hx
    rw [show ν = volume.comap (Subtype.val : ↥K → EuclideanSpace ℝ (Fin N)) from rfl,
      comap_subtype_coe_apply hK, he] at hs
    change volume.restrict K _ < _
    rw [Measure.restrict_apply]
    · exact hs
    · exact measurableSet_le
        ((AnalyticOnNhd.eval_continuousLinearMap'
          (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)
          (e v).val).continuous.abs.measurable) measurable_const
  have hEμ : NullMeasurableSet E μ := hE.mono Measure.restrict_le_self
  have hrestrict : μ.restrict E = volume.restrict E :=
    Measure.restrict_restrict_of_subset hEK
  have hmass' : A ≤ μ.real E := by
    have he : μ E = volume E := by
      have he := congrArg (fun η : Measure (EuclideanSpace ℝ (Fin N)) ↦ η Set.univ)
        hrestrict
      simpa only [Measure.restrict_apply_univ] using he
    simpa only [measureReal_def, he] using hmass
  have hb := polynomial_bound (e v).val E hEμ hEK r hr hmass' hsublevel
  simpa only [hrestrict] using hb

end HolomorphicAnosov.Analysis.Regularity
