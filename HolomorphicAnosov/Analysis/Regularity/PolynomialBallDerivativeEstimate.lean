import HolomorphicAnosov.Analysis.Regularity.PolynomialAffineScaling
import HolomorphicAnosov.Analysis.Regularity.EuclideanBallAffineIntegral
import HolomorphicAnosov.Analysis.Regularity.PolynomialUnitBallCoefficientEstimate

/-!
# Polynomial derivatives controlled by ball norms

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], printed pp.140–143, specialized to q=2 and a whole Euclidean ball.
This module formalizes `analysis.polynomial_ball_derivative_estimate`.
Euclidean balls use the L² coordinate norm and `volume` is Euclidean Lebesgue measure.
-/

open MeasureTheory

namespace HolomorphicAnosov

noncomputable section

/-- The total order of a multi-index, as used in Campanato Lemma [2.I]. -/
def polynomialMultiIndexOrder {N : ℕ} (β : Fin N →₀ ℕ) : ℕ :=
  β.sum fun _ k ↦ k

/-- Translate a polynomial by a Euclidean center, substituting `aᵢ + Xᵢ` for `Xᵢ`.
This is an actual polynomial substitution, used in Campanato's affine scaling (2.12). -/
def polynomialTranslate {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ)
    (fun i ↦ MvPolynomial.C (a i) + MvPolynomial.X i) P

/-- The classical partial multi-index derivative of `P` at `a`.
Termwise differentiation of `P(a+x)` gives β! times its β coefficient. Thus this
coefficient formula is precisely D^βP(a), including β=0; it is not a divided derivative.
Source: Campanato Lemma [2.I], derivative-coefficient calculation on printed p.143. -/
def polynomialPartialAt {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (a : EuclideanSpace ℝ (Fin N)) (β : Fin N →₀ ℕ) : ℝ :=
  (β.prod (fun _ k ↦ k.factorial) : ℝ) * (polynomialTranslate P a).coeff β

/-- Campanato Lemma [2.I], printed pp.140–143 (q=2, whole-ball specialization).

D1. Apply the normalized unit-ball coefficient estimate with dimension N and degree n,
obtaining C>0. Its source proof uses the Euclidean monomial-coefficient unit sphere,
the continuous squared integral with fixed weight 1, a positive minimum, homogeneity,
and the finite factorial bound from Campanato (2.3)--(2.11). Set
v=sqrt(volume(B(0,1))) and K=C max(1,v), so K≥C and K≥Cv.

D2. For a center a and radius ρ>0, polynomial affine scaling supplies Q(x)=P(a+ρx)
of degree at most n. Its β coefficient is ρ^|β| times the β coefficient of P(a+X),
so |β! coeff(Q,β)|=ρ^|β||D^βP(a)|. The affine ball integral identity gives
∫_{B(0,1)}|Q|²=ρ^(-N)∫_{B(a,ρ)}|P|². Substitute both identities into the unit-ball
estimate and divide by the positive power ρ^|β|. The square-root and real-power
identities give the exponent -|β|-N/2. Increasing C to K proves the first bound.
This is Campanato (2.12) and the derivative-coefficient calculation on printed p.143.

D3. Polynomial evaluation is continuous. Its square is bounded on the compact closed
ball, and the open ball has finite volume; domination by an integrable constant
therefore gives integrability on the open ball. If |P|≤M there and M≥0, monotonicity
of the integral gives ∫|P|²≤M² volume(B(a,ρ)). Haar ball-volume scaling gives
volume(B(a,ρ))=ρ^N volume(B(0,1)). Taking square roots in this inequality and
substituting into D2 cancels ρ^(-N/2)ρ^(N/2), yielding
|D^βP(a)|≤Cv ρ^(-|β|)M≤K ρ^(-|β|)M.

The zero polynomial, M=0, n=0, β=0, and N=1 are included. No estimate is asserted
at radius zero: the original hypothesis is ρ>0, which justifies every inverse and
real-power cancellation.
-/
theorem polynomial_ball_derivative_estimate (N n : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ), P.totalDegree ≤ n →
        ∀ (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ), 0 < ρ →
          ∀ (β : Fin N →₀ ℕ), polynomialMultiIndexOrder β ≤ n →
            |polynomialPartialAt P a β| ≤
                K * Real.rpow ρ
                  (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
                  Real.sqrt (∫ y in Metric.ball a ρ,
                    |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume) ∧
              ∀ M : ℝ, 0 ≤ M →
                (∀ y ∈ Metric.ball a ρ, |MvPolynomial.eval (fun i ↦ y i) P| ≤ M) →
                |polynomialPartialAt P a β| ≤
                  K * Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ)) * M := by
  have evaluation_continuous (P : MvPolynomial (Fin N) ℝ) :
      Continuous (fun y : EuclideanSpace ℝ (Fin N) ↦ MvPolynomial.eval (fun i ↦ y i) P) := by
    induction P using MvPolynomial.induction_on with
    | C r => simpa only [MvPolynomial.eval_C] using
        (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin N) ↦ r))
    | add P Q hP hQ =>
        convert hP.add hQ using 1
        funext y
        exact MvPolynomial.eval_add
    | mul_X P i hP =>
        simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
        exact hP.mul (EuclideanSpace.proj i).continuous
  have square_integrable (P : MvPolynomial (Fin N) ℝ)
      (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) :
      Integrable (fun y : EuclideanSpace ℝ (Fin N) ↦
        |MvPolynomial.eval (fun i ↦ y i) P| ^ 2) (volume.restrict (Metric.ball a ρ)) := by
    have : IsFiniteMeasure (volume.restrict (Metric.ball a ρ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin N) ↦
        |MvPolynomial.eval (fun i ↦ y i) P| ^ 2) := (evaluation_continuous P).abs.pow 2
    obtain ⟨C, hC⟩ := (isCompact_closedBall a ρ).bddAbove_image hc.continuousOn
    apply (integrable_const C).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
      hC (Set.mem_image_of_mem _ (Metric.ball_subset_closedBall hy))
  have square_integral_bound (P : MvPolynomial (Fin N) ℝ)
      (a : EuclideanSpace ℝ (Fin N)) (ρ M : ℝ)
      (hM : ∀ y ∈ Metric.ball a ρ, |MvPolynomial.eval (fun i ↦ y i) P| ≤ M) :
      (∫ y in Metric.ball a ρ, |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume) ≤
        M ^ 2 * volume.real (Metric.ball a ρ) := by
    have : IsFiniteMeasure (volume.restrict (Metric.ball a ρ)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have h := integral_mono_ae (square_integrable P a ρ)
      (integrable_const (M ^ 2 : ℝ)) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        exact pow_le_pow_left₀ (abs_nonneg _) (hM y hy) 2)
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
      mul_comm] using h
  have square_root_integral_bound (P : MvPolynomial (Fin N) ℝ)
      (a : EuclideanSpace ℝ (Fin N)) (ρ M : ℝ) (hM0 : 0 ≤ M)
      (hM : ∀ y ∈ Metric.ball a ρ, |MvPolynomial.eval (fun i ↦ y i) P| ≤ M) :
      Real.sqrt (∫ y in Metric.ball a ρ, |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume) ≤
        M * Real.sqrt (volume.real (Metric.ball a ρ)) := by
    have h := Real.sqrt_le_sqrt (square_integral_bound P a ρ M hM)
    simpa only [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0] using h
  obtain ⟨C, hC, hest⟩ := polynomial_unit_ball_coefficient_estimate N n hN
  let v := Real.sqrt (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
  let K := C * max 1 v
  have hCK : C ≤ K := by
    exact le_mul_of_one_le_right hC.le (le_max_left _ _)
  have hCvK : C * v ≤ K := mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le
  refine ⟨K, mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro P hP a ρ hρ β hβ
  obtain ⟨Q, hQ, hQeval, hQcoeff⟩ := polynomial_affine_scaling P a ρ
  have hnorm := hest Q (hQ.trans hP) β hβ
  have hcoeff : |(β.prod (fun _ k ↦ k.factorial) : ℝ) * Q.coeff β| =
      ρ ^ polynomialMultiIndexOrder β * |polynomialPartialAt P a β| := by
    rw [hQcoeff]
    change |(β.prod (fun _ k ↦ k.factorial) : ℝ) *
      (ρ ^ polynomialMultiIndexOrder β * (polynomialTranslate P a).coeff β)| = _
    rw [mul_left_comm, abs_mul, abs_of_pos (pow_pos hρ _)]
    rfl
  have hint : (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1,
      |MvPolynomial.eval (fun i ↦ y i) Q| ^ 2 ∂volume) =
      (ρ ^ N)⁻¹ * ∫ y in Metric.ball a ρ,
        |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume := by
    simp_rw [hQeval]
    exact euclidean_ball_affine_integral a ρ hρ
      (fun y ↦ |MvPolynomial.eval (fun i ↦ y i) P| ^ 2)
  rw [hcoeff, hint, Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hρ.le N))] at hnorm
  have hsqrt : Real.sqrt ((ρ ^ N)⁻¹) = Real.rpow ρ (-(N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le,
      ← Real.rpow_mul hρ.le]
    congr 1
    ring
  rw [hsqrt] at hnorm
  have hscale : Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) =
      (ρ ^ polynomialMultiIndexOrder β)⁻¹ * Real.rpow ρ (-(N : ℝ) / 2) := by
    change ρ ^ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) = _
    rw [sub_eq_add_neg, Real.rpow_add hρ, Real.rpow_neg hρ.le, Real.rpow_natCast]
    congr 2
    ring
  have hL2 : |polynomialPartialAt P a β| ≤
      C * Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
        Real.sqrt (∫ y in Metric.ball a ρ,
          |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hρ (polynomialMultiIndexOrder β))).mp
    rw [hscale]
    convert hnorm using 1
    field_simp
  constructor
  · exact hL2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hρ.le _)) (Real.sqrt_nonneg _))
  · intro M hM hbound
    have hv : volume.real (Metric.ball a ρ) =
        ρ ^ N * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos volume a hρ, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hρ.le _)]
      simp [MeasureTheory.measureReal_def]
    have hsqrtv : Real.sqrt (volume.real (Metric.ball a ρ)) =
        Real.rpow ρ ((N : ℝ) / 2) * v := by
      rw [hv, Real.sqrt_mul (pow_nonneg hρ.le _)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      congr 1
      ring
    have hcancel : Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
        Real.rpow ρ ((N : ℝ) / 2) =
        Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ)) := by
      change ρ ^ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
        ρ ^ ((N : ℝ) / 2) = _
      rw [← Real.rpow_add hρ]
      congr 1
      ring
    calc
      |polynomialPartialAt P a β| ≤
          C * Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
            (M * Real.sqrt (volume.real (Metric.ball a ρ))) :=
        hL2.trans (mul_le_mul_of_nonneg_left
          (square_root_integral_bound P a ρ M hM hbound)
          (mul_nonneg hC.le (Real.rpow_nonneg hρ.le _)))
      _ = (C * v) * Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ)) * M := by
        rw [hsqrtv]
        calc
          _ = C * v *
              (Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ) - (N : ℝ) / 2) *
                Real.rpow ρ ((N : ℝ) / 2)) * M := by ring
          _ = _ := by rw [hcancel]
      _ ≤ K * Real.rpow ρ (-(polynomialMultiIndexOrder β : ℝ)) * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCvK (Real.rpow_nonneg hρ.le _)) hM

end
end HolomorphicAnosov
