import HolomorphicAnosov.Analysis.RudinIndicatorMeasure
import HolomorphicAnosov.Analysis.RudinComplexRadonNikodymFinite
import HolomorphicAnosov.MeasureTheory.RudinBoundedComplexUniformSimpleApproximation
import HolomorphicAnosov.MeasureTheory.RudinClosedSetAverageAE
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The finite-measure complex L¹ dual representation

This file states DAG node `analysis.rudin_finite_complex_l1_dual_g1`.
Source: Rudin, *Real and Complex Analysis*, third edition (1987), Theorem 6.16,
printed pp. 127–128, finite-measure case with exponent 1; local source:
`literature/Rudin-Real-and-Complex-Analysis-3rd-1987.pdf`.
The measure is on the original measurable space; no topology or completeness
of that measurable space is assumed. The representative bound is only almost
everywhere, and both integrals and L¹ classes use the same measure.
-/

open MeasureTheory

namespace HolomorphicAnosov

/-- **Finite complex L¹ dual representation.**

Source: Walter Rudin, *Real and Complex Analysis*, third edition (1987),
Theorem 6.16, printed pp. 127–128 (PDF pp. 140–141), finite-measure case
with exponent 1, equations (4)–(6) and Case 1. The supporting results are
complex Radon–Nikodym, Theorem 6.10, pp. 121–123, and the closed-set
average criterion, Theorem 1.40, pp. 30–31. The local source is
`literature/Rudin-Real-and-Complex-Analysis-3rd-1987.pdf`.

Natural-language proof, following the current DAG proof:

1. If the functional is zero, take the original-measurable function zero.
   Otherwise, for each measurable set E, finite measure makes its indicator
   genuinely integrable. Its L¹ class I_E has norm μ.real E, also for null E.
   Addition and complex scalar multiplication of these classes agree almost
   everywhere with the corresponding operations on representatives.

2. Set ν(E) = T(I_E) on measurable sets and zero on nonmeasurable sets.
   Finite disjoint additivity follows from indicator additivity and linearity.
   For a disjoint measurable sequence with union E, the remainders obtained
   by deleting its first n terms decrease to the empty set. Continuity from
   above for the finite measure makes their real measures tend to zero.
   Every finite subunion containing those first n terms has indicator-class
   difference from I_E bounded in norm by that remainder's real measure.
   Thus the finite-subset sums tend to I_E; continuity of T proves the HasSum
   condition for a genuine countably additive complex measure. A μ-null
   measurable set has zero indicator class, so ν is absolutely continuous.

3. Complex Radon–Nikodym gives an original-measurable, genuinely integrable
   function h with ν(E) = ∫_E h. Finite μ provides sigma-finiteness internally;
   the sigma-algebra is not completed or replaced. The indicator integral
   identity gives T(I_E) = ∫ χ_E h, with almost-everywhere representative
   identifications preserving the integral.

4. Expand a finite-valued measurable simple function into its finite sum of
   scalar indicators. Each product with h is integrable, so linearity of T
   and of the integral gives T([s]) = ∫ s h. For a bounded measurable b,
   finite μ makes b integrable and gives its L∞ membership; Hölder first
   proves genuine integrability of b h. Rudin's uniform simple approximation
   s_n to b, with uniform error δ_n tending to zero, gives L¹-class error at
   most δ_n μ.real X and pairing error at most δ_n ∫ ‖h‖. All differences
   and products involved are integrable before integral linearity is used.
   Continuity therefore extends the identity to bounded measurable b.

5. For every measurable E of positive measure,
   |∫_E h| ≤ ‖T‖ μ.real E. Each average of h lies in the closed disk of radius
   ‖T‖. Rudin's average criterion yields ‖h x‖ ≤ ‖T‖ almost everywhere.
   Together with the already established integrability and measurability of
   h, this gives L∞ membership with that bound. For zero μ the bound is
   vacuous and the zero construction already applies.

6. For any genuinely integrable f, Hölder with exponents 1 and ∞ proves
   genuine integrability of f h. The integral pairing has bound
   |∫ f h| ≤ ‖T‖ ∫ ‖f‖. It consequently defines a bounded complex-linear
   functional on L¹: almost-everywhere equal representatives give equal
   product integrals, and integrability justifies addition and scalar rules.
   Simple-function classes are dense in L¹, and this functional agrees with
   T on them by step 4. Continuity gives agreement on every L¹ class,
   including the actual class `hf.toL1 f` of each integrable f.

The empty domain, zero measure, and zero functional are included. Neither an
everywhere bound on h nor uniqueness of its pointwise representative is claimed.
-/
theorem rudin_finite_complex_l1_dual
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : (Lp ℂ 1 μ) →L[ℂ] ℂ) :
    ∃ h : X → ℂ, Measurable h ∧
      (∀ᵐ x ∂μ, ‖h x‖ ≤ ‖T‖) ∧
      ∀ (f : X → ℂ) (hf : Integrable f μ),
        Integrable (fun x => f x * h x) μ ∧
          T (hf.toL1 f) = ∫ x, f x * h x ∂μ := by
  obtain ⟨h, hm, hi, hb, hset⟩ := rudin_indicator_bounded_density μ T
  have hprod (f : X → ℂ) (hf : Integrable f μ) :
      Integrable (fun x ↦ f x * h x) μ :=
    hf.mul_bdd hm.aestronglyMeasurable hb
  have hprodLp (f : Lp ℂ 1 μ) : Integrable (fun x ↦ f x * h x) μ :=
    hprod f (L1.integrable_coeFn f)
  let Blinear : Lp ℂ 1 μ →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f x * h x ∂μ
      map_add' := by
        intro f g
        calc
          _ = ∫ x, (f x * h x + g x * h x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with x hx
            simp only [hx, Pi.add_apply, add_mul]
          _ = _ := integral_add (hprodLp f) (hprodLp g)
      map_smul' := by
        intro c f
        calc
          _ = ∫ x, c • (f x * h x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c f] with x hx
            simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
          _ = _ := integral_smul c _ }
  have hbound (f : Lp ℂ 1 μ) : ‖Blinear f‖ ≤ ‖T‖ * ‖f‖ := by
    calc
      ‖Blinear f‖ ≤ ∫ x, ‖f x * h x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖T‖ * ‖f x‖ ∂μ := by
        apply integral_mono_ae (hprodLp f).norm ((L1.integrable_coeFn f).norm.const_mul _)
        filter_upwards [hb] with x hx
        rw [norm_mul, mul_comm ‖T‖]
        exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = ‖T‖ * ‖f‖ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]
  let B : Lp ℂ 1 μ →L[ℂ] ℂ := Blinear.mkContinuous ‖T‖ hbound
  have hTB : ∀ f : Lp ℂ 1 μ, T f = B f := by
    apply Lp.induction ENNReal.one_ne_top (fun f ↦ T f = B f)
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst]
      have hIc : indicatorConstLp (μ := μ) 1 hs hμs.ne c =
          c • indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℂ) := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs)
          (hμs := hμs.ne) (c := c),
          indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs)
            (hμs := measure_ne_top μ s) (c := (1 : ℂ)),
          Lp.coeFn_smul c (indicatorConstLp (μ := μ) 1 hs
            (measure_ne_top μ s) (1 : ℂ))] with x hxc hxone hxmul
        rw [hxmul, hxc, Pi.smul_apply, hxone]
        by_cases hxs : x ∈ s <;> simp [hxs]
      change T (indicatorConstLp 1 hs hμs.ne c) =
        ∫ x, indicatorConstLp (μ := μ) 1 hs hμs.ne c x * h x ∂μ
      calc
        _ = c * T (indicatorConstLp (μ := μ) 1 hs (measure_ne_top μ s) (1 : ℂ)) := by
          rw [hIc, map_smul, smul_eq_mul]
        _ = c * ∫ x in s, h x ∂μ := by rw [hset s hs]
        _ = ∫ x, s.indicator (fun x ↦ c * h x) x ∂μ := by
          rw [integral_indicator hs, integral_const_mul]
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs)
            (hμs := hμs.ne) (c := c)] with x hx
          rw [hx]
          by_cases hxs : x ∈ s <;> simp [hxs]
    · intro f g hf hg hdisj hTf hTg
      simp only [map_add, hTf, hTg]
    · exact isClosed_eq T.continuous B.continuous
  refine ⟨h, hm, hb, ?_⟩
  intro f hf
  refine ⟨hprod f hf, (hTB (hf.toL1 f)).trans ?_⟩
  change (∫ x, (hf.toL1 f) x * h x ∂μ) = _
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1] with x hx
  rw [hx]

end HolomorphicAnosov

