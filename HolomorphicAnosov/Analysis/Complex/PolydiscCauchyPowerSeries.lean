import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Analysis.Complex.PolydiscBoundaryCauchySeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Cauchy formulas and power series on a polydisc

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012,
Chapter I §3.B, p.22, (3.6)–(3.9) and (3.11). The conversion to a normed-space
analytic certificate follows Heins2024 pp.27–28,31–32 and Kriegl–Michor1997
Lemmas7.13–7.14 pp.84–86. The coordinate space is the existing `ComplexModel`,
with its finite-product maximum norm. All polydisc, integral and coefficient
notions are the explicit definitions in `PolydiscBoundaryCauchySeries`; the
circle-integral recursion has coordinate0 outermost. Only the named theorem's
proof is postponed in Stage2.
-/

namespace HolomorphicAnosov.PolydiscCauchy

open HolomorphicAnosov.PolydiscBoundaryCauchySeries
open scoped BigOperators ENNReal NNReal

/-- A coordinate monomial as an actual continuous multilinear map. Slots
are the finite pairs `(j,k)` with `k < α j`, reindexed by their total number.
The diagonal is the ordinary coordinate monomial; no symmetric-form witness
or analyticity premise is included in this construction. -/
noncomputable def monomialMultilinear {d : ℕ} (α : Fin d → ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (∑ j, α j) ↦ ComplexModel d) ℂ :=
  let e : (Σ j : Fin d, Fin (α j)) ≃ Fin (∑ j, α j) :=
    Fintype.equivOfCardEq (by simp)
  ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Σ j : Fin d, Fin (α j)) ℂ).compContinuousLinearMap (fun j ↦ ContinuousLinearMap.proj j.1)).domDomCongr e

/-- Literal diagonal evaluation of the slot construction. -/
theorem monomialMultilinear_diagonal {d : ℕ} (α : Fin d → ℕ) (y : ComplexModel d) :
    monomialMultilinear α (fun _ ↦ y) = ∏ j, y j ^ α j := by
  classical
  simp [monomialMultilinear, ContinuousMultilinearMap.mkPiAlgebra_apply,
    Fintype.prod_sigma]

/-- Coordinate evaluations have norm at most the original maximum norm.
Thus every slot product has operator norm at most one, also in degree zero. -/
theorem norm_monomialMultilinear_le {d : ℕ} (α : Fin d → ℕ) :
    ‖monomialMultilinear α‖ ≤ 1 := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  simp only [monomialMultilinear, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply,
    norm_prod, one_mul]
  calc
    _ ≤ ∏ j : Σ j : Fin d, Fin (α j),
        ‖v ((Fintype.equivOfCardEq (by simp) :
          (Σ j : Fin d, Fin (α j)) ≃ Fin (∑ j, α j)) j)‖ := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi; exact norm_le_pi_norm _ _
    _ = _ := Fintype.prod_equiv
      (Fintype.equivOfCardEq (by simp) :
        (Σ j : Fin d, Fin (α j)) ≃ Fin (∑ j, α j)) _ _ (fun _ ↦ rfl)

/-- Grouping the concrete coordinate slot maps by total degree. -/
noncomputable def coefficientSeries {d : ℕ} (c : (Fin d → ℕ) → ℂ) :
    FormalMultilinearSeries ℂ (ComplexModel d) ℂ := fun n ↦
  ∑ α ∈ (Finset.Nat.antidiagonalTuple d n).attach,
    c α.1 • (monomialMultilinear α.1).domDomCongr
      (finCongr (Finset.Nat.mem_antidiagonalTuple.mp α.2))

/-- The grouped maps have exactly the original total-degree polynomials as
diagonal values. -/
theorem coefficientSeries_diagonal {d : ℕ} (c : (Fin d → ℕ) → ℂ)
    (n : ℕ) (y : ComplexModel d) :
    coefficientSeries c n (fun _ ↦ y) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d n, c α * ∏ j, y j ^ α j := by
  classical
  simp [coefficientSeries, ContinuousMultilinearMap.domDomCongr_apply,
    monomialMultilinear_diagonal,
    smul_eq_mul]
  exact Finset.sum_attach _ (fun α ↦ c α * ∏ j, y j ^ α j)

/-- The grouping preserves a direct coefficient norm bound; no diagonal
estimate is substituted for a multilinear operator-norm estimate. -/
theorem norm_coefficientSeries_le {d : ℕ} (c : (Fin d → ℕ) → ℂ) (n : ℕ) :
    ‖coefficientSeries c n‖ ≤
      ∑ α ∈ Finset.Nat.antidiagonalTuple d n, ‖c α‖ := by
  classical
  calc
    ‖coefficientSeries c n‖ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ α ∈ (Finset.Nat.antidiagonalTuple d n).attach, ‖c α.1‖ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_smul, ContinuousMultilinearMap.norm_domDomCongr]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_monomialMultilinear_le _)
    _ = _ := Finset.sum_attach _ (fun α ↦ ‖c α‖)

/-- Absolute coordinate sums may be grouped by their finite total-degree
fibres. This is the exact grouping used for the analytic certificate. -/
theorem hasSum_coefficientSeries {d : ℕ} (c : (Fin d → ℕ) → ℂ)
    (y : ComplexModel d) (b : ℂ)
    (hs : HasSum (fun α ↦ c α * ∏ j, y j ^ α j) b) :
    HasSum (fun n ↦ coefficientSeries c n (fun _ ↦ y)) b := by
  classical
  have he := (Finset.Nat.sigmaAntidiagonalTupleEquivTuple d).hasSum_iff.mpr hs
  have hg := he.sigma (fun n ↦ hasSum_fintype
    (fun α : Finset.Nat.antidiagonalTuple d n ↦ c α.1 * ∏ j, y j ^ α.1 j))
  convert hg using 1
  ext n
  rw [coefficientSeries_diagonal]
  exact (Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple d n)
    (fun α ↦ c α * ∏ j, y j ^ α j)).symm

/-- Summability of the same absolute scalar coefficient weights gives a
positive radius for the actual multilinear series. -/
theorem coefficientSeries_radius {d : ℕ} (c : (Fin d → ℕ) → ℂ) (t : ℝ≥0)
    (hs : Summable (fun α ↦ ‖c α‖ * (t : ℝ) ^ (∑ j, α j))) :
    (t : ℝ≥0∞) ≤ (coefficientSeries c).radius := by
  classical
  have he := (Finset.Nat.sigmaAntidiagonalTupleEquivTuple d).summable_iff.mpr hs
  have hg := he.hasSum.sigma (fun n ↦ hasSum_fintype
    (fun α : Finset.Nat.antidiagonalTuple d n ↦
      ‖c α.1‖ * (t : ℝ) ^ (∑ j, α.1 j)))
  have hsum : Summable (fun n ↦
      (∑ α ∈ Finset.Nat.antidiagonalTuple d n, ‖c α‖) * (t : ℝ) ^ n) := by
    convert hg.summable using 1
    ext n
    rw [Finset.sum_mul]
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.Nat.mem_antidiagonalTuple.mp α.2]
  apply FormalMultilinearSeries.le_radius_of_summable
  exact Summable.of_nonneg_of_le (fun n ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_right (norm_coefficientSeries_le c n) (by positivity)) hsum

/-- Coordinate updates stay inside the original closed polydisc. This is the
actual domain guard in Demailly I§3.B (3.8), p.22, including boundary values. -/
theorem update_mem_closedPolydisc {d : ℕ} (a z : ComplexModel d) (R : Fin d → ℝ)
    (hz : z ∈ closedPolydisc a R) (j : Fin d) (t : ℂ)
    (ht : ‖t - a j‖ ≤ R j) : Function.update z j t ∈ closedPolydisc a R := by
  intro k
  by_cases h : k = j
  · subst k
    simpa using ht
  · simpa only [Function.update_of_ne h] using hz k

/-- The distinguished boundary is contained in the original closed polydisc. -/
theorem distinguishedBoundary_subset_closedPolydisc {d : ℕ}
    (a : ComplexModel d) (R : Fin d → ℝ) :
    distinguishedBoundary a R ⊆ closedPolydisc a R := by
  intro z hz j
  exact (hz j).le

/-- One-variable Cauchy on the genuine original coordinate slice, including
mixed boundary/interior coordinates. The separate differentiability premise
is used on its actual open preimage and restricted to the contained disk.
Demailly I§3.B, induction for (3.8), p.22. -/
theorem coordinate_cauchy_formula {d : ℕ} (U : Set (ComplexModel d))
    (g : ComplexModel d → ℂ)
    (hseparate : ∀ (z : ComplexModel d) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U))
    (a z : ComplexModel d) (R : Fin d → ℝ)
    (hclosed : closedPolydisc a R ⊆ U) (hz : z ∈ closedPolydisc a R)
    (j : Fin d) (w : ℂ) (hw : ‖w - a j‖ < R j) :
    (∮ t in C(a j, R j), (t - w)⁻¹ * g (Function.update z j t)) =
      (2 * (Real.pi : ℂ) * Complex.I) * g (Function.update z j w) := by
  have hd : DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
      (Metric.closedBall (a j) (R j)) := (hseparate z j).mono (by
    intro t ht
    exact hclosed (update_mem_closedPolydisc a z R hz j t
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using ht)))
  simpa only [smul_eq_mul] using hd.circleIntegral_sub_inv_smul
    (show w ∈ Metric.ball (a j) (R j) by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw)

/-- Iterated circle integration depends only on the same distinguished
boundary. The proof descends the fixed coordinate order, so no Fubini or
nonregular boundary identification is assumed. -/
theorem iteratedCircleIntegral_congr (d : ℕ) (a : ComplexModel d)
    (R : Fin d → ℝ) (hR : ∀ j, 0 ≤ R j) (F G : ComplexModel d → ℂ)
    (hFG : Set.EqOn F G (distinguishedBoundary a R)) :
    iteratedCircleIntegral d a R F = iteratedCircleIntegral d a R G := by
  induction d with
  | zero =>
      apply hFG
      intro j
      exact Fin.elim0 j
  | succ n ih =>
      apply circleIntegral.integral_congr (hR 0)
      intro z hz
      apply ih (fun j ↦ a j.succ) (fun j ↦ R j.succ) (fun j ↦ hR j.succ)
      intro ζ hζ
      apply hFG
      intro j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simpa only [Fin.cons_zero, Metric.mem_sphere, dist_eq_norm] using hz
      · simpa only [Fin.cons_succ] using hζ k

/-- Cons and update preserve the original finite coordinate labels. -/
theorem cons_update_tail {n : ℕ} (z t : ℂ) (ζ : ComplexModel n) (j : Fin n) :
    (Fin.cons z (Function.update ζ j t) : ComplexModel (n + 1)) = Function.update (Fin.cons z ζ : ComplexModel (n + 1)) j.succ t := by
  ext k
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · by_cases h : i = j
    · subst i
      simp
    · simp [h, Fin.succ_inj]

/-- The written finite-coordinate Cauchy induction, with coordinate zero
outermost, on the SAME original separately holomorphic function. This theorem
also covers dimension zero for the induction base; the public theorem keeps
its exact d≥1 guard. No holomorphy of an integrated function is needed. -/
theorem iterated_cauchy_formula (d : ℕ) (U : Set (ComplexModel d)) (hU : IsOpen U)
    (g : ComplexModel d → ℂ) (hg : ContinuousOn g U)
    (hseparate : ∀ (z : ComplexModel d) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U))
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (hclosed : closedPolydisc a R ⊆ U) (w : ComplexModel d)
    (hw : w ∈ openPolydisc a R) :
    iteratedCircleIntegral d a R (fun ζ ↦ g ζ * kernel ζ w) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ d * g w := by
  induction d with
  | zero =>
      simp only [iteratedCircleIntegral, kernel, Finset.univ_eq_empty,
        Finset.prod_empty, pow_zero, one_mul, mul_one]
      congr 1
      ext j
      exact Fin.elim0 j
  | succ n ih =>
      let B : ℂ := 2 * (Real.pi : ℂ) * Complex.I
      let wt : ComplexModel n := fun j ↦ w j.succ
      let ac : ComplexModel n := fun j ↦ a j.succ
      let Rt : Fin n → ℝ := fun j ↦ R j.succ
      have htR : ∀ j, 0 < Rt j := fun j ↦ hR j.succ
      have hwt : wt ∈ openPolydisc ac Rt := fun j ↦ hw j.succ
      have htail (z : ℂ) (hz : ‖z - a 0‖ = R 0) :
          iteratedCircleIntegral n ac Rt
            (fun ζ ↦ g (Fin.cons z ζ : ComplexModel (n + 1)) * kernel ζ wt) = B ^ n * g (Fin.cons z wt) := by
        let Ut : Set (ComplexModel n) := (fun ζ : ComplexModel n ↦ (Fin.cons z ζ : ComplexModel (n + 1))) ⁻¹' U
        have hcons : Continuous (fun ζ : ComplexModel n ↦ (Fin.cons z ζ : ComplexModel (n + 1))) := by fun_prop
        have hUt : IsOpen Ut := hU.preimage hcons
        have hgt : ContinuousOn (fun ζ ↦ g (Fin.cons z ζ : ComplexModel (n + 1))) Ut :=
          hg.comp hcons.continuousOn (fun _ hζ ↦ hζ)
        have hst : ∀ (ζ : ComplexModel n) (j : Fin n),
            DifferentiableOn ℂ (fun t : ℂ ↦ g ((Fin.cons z (Function.update ζ j t) : ComplexModel (n + 1))))
              ((fun t : ℂ ↦ (Fin.cons z (Function.update ζ j t) : ComplexModel (n + 1))) ⁻¹' U) := by
          intro ζ j
          simpa only [cons_update_tail] using hseparate (Fin.cons z ζ) j.succ
        have hct : closedPolydisc ac Rt ⊆ Ut := by
          intro ζ hζ
          apply hclosed
          intro j
          refine Fin.cases ?_ (fun k ↦ ?_) j
          · simpa only [Fin.cons_zero] using hz.le
          · exact hζ k
        exact ih Ut hUt (fun ζ ↦ g (Fin.cons z ζ : ComplexModel (n + 1))) hgt hst ac Rt htR hct wt hwt
      have hsplit (z : ℂ) (ζ : ComplexModel n) :
          g (Fin.cons z ζ : ComplexModel (n + 1)) * kernel (Fin.cons z ζ) w =
            (z - w 0)⁻¹ * (g (Fin.cons z ζ : ComplexModel (n + 1)) * kernel ζ wt) := by
        simp only [kernel, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          zpow_neg_one, wt]
        ring
      have houter : iteratedCircleIntegral (n + 1) a R (fun ζ ↦ g ζ * kernel ζ w) =
          circleIntegral (fun z ↦ B ^ n * ((z - w 0)⁻¹ * g (Fin.cons z wt)))
            (a 0) (R 0) := by
        simp only [iteratedCircleIntegral]
        apply circleIntegral.integral_congr (hR 0).le
        intro z hz
        have hz' : ‖z - a 0‖ = R 0 := by
          simpa only [Metric.mem_sphere, dist_eq_norm] using hz
        simp_rw [hsplit]
        rw [iteratedCircleIntegral_const_mul, htail z hz']
        ring
      have hwc : w ∈ closedPolydisc a R := fun j ↦ (hw j).le
      have hconsw (z : ℂ) : Fin.cons z wt = Function.update w 0 z := by
        ext j
        refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [wt]
      rw [houter, circleIntegral.integral_const_mul]
      have hc := coordinate_cauchy_formula U g hseparate a w R hclosed hwc 0 (w 0) (hw 0)
      simp_rw [hconsw]
      rw [hc]
      simp only [Function.update_eq_self]
      change B ^ n * (B * g w) = B ^ (n + 1) * g w
      rw [pow_succ]
      ring

/-- Demailly's normalized polydisc Cauchy identity from the literal fixed-order
coordinate induction. The normalization is the original integer power. -/
theorem eq_cauchyTransform_of_separate {d : ℕ}
    (U : Set (ComplexModel d)) (hU : IsOpen U) (g : ComplexModel d → ℂ)
    (hg : ContinuousOn g U)
    (hseparate : ∀ (z : ComplexModel d) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U))
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (hclosed : closedPolydisc a R ⊆ U) (w : ComplexModel d)
    (hw : w ∈ openPolydisc a R) : g w = cauchyTransform a R g w := by
  have hB : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [cauchyTransform, iterated_cauchy_formula d U hU g hg hseparate a R hR hclosed w hw,
    zpow_neg, zpow_natCast, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hB), one_mul]

/-- The norm of an actual scalar series term is the coordinate product norm;
no Euclidean/sup-norm identity or enumeration of multi-indices is used. -/
theorem norm_seriesTerm {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (g : ComplexModel d → ℂ) (w : ComplexModel d) (α : Fin d → ℕ) :
    ‖seriesTerm a R g w α‖ = ‖coefficient a R g α‖ * ∏ j, ‖w j - a j‖ ^ α j := by
  simp [seriesTerm, monomial, norm_prod, norm_pow]

/-- Absolute uniform convergence on a smaller closed polydisc. The original
boundary theorem supplies summability at a strictly larger interior point;
coordinate norm monotonicity makes those actual term norms a summable uniform
majorant on the smaller polydisc, including zero coordinate radii. -/
theorem absolute_uniform_series {d : ℕ} (hd : 1 ≤ d)
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (g : ComplexModel d → ℂ) (hg : ContinuousOn g (distinguishedBoundary a R))
    (r : Fin d → ℝ) (hr : ∀ j, 0 ≤ r j ∧ r j < R j) :
    SummableUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ ‖seriesTerm a R g w α‖)
      (closedPolydisc a r) := by
  let s : Fin d → ℝ := fun j ↦ (r j + R j) / 2
  let w₀ : ComplexModel d := fun j ↦ a j + (s j : ℂ)
  have hs : ∀ j, 0 ≤ s j ∧ r j ≤ s j ∧ s j < R j := by
    intro j
    dsimp [s]
    constructor
    · linarith [(hr j).1, hR j]
    · constructor <;> linarith [(hr j).2]
  have hw₀norm (j : Fin d) : ‖w₀ j - a j‖ = s j := by
    simp only [w₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hs j).1]
  have hw₀ : w₀ ∈ openPolydisc a R := by
    intro j
    rw [hw₀norm]
    exact (hs j).2.2
  have hsum := (polydisc_boundary_cauchy_series hd a R hR g hg).2.1 w₀ hw₀ |>.1
  have hbound : ∀ (α : Fin d → ℕ) (w : ComplexModel d), w ∈ closedPolydisc a r →
      ‖‖seriesTerm a R g w α‖‖ ≤ ‖seriesTerm a R g w₀ α‖ := by
    intro α w hw
    rw [norm_norm, norm_seriesTerm, norm_seriesTerm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.prod_le_prod₀ (fun j _ ↦ by positivity)
    intro j _
    apply pow_le_pow_left₀ (norm_nonneg _) ((hw j).trans _)
    rw [hw₀norm]
    exact (hs j).2.1
  exact (hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    (tendstoUniformlyOn_tsum hsum hbound)).summableUniformlyOn

/-- All integral, coefficient and unconditional-series conclusions of the
public theorem, assembled from the genuine finite-coordinate Cauchy formula
and its named boundary-series provider. The multivariate multilinear analytic
certificate is deliberately a separate conclusion, not assumed here. -/
theorem cauchy_and_series_conclusions
    {d : ℕ} (hd : 1 ≤ d) (U : Set (ComplexModel d)) (hU : IsOpen U)
    (g : ComplexModel d → ℂ) (hg : ContinuousOn g U)
    (hseparate : ∀ (z : ComplexModel d) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U))
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (hclosed : closedPolydisc a R ⊆ U) :
    (∀ w ∈ openPolydisc a R, g w = cauchyTransform a R g w) ∧
    (∀ w ∈ openPolydisc a R,
      HasSum (seriesTerm a R g w) (g w) ∧
      Summable (fun α : Fin d → ℕ ↦ ‖seriesTerm a R g w α‖) ∧
      g w = ∑' α : Fin d → ℕ, seriesTerm a R g w α) ∧
    (∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j < R j) →
      HasSumUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α) g
        (closedPolydisc a r) ∧
      SummableUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α)
        (closedPolydisc a r) ∧
      SummableUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ ‖seriesTerm a R g w α‖)
        (closedPolydisc a r)) ∧
    (∀ α : Fin d → ℕ,
      ‖coefficient a R g α‖ ≤ boundaryMaximum a R g * ∏ j, (R j) ^ (-(α j : ℤ))) := by
  have hc := eq_cauchyTransform_of_separate U hU g hg hseparate a R hR hclosed
  have hbd : ContinuousOn g (distinguishedBoundary a R) :=
    hg.mono ((distinguishedBoundary_subset_closedPolydisc a R).trans hclosed)
  obtain ⟨hbound, hpoint, huniform, _⟩ := polydisc_boundary_cauchy_series hd a R hR g hbd
  refine ⟨hc, ?_, ?_, hbound.2.2.2⟩
  · intro w hw
    obtain ⟨hs, heq⟩ := hpoint w hw
    have hgw : g w = ∑' α, seriesTerm a R g w α := (hc w hw).trans heq
    exact ⟨hgw ▸ hs.of_norm.hasSum, hs, hgw⟩
  · intro r hr
    have hsm : HasSumUniformlyOn
        (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α)
        (cauchyTransform a R g) (closedPolydisc a r) :=
      hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr (huniform r hr)
    have hsg : HasSumUniformlyOn
        (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α)
        g (closedPolydisc a r) := hsm.congr_right (by
      intro w hw
      exact (hc w (fun j ↦ (hw j).trans_lt (hr j).2)).symm)
    exact ⟨hsg, hsg.summableUniformlyOn, absolute_uniform_series hd a R hR g hbd r hr⟩

/-- Convert the actual absolutely convergent coordinate expansion to the
normed-space analytic certificate. Slot maps give direct multilinear norm
bounds; grouping absolute weights supplies a positive convergence radius.
This avoids treating a coordinate series as a formal multilinear series by
notation alone. -/
theorem analyticAt_of_coordinate_series {d : ℕ} (hd : 1 ≤ d)
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (g : ComplexModel d → ℂ)
    (hs : ∀ w ∈ openPolydisc a R,
      HasSum (seriesTerm a R g w) (g w) ∧
      Summable (fun α : Fin d → ℕ ↦ ‖seriesTerm a R g w α‖) ∧
      g w = ∑' α, seriesTerm a R g w α) : AnalyticAt ℂ g a := by
  classical
  have hn : (Finset.univ.image R).Nonempty := by
    exact Finset.Nonempty.image ⟨⟨0, hd⟩, Finset.mem_univ _⟩ _
  let m : ℝ := (Finset.univ.image R).min' hn
  have hm : 0 < m := by
    obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp (Finset.min'_mem _ hn)
    change 0 < (Finset.univ.image R).min' hn
    rw [← hjm]
    exact hR j
  have hmR : ∀ j, m ≤ R j := fun j ↦
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  let t : ℝ≥0 := ⟨m / 2, by positivity⟩
  have ht : 0 < (t : ℝ) := by
    change 0 < m / 2
    exact div_pos hm (by norm_num)
  have htR : ∀ j, (t : ℝ) < R j := fun j ↦
    lt_of_lt_of_le (by change m / 2 < m; linarith) (hmR j)
  let w₀ : ComplexModel d := fun j ↦ a j + (t : ℝ)
  have hw₀ : w₀ ∈ openPolydisc a R := by
    intro j
    simpa [w₀, abs_of_pos ht] using htR j
  have hweights : Summable (fun α : Fin d → ℕ ↦
      ‖coefficient a R g α‖ * (t : ℝ) ^ (∑ j, α j)) := by
    convert (hs w₀ hw₀).2.1 using 1
    ext α
    rw [norm_seriesTerm]
    simp only [w₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    rw [Finset.prod_pow_eq_pow_sum]
  let p := coefficientSeries (coefficient a R g)
  have hp : (t : ℝ≥0∞) ≤ p.radius := coefficientSeries_radius _ t hweights
  apply HasFPowerSeriesOnBall.analyticAt
  refine ⟨hp, by exact_mod_cast ht, ?_⟩
  intro y hy
  have hynorm : ‖y‖ < (t : ℝ) := by
    simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using hy
  have hyR : a + y ∈ openPolydisc a R := by
    intro j
    simp only [Pi.add_apply, add_sub_cancel_left]
    exact (norm_le_pi_norm y j).trans_lt (hynorm.trans (htR j))
  have hg := (hs (a + y) hyR).1
  have hterms : HasSum (fun α ↦ coefficient a R g α * ∏ j, y j ^ α j)
      (g (a + y)) := by
    convert hg using 1
    ext α
    simp only [seriesTerm, monomial, Pi.add_apply, add_sub_cancel_left]
  exact hasSum_coefficientSeries _ _ _ hterms

/-- Cauchy's formula, its multi-index power series, and complex analyticity from continuous
separate holomorphy. Source and complete natural-language proof of DAG node
`analysis.polydisc_cauchy_power_series` follow. No joint differentiability or analyticity is
an input. Uniform convergence uses the net of all finite multi-index partial sums.

Source: Demailly, Complex Analytic and Differential Geometry, locally obtained June 21, 2012
version, Chapter I §3.B, printed p.22: definitions (3.6)–(3.7), Cauchy formula (3.8),
geometric-kernel expansion and coefficient formula (3.9), and the ensuing holomorphic iff C-analytic
conclusion; derivative estimate (3.11) on p.22. Continuity and separate holomorphy are the
definition of O(U) at the start of §3.B. The final conversion of the coordinate expansion to a
positive-radius continuous multilinear expansion follows the written proofs in Heins, Holomorphic
Perspective on Strict Deformation Quantization, 2024, Example2.1.1 and equation(2.1.3),
Proposition2.1.2 and Corollary2.1.3, printed pp.27–28 (PDF pp.32–33), and Corollary2.1.7, printed
pp.31–32 (PDF pp.36–37); and Kriegl–Michor, The Convenient Setting of Global Analysis, 1997,
Lemma7.13, printed pp.84–85 (PDF pp.90–91), and Lemma7.14, printed pp.85–86 (PDF pp.91–92),
specifically its written (1)⇒(3)⇒(4) Baire/polarization proof.

Step 1. Write B=2πi≠0. For any coordinate j and any fixed values of the other coordinates in their
closed coordinate disks, the map t↦update z j t carries the closed disk |t−a_j|≤R_j into
Pbar(a,R)⊆U. The preimage of U is open and contains this closed disk. By the assumed slice
differentiability on that open preimage, restriction gives DifferentiableOn ℂ of the slice on the
closed disk; continuity follows also by composing g|U with the coordinate-update map. For
|w_j−a_j|<R_j the one-variable theorem gives f(w_j)=B^(−1)∮_{C(a_j,R_j)}f(ζ_j)/(ζ_j−w_j) dζ_j. This
statement applies when some other coordinate values already lie on their circles, since the closed
polydisc is contained in U.

Step 2. Start with g(w) for w∈P(a,R), and use step1 in coordinate0, obtaining the first outer
integral. Inside that integral apply step1 pointwise to coordinate1 with coordinate0 fixed at ζ_0;
pull B^(−1) and the coordinate0 kernel outside the inner coordinate1 integral by
circleIntegral.integral_smul. Continue in coordinates2,…,d−1. At each stage one applies Cauchy to a
slice of the original g, not to an already integrated function, so holomorphy of parameter-dependent
integrals is never assumed. All original mixed boundary/interior slices and kernel products are
continuous and circle-integrable. The induction invariant is the first k successive outer circle
integrals of g(ζ_0,…,ζ_(k−1),w_k,…,w_(d−1)) times ∏_{j<k}(ζ_j−w_j)^(−1), normalized by B^(−k). At
k=d it is exactly B^(−d) I_R(g(ζ)∏j(ζ_j−w_j)^(−1)). This is Demailly(3.8), with coordinate0
outermost and no exchange of integration order. Partial-integral continuity/integrability is the
compact-circle argument included in the boundary-series child.

Step 3. Because Γ⊆Pbar(a,R)⊆U, the restriction of g to Γ is continuous. Apply the boundary
Cauchy-series theorem to h=g. Its coefficient integrals are literally the c_α in this proposition,
with the same circle order and normalization. It gives the multi-index HasSum equal to the
integrated kernel, coefficient estimate |c_α|≤M∏jR_j^(−α_j), absolute summability, and uniform
convergence on each Pbar(a,r) with 0≤r_j<R_j. Step2 identifies its integrated kernel with g(w). This
is Demailly(3.9) and the estimate corresponding to (3.11), with all uniform-convergence details
retained in the substantive child.

Step 4. Follow the actual Heins symmetric-form construction and Kriegl–Michor Lemma7.14 (1)⇒(3)⇒(4),
as follows. Write Rmin=min_j R_j>0; this minimum exists because d≥1 and Fin d is finite. All norms
and neighborhoods below are those of the original finite-product norm on E=Fin d→ℂ.

4a. For n∈ℕ put A_n={α:Fin d→ℕ : ∑jα_j=n} and Q_n(h)=∑_{α∈A_n}c_α∏j h_j^α_j. Every α_j≤n, so A_n is
finite, as a subset of the finite product {0,…,n}^d. For α∈A_n list coordinate j exactly α_j times
in increasing coordinate order to obtain σ_α:Fin n→Fin d. Heins Example2.1.1 gives the actual
complex n-linear monomial B_α(v_0,…,v_(n−1))=∏_{t:Fin n}(v_t)_(σ_α(t)); each input occurs in exactly
one factor. Set B_n=∑_{α∈A_n}c_α B_α and L_n(v)=(1/n!)∑_{σ∈Perm(Fin n)}B_n(v∘σ), exactly
Heins(2.1.3). Coordinate maps, finite products and finite sums are continuous, so these maps are
continuous. Alternatively the explicit pointwise estimate |B_n(v)|≤(∑_{α∈A_n}|c_α|)∏t‖v_t‖, and the
same estimate for its permutation average, permit bundling by MultilinearMap.mkContinuous. There is
no unspecified polynomial object: L_n is a specified symmetric complex n-linear map. Since all
permuted diagonal tuples coincide and #(Perm(Fin n))=n!, its diagonal is
L_n(h,…,h)=B_n(h,…,h)=Q_n(h), as in the written proof of Heins Corollary2.1.3. Its continuity also
agrees with Heins Corollary2.1.7. For n=0, A_0 consists of the zero multi-index, and define L_0 on
the unique empty tuple to be c_0, so Q_0(h)=c_0; use no positive-degree polarization formula for
n=0.

4b. If ‖h‖<Rmin, then |h_j|≤‖h‖<R_j for every j, so step3 gives the unconditional multi-index HasSum
equal to g(a+h). Apply HasSum.tsum_fiberwise with the degree function α↦∑jα_j. Each fiber A_n is
finite, so the fiber tsum is precisely Q_n(h). Thus HasSum (n↦Q_n(h)) (g(a+h)) on the open ball
B(0,Rmin). In particular the diagonal series converges there, and this ball is absorbing in E. We
shall use the written complex case of Kriegl–Michor7.14; no real-to-complex extension of a power
series is needed.

4c. Supply the exact Baire hypothesis for this E. FiniteDimensional.finiteDimensional_pi, with K=ℂ
and I=Fin d, gives finite dimensionality over ℂ. Restricting scalars to ℝ uses the actual supporting
instance FiniteDimensional.complexToReal E
(Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:47–49): [AddCommGroup E] [Module ℂ E]
[FiniteDimensional ℂ E] give FiniteDimensional ℝ E. This scalar restriction changes neither the
given norm, topology, nor any L_n. FiniteDimensional.proper_real for that real normed space gives
ProperSpace E; locallyCompact_of_proper gives LocallyCompactSpace E for its original norm-metric
topology; metric separation gives R1Space E. The exact BaireSpace.of_t2Space_locallyCompactSpace
instance with its [R1Space E] [LocallyCompactSpace E] binders now gives BaireSpace E. This is a
finite-dimensional verification of the Baire hypothesis of the printed Fréchet-space proof, not an
assumption of Baire for an arbitrary space.

4d. For positive integers K,r define the closed set D_(K,r)={x∈E:∀n≥1, |Q_n(x)|≤K r^n}. It is closed
because each Q_n is continuous and the scalar norm inequality defines a closed set. These countably
many closed sets cover all E. Indeed, for any x choose a positive integer r so that y=x/r belongs to
B(0,Rmin), using Rmin>0. The series ∑n Q_n(y) converges by4b; its terms are bounded: its ordinary
finite partial sums converge, and Q_n(y) is the difference of two consecutive partial sums, hence
tends to zero and is bounded. Choose a positive integer K bounding their norms. Homogeneity gives
Q_n(x)=r^n Q_n(y), so x∈D_(K,r). Apply dense_iUnion_interior_of_closed to this countable closed
cover in the same topology. E contains 0, so a dense union of interiors cannot be empty. Choose
positive K,r with a nonempty interior and x_0 therein. Choose ε>0 such that x_0+B(0,ε) lies in
D_(K,r), and let V_0=B(0,ε), an absolutely convex neighborhood of0.

4e. Write e=exp(1)>0. The shifted polarization formula Kriegl–Michor7.13(3), for n≥1, is
Q_n(x)=(n^n/n!)∑_{j=0}^n (−1)^(n−j) binom(n,j) Q_n(x_0+(j/n)x).
To spell out the printed finite-combinatorial proof: in7.13(1), expand
L_n(x_0+∑_{i∈S}x_i,…,x_0+∑_{i∈S}x_i) and sum over subsets S with sign (−1)^(n−|S|). Every
multilinear term omitting an x_i cancels between subsets containing and omitting i. Only terms using
each x_i once survive, with n! permutations, giving L_n(x_1,…,x_n). Setting all x_i=x gives7.13(2);
replacing the base point there by n x_0 and pulling out n^n gives7.13(3). For x∈V_0 every x_0+(j/n)x
lies in D_(K,r), hence |Q_n(x)|≤(n^n/n!)2^n K r^n. The exact Real.pow_div_factorial_le_exp with
x=(n:ℝ)≥0 gives n^n/n!≤exp(n). The supporting identity Real.exp_nat_mul (x:ℝ) (n:ℕ),
exp((n:ℝ)*x)=(exp x)^n (Mathlib/Analysis/Complex/Exponential.lean:233–234), at x=1 yields
exp(n)=e^n. Consequently |Q_n(x)|≤K(2re)^n. Put V_1=(1/(2re))V_0. Homogeneity now gives |Q_n(x)|≤K
for every n≥1 and x∈V_1, precisely the printed (1)⇒(3) step.

4f. Apply the printed (3)⇒(4) step using7.13(1) with x_0=0. For x_1,…,x_n∈V_1,
L_n(x_1,…,x_n)=(1/n!)∑_{S⊆Fin n}(−1)^(n−|S|) Q_n(∑_{i∈S}x_i).
For S nonempty of size s, its average s^(−1)∑_{i∈S}x_i belongs to the convex set V_1, so homogeneity
gives |Q_n(∑_{i∈S}x_i)|≤K s^n. For S empty the term is Q_n(0)=0, since n≥1. Therefore
|L_n(x_1,…,x_n)|≤(K/n!)∑_{s=0}^n binom(n,s)s^n≤K 2^n n^n/n!≤K(2e)^n. Put U_0=(1/(2e))V_1.
Multilinearity gives the common bound |L_n(v_1,…,v_n)|≤K for every n≥1 and every tuple with all
v_i∈U_0. Thus one neighborhood controls all arguments of all positive degrees, as required; diagonal
boundedness alone has not been substituted for an operator-norm bound.

4g. Choose δ>0 such that the original closed norm ball of radius δ centered at0 is contained in U_0
(take half of an open ball radius contained in U_0). Set C=max(K,|c_0|)≥0. For n≥1 and a tuple with
no zero argument, put w_i=(δ/‖v_i‖)v_i, regarded as real scalars embedded in ℂ. Then ‖w_i‖=δ, so all
w_i∈U_0, and multilinearity yields |L_n(v)|≤C δ^(−n)∏i‖v_i‖. If any v_i=0 then L_n(v)=0 and the same
estimate holds. For n=0, the empty product is1 and |L_0|=|c_0|≤C, so the estimate holds in that
degree as well. Apply MultilinearMap.mkContinuous with nonnegative bound C δ^(−n) to bundle these
actual maps as p_n:ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ, retaining exactly the same
evaluations. The sequence p is an actual FormalMultilinearSeries ℂ E ℂ.
ContinuousMultilinearMap.opNorm_le_bound gives ‖p_n‖≤C δ^(−n); since δ>0, ‖p_n‖δ^n≤C for every n,
including n=0.

4h. Define ρ=min(Rmin,δ)/2>0. Then ρ<Rmin and ρ≤δ. Let rρ:NNReal be ⟨ρ,ρ≥0⟩ and let r=(rρ:ENNReal).
Since ‖p_n‖≥0 and ρ≤δ, ‖p_n‖ρ^n≤‖p_n‖δ^n≤C. Apply FormalMultilinearSeries.le_radius_of_bound with
this actual NNReal rρ to obtain r≤p.radius. We have 0<r. If h∈eball0 r, finiteness of r and the
norm-metric equality edist(h,0)=ofReal(‖h‖) give ‖h‖<ρ<Rmin. The grouped HasSum from4b and the
literal diagonal equality p_n(h,…,h)=Q_n(h) give HasSum (n↦p_n(h,…,h)) (g(a+h)). This fills exactly
the three HasFPowerSeriesOnBall g p a r fields in the pinned
Mathlib/Analysis/Analytic/Basic.lean:74–79: r≤p.radius, 0<r, and diagonal HasSum for every h in
eball0 r. By its definition at lines95–96, this certificate yields HasFPowerSeriesAt g p a; by
AnalyticAt's existential definition at lines138–139, it yields AnalyticAt ℂ g a. The positive radius
here is existential and source-produced; the former agent child's prescribed ρ=Rmin/(2d) and
explicit M d^n Rmin^(−n) bound are neither used nor asserted. This completes Demailly's analytic
conclusion by the written Heins and Kriegl–Michor proofs and exact Mathlib interfaces, without
assuming joint analyticity.

-/

theorem polydisc_cauchy_power_series
    {d : ℕ} (hd : 1 ≤ d) (U : Set (ComplexModel d)) (hU : IsOpen U)
    (g : ComplexModel d → ℂ) (hg : ContinuousOn g U)
    (hseparate : ∀ (z : ComplexModel d) (j : Fin d),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' U))
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 < R j)
    (hclosed : closedPolydisc a R ⊆ U) :
    (∀ w ∈ openPolydisc a R, g w = cauchyTransform a R g w) ∧
    (∀ w ∈ openPolydisc a R,
      HasSum (seriesTerm a R g w) (g w) ∧
      Summable (fun α : Fin d → ℕ ↦ ‖seriesTerm a R g w α‖) ∧
      g w = ∑' α : Fin d → ℕ, seriesTerm a R g w α) ∧
    (∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j < R j) →
      HasSumUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α) g
        (closedPolydisc a r) ∧
      SummableUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ seriesTerm a R g w α)
        (closedPolydisc a r) ∧
      SummableUniformlyOn (fun α : Fin d → ℕ ↦ fun w ↦ ‖seriesTerm a R g w α‖)
        (closedPolydisc a r)) ∧
    (∀ α : Fin d → ℕ,
      ‖coefficient a R g α‖ ≤ boundaryMaximum a R g * ∏ j, (R j) ^ (-(α j : ℤ))) ∧
    AnalyticAt ℂ g a := by
  obtain ⟨hc, hs, hu, hb⟩ :=
    cauchy_and_series_conclusions hd U hU g hg hseparate a R hR hclosed
  exact ⟨hc, hs, hu, hb, analyticAt_of_coordinate_series hd a R hR g hs⟩


end HolomorphicAnosov.PolydiscCauchy
