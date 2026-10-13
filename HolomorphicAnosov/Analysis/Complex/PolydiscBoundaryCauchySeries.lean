import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Cauchy series for continuous data on a polydisc boundary

Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012
edition, Chapter I §3.B, printed p.22: the geometric-kernel expansion following
(3.8), coefficient formula (3.9), and coefficient estimate (3.11).

DAG node: `analysis.polydisc_boundary_cauchy_series`. The data definitions below
are actual finite-coordinate products and successive Mathlib circle integrals.
Only the named theorem's proof is postponed to Stage3.
-/

namespace HolomorphicAnosov.PolydiscBoundaryCauchySeries

noncomputable section

open scoped BigOperators Topology _root_.Topology

/-- The distinguished boundary, a product of circles, in the original finite-product
complex coordinate model. Source: Demailly I §3.B, (3.8), p.22. -/
def distinguishedBoundary {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ) :
    Set (ComplexModel d) :=
  {ζ | ∀ j, ‖ζ j - a j‖ = R j}

/-- The open polydisc in the original coordinates. Source: Demailly I §3.B, p.22. -/
def openPolydisc {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ) :
    Set (ComplexModel d) :=
  {w | ∀ j, ‖w j - a j‖ < R j}

/-- A closed polydisc; zero component radii are allowed.
Source: the smaller-polydisc convergence in Demailly I §3.B, p.22. -/
def closedPolydisc {d : ℕ} (a : ComplexModel d) (r : Fin d → ℝ) :
    Set (ComplexModel d) :=
  {w | ∀ j, ‖w j - a j‖ ≤ r j}

/-- Successive counterclockwise circle integration, with coordinate 0 outermost.

At dimension `n+1`, the first circle integral surrounds the already integrated
tail coordinates, in increasing order. `Fin.cons` restores the original first
coordinate and its tail. At dimension zero the empty product integral evaluates
the integrand at the unique empty tuple. Mathlib's `circleIntegral` uses
`a + R * exp (θ * I)` for `0 ≤ θ ≤ 2π`; positive radii therefore give the
counterclockwise convention in Demailly (3.8)–(3.9), p.22.
-/
def iteratedCircleIntegral : (d : ℕ) → ComplexModel d → (Fin d → ℝ) →
    (ComplexModel d → ℂ) → ℂ
  | 0, _, _, F => F (fun j => Fin.elim0 j)
  | n + 1, a, R, F =>
      circleIntegral
        (fun z => iteratedCircleIntegral n (fun j => a j.succ)
          (fun j => R j.succ) (fun ζ => F (Fin.cons z ζ)))
        (a 0) (R 0)

/-- The real supremum of the norm of the boundary data. Under the theorem's
positive-radius and continuity hypotheses, this is a nonnegative attained maximum.
Source: the constant `M` in Demailly I §3.B, (3.11), p.22. -/
def boundaryMaximum {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (h : ComplexModel d → ℂ) : ℝ :=
  sSup ((fun ζ => ‖h ζ‖) '' distinguishedBoundary a R)

/-- The monomial centered at `a`. Natural powers retain `0^0 = 1`.
Source: Demailly I §3.B, (3.8)–(3.9), p.22. -/
def monomial {d : ℕ} (a w : ComplexModel d) (α : Fin d → ℕ) : ℂ :=
  ∏ j, (w j - a j) ^ α j

/-- The multi-index term of the geometric Cauchy kernel. All negative exponents
are integer powers. Source: the expansion following Demailly (3.8), p.22. -/
def kernelTerm {d : ℕ} (a ζ w : ComplexModel d) (α : Fin d → ℕ) : ℂ :=
  ∏ j, ((w j - a j) ^ α j * (ζ j - a j) ^ (-((α j : ℤ) + 1)))

/-- The full product Cauchy kernel. Source: Demailly I §3.B, (3.8), p.22. -/
def kernel {d : ℕ} (ζ w : ComplexModel d) : ℂ :=
  ∏ j, (ζ j - w j) ^ (-1 : ℤ)

/-- The Cauchy coefficient of arbitrary continuous boundary data, with the fixed
coordinate order of `iteratedCircleIntegral`. Source: Demailly (3.9), p.22. -/
def coefficient {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (h : ComplexModel d → ℂ) (α : Fin d → ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ (-(d : ℤ)) *
    iteratedCircleIntegral d a R
      (fun ζ => h ζ * ∏ j, (ζ j - a j) ^ (-((α j : ℤ) + 1)))

/-- The boundary Cauchy transform. No analyticity of the boundary datum is built
into its definition. Source: the integral in Demailly (3.8), p.22. -/
def cauchyTransform {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (h : ComplexModel d → ℂ) (w : ComplexModel d) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ (-(d : ℤ)) *
    iteratedCircleIntegral d a R (fun ζ => h ζ * kernel ζ w)

/-- A term of the centered coefficient series. Source: Demailly (3.8)–(3.9), p.22. -/
def seriesTerm {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (h : ComplexModel d → ℂ) (w : ComplexModel d) (α : Fin d → ℕ) : ℂ :=
  coefficient a R h α * monomial a w α

/-- The distinguished boundary is the compact product of its coordinate spheres. -/
theorem boundary_isCompact {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ) :
    IsCompact (distinguishedBoundary a R) := by
  have heq : distinguishedBoundary a R = Set.pi Set.univ
      (fun j ↦ Metric.sphere (a j) (R j)) := by
    ext z
    simp [distinguishedBoundary]
  rw [heq]
  exact isCompact_univ_pi (fun j ↦ isCompact_sphere (a j) (R j))

/-- Positive radii provide a literal boundary point, without a nonempty-dimension premise. -/
theorem boundary_nonempty {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) : (distinguishedBoundary a R).Nonempty := by
  refine ⟨fun j ↦ a j + (R j : ℂ), ?_⟩
  intro j
  simp [Complex.norm_real, abs_of_nonneg (hR j)]

/-- The norm of continuous boundary data attains its actual real supremum. -/
theorem boundaryMaximum_spec {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) (h : ComplexModel d → ℂ)
    (hh : ContinuousOn h (distinguishedBoundary a R)) :
    0 ≤ boundaryMaximum a R h ∧
      (∃ z ∈ distinguishedBoundary a R, ‖h z‖ = boundaryMaximum a R h) ∧
      (∀ z ∈ distinguishedBoundary a R, ‖h z‖ ≤ boundaryMaximum a R h) := by
  obtain ⟨z, hz, heq, hmax⟩ := (boundary_isCompact a R).exists_sSup_image_eq_and_ge
    (boundary_nonempty a R hR) hh.norm
  refine ⟨?_, ⟨z, hz, heq.symm⟩, ?_⟩
  · change 0 ≤ sSup _
    rw [heq]
    exact norm_nonneg _
  · intro w hw
    change ‖h w‖ ≤ sSup _
    rw [heq]
    exact hmax w hw

/-- Repeated one-circle bounds in the specified coordinate order. The estimate
requires no integrability premise, since Mathlib's total integral also satisfies it. -/
theorem iterated_norm_le (d : ℕ) (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) (F : ComplexModel d → ℂ) (C : ℝ) (_hC : 0 ≤ C)
    (hF : ∀ z ∈ distinguishedBoundary a R, ‖F z‖ ≤ C) :
    ‖iteratedCircleIntegral d a R F‖ ≤ (∏ j, 2 * Real.pi * R j) * C := by
  induction d with
  | zero =>
      simpa [iteratedCircleIntegral] using
        hF (fun j ↦ Fin.elim0 j) (by intro j; exact Fin.elim0 j)
  | succ n ih =>
      rw [iteratedCircleIntegral, Fin.prod_univ_succ]
      calc
        _ ≤ (2 * Real.pi * R 0) * ((∏ j : Fin n, 2 * Real.pi * R j.succ) * C) := by
          apply circleIntegral.norm_integral_le_of_norm_le_const (hR 0)
          intro z hz
          apply ih _ _ (fun j ↦ hR j.succ) _
          intro w hw
          apply hF (Fin.cons z w)
          intro j
          refine Fin.cases ?_ (fun k ↦ ?_) j
          · simpa [Metric.mem_sphere, dist_eq_norm] using hz
          · exact hw k
        _ = _ := by ring

/-- Constant scalars commute with the specified iterated circle integral,
without any reordering or parameter-holomorphy premise. -/
theorem _root_.HolomorphicAnosov.PolydiscCauchy.iteratedCircleIntegral_const_mul (d : ℕ) (a : ComplexModel d)
    (R : Fin d → ℝ) (c : ℂ) (F : ComplexModel d → ℂ) :
    iteratedCircleIntegral d a R (fun z ↦ c * F z) =
      c * iteratedCircleIntegral d a R F := by
  induction d with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedCircleIntegral]
      simp_rw [ih]
      exact circleIntegral.integral_const_mul c _ _ _

/-- Absolute summability of finite products of coordinate series, using the
bijection between a successor tuple and its head/tail pair. -/
theorem summable_norm_product (d : ℕ) (f : Fin d → ℕ → ℂ)
    (hf : ∀ j, Summable (fun k ↦ ‖f j k‖)) :
    Summable (fun α : Fin d → ℕ ↦ ‖∏ j, f j (α j)‖) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have ht := ih (fun j ↦ f j.succ) (fun j ↦ hf j.succ)
      have hp := (hf 0).mul_norm ht
      have he := (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).summable_iff
        (f := fun α ↦ ‖∏ j, f j (α j)‖)
      apply he.mp
      apply hp.congr
      intro p
      dsimp only [Function.comp_apply, Fin.consEquiv]
      rw [Fin.prod_univ_succ]
      rfl

/-- The product of absolutely convergent coordinate sums equals the unconditional
sum indexed by all multi-indices. This is a bijective reindexing, not a rectangular limit. -/
theorem tsum_product (d : ℕ) (f : Fin d → ℕ → ℂ)
    (hf : ∀ j, Summable (fun k ↦ ‖f j k‖)) :
    (∏ j, ∑' k, f j k) = ∑' α : Fin d → ℕ, ∏ j, f j (α j) := by
  induction d with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_succ, ih (fun j ↦ f j.succ) (fun j ↦ hf j.succ)]
      rw [tsum_mul_tsum_of_summable_norm (hf 0)
        (summable_norm_product n (fun j ↦ f j.succ) (fun j ↦ hf j.succ))]
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).tsum_eq]
      simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

/-- Complex coordinate geometric sums give the literal reciprocal kernel.
The denominator is nonzero because its norm is the positive boundary radius. -/
theorem kernel_coordinate_hasSum (a z w : ℂ) (R r : ℝ) (hR : 0 < R)
    (hr : 0 ≤ r ∧ r < R) (hz : ‖z - a‖ = R) (hw : ‖w - a‖ ≤ r) :
    Summable (fun k : ℕ ↦ ‖(w - a) ^ k * (z - a) ^ (-((k : ℤ) + 1))‖) ∧
    HasSum (fun k : ℕ ↦ (w - a) ^ k * (z - a) ^ (-((k : ℤ) + 1)))
      ((z - w) ^ (-1 : ℤ)) := by
  have hza : z - a ≠ 0 := by intro he; rw [he, norm_zero] at hz; linarith
  have hq : ‖(w - a) / (z - a)‖ < 1 := by
    rw [norm_div, hz, div_lt_one hR]
    exact hw.trans_lt hr.2
  have heq (k : ℕ) : (w - a) ^ k * (z - a) ^ (-((k : ℤ) + 1)) =
      ((w - a) / (z - a)) ^ k * (z - a)⁻¹ := by
    rw [zpow_neg, zpow_add₀ hza, zpow_natCast, zpow_one, mul_inv_rev, div_pow]
    ring
  simp_rw [heq]
  refine ⟨?_, ?_⟩
  · simpa only [norm_mul] using
      (summable_norm_geometric_of_norm_lt_one hq).mul_right ‖(z - a)⁻¹‖
  · convert (hasSum_geometric_of_norm_lt_one hq).mul_right ((z - a)⁻¹) using 1
    simp only [zpow_neg_one]
    field_simp
    ring

/-- A summable multi-index geometric majorant for all smaller closed polydiscs.
Zero radii are included, so this uses natural powers with `0^0 = 1`. -/
theorem summable_geometric_product {d : ℕ} (q : Fin d → ℝ)
    (hq : ∀ j, 0 ≤ q j ∧ q j < 1) :
    Summable (fun α : Fin d → ℕ ↦ ∏ j, (q j) ^ α j) := by
  have hs := summable_norm_product d (fun j k ↦ (q j : ℂ) ^ k)
    (fun j ↦ by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq j).1] using
        summable_geometric_of_lt_one (hq j).1 (hq j).2)
  simpa only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hq _).1] using hs

/-- The geometric Cauchy kernel has the unconditional multi-index sum on the
original boundary and smaller polydisc; no analyticity of boundary data is used. -/
theorem kernel_series_pointwise {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (z w : ComplexModel d) (hz : z ∈ distinguishedBoundary a R)
    (hw : w ∈ closedPolydisc a r) :
    Summable (fun α : Fin d → ℕ ↦ ‖kernelTerm a z w α‖) ∧
      kernel z w = ∑' α : Fin d → ℕ, kernelTerm a z w α := by
  have hc (j : Fin d) := kernel_coordinate_hasSum (a j) (z j) (w j) (R j) (r j)
    (hR j) (hr j) (hz j) (hw j)
  refine ⟨?_, ?_⟩
  · exact summable_norm_product d
      (fun j k ↦ (w j - a j) ^ k * (z j - a j) ^ (-((k : ℤ) + 1)))
      (fun j ↦ (hc j).1)
  · unfold kernel kernelTerm
    conv_lhs => arg 2; ext j; rw [← (hc j).2.tsum_eq]
    exact tsum_product d _ (fun j ↦ (hc j).1)

/-- The pointwise geometric bound is uniform on the product of the original
boundary and the smaller closed polydisc. -/
theorem kernelTerm_norm_le {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (_hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (z w : ComplexModel d) (hz : z ∈ distinguishedBoundary a R)
    (hw : w ∈ closedPolydisc a r) (α : Fin d → ℕ) :
    ‖kernelTerm a z w α‖ ≤
      (∏ j, (R j)⁻¹) * ∏ j, (r j / R j) ^ α j := by
  unfold kernelTerm
  rw [norm_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro j _
    exact norm_nonneg _
  · intro j _
    rw [norm_mul, norm_pow, norm_zpow, hz j]
    calc
      ‖w j - a j‖ ^ α j * R j ^ (-((α j : ℤ) + 1)) ≤
          r j ^ α j * R j ^ (-((α j : ℤ) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (hR j).le _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hw j) _
      _ = (R j)⁻¹ * (r j / R j) ^ α j := by
        rw [zpow_neg, zpow_add₀ (ne_of_gt (hR j)), zpow_natCast, zpow_one,
          mul_inv_rev, div_pow]
        ring

/-- The arbitrary-index finite-sum net of the kernel converges uniformly on
boundary times smaller closed polydisc, by the summable geometric majorant. -/
theorem kernel_series_uniform {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hr : ∀ j, 0 ≤ r j ∧ r j < R j) :
    TendstoUniformlyOn
      (fun t : Finset (Fin d → ℕ) ↦ fun p : ComplexModel d × ComplexModel d ↦
        ∑ α ∈ t, kernelTerm a p.1 p.2 α)
      (fun p : ComplexModel d × ComplexModel d ↦ kernel p.1 p.2) Filter.atTop
      (distinguishedBoundary a R ×ˢ closedPolydisc a r) := by
  have hq (j : Fin d) : 0 ≤ r j / R j ∧ r j / R j < 1 :=
    ⟨div_nonneg (hr j).1 (hR j).le, (div_lt_one (hR j)).mpr (hr j).2⟩
  have hs := (summable_geometric_product (fun j ↦ r j / R j) hq).mul_left
    (∏ j, (R j)⁻¹)
  have hu := tendstoUniformlyOn_tsum (f := fun α (p : ComplexModel d × ComplexModel d) ↦
    kernelTerm a p.1 p.2 α) (s := distinguishedBoundary a R ×ˢ closedPolydisc a r) hs
    (fun α p hp ↦ kernelTerm_norm_le a R r hR hr p.1 p.2 hp.1 hp.2 α)
  apply hu.congr_right
  intro p hp
  exact (kernel_series_pointwise a R r hR hr p.1 p.2 hp.1 hp.2).2.symm

/-- Dominated convergence on the circle parameter proves continuity of its
integral for compact continuous parameter families. -/
theorem compact_circleIntegral_continuous {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [FirstCountableTopology X] (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (F : X → ℂ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Metric.sphere c R)) :
    Continuous (fun x ↦ circleIntegral (F x) c R) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_sphere c R)).bddAbove_image hF.norm
  have hG : Continuous (fun p : X × ℝ ↦
      circleMap 0 R p.2 * Complex.I * F p.1 (circleMap c R p.2)) := by
    apply Continuous.mul (by fun_prop)
    exact hF.comp_continuous
      (show Continuous (fun p : X × ℝ ↦ (p.1, circleMap c R p.2)) from (by fun_prop))
      (fun p ↦ ⟨Set.mem_univ _, circleMap_mem_sphere c hR p.2⟩)
  unfold circleIntegral
  simp only [deriv_circleMap, smul_eq_mul]
  apply intervalIntegral.continuous_of_dominated_interval
    (F := fun x t ↦ circleMap 0 R t * Complex.I * F x (circleMap c R t))
    (bound := fun _ ↦ R * C)
  · intro x
    exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    apply Filter.Eventually.of_forall
    intro t _
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left
      (hC (Set.mem_image_of_mem _ (show (x, circleMap c R t) ∈ Set.univ ×ˢ Metric.sphere c R from
        ⟨Set.mem_univ _, circleMap_mem_sphere c hR t⟩))) hR
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t _
    have ht : Continuous (fun x : X ↦ F x (circleMap c R t)) :=
      hF.comp_continuous (continuous_id.prodMk continuous_const)
        (fun x ↦ ⟨Set.mem_univ x, circleMap_mem_sphere c hR t⟩)
    exact continuous_const.mul ht

/-- Fixed-order iterated circle integration preserves continuity in compact
parameters by induction, applying the one-circle dominated-convergence theorem. -/
theorem compact_iteratedIntegral_continuous (d : ℕ) {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [FirstCountableTopology X]
    (a : ComplexModel d) (R : Fin d → ℝ) (hR : ∀ j, 0 ≤ R j)
    (F : X → ComplexModel d → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ distinguishedBoundary a R)) :
    Continuous (fun x ↦ iteratedCircleIntegral d a R (F x)) := by
  induction d generalizing X with
  | zero =>
      exact hF.comp_continuous
        (show Continuous (fun x : X ↦ (x, fun j : Fin 0 ↦ Fin.elim0 j)) from (by fun_prop))
        (fun _ ↦ ⟨Set.mem_univ _, by intro j; exact Fin.elim0 j⟩)
  | succ n ih =>
      let S := Metric.sphere (a 0) (R 0)
      have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (a 0) (R 0))
      have ht : Continuous (fun p : X × S ↦ iteratedCircleIntegral n
          (fun j ↦ a j.succ) (fun j ↦ R j.succ) (fun w ↦ F p.1 (Fin.cons p.2.val w))) := by
        apply ih _ _ (fun j ↦ hR j.succ)
        apply hF.comp
          (show ContinuousOn (fun p : (X × S) × ComplexModel n ↦
            (p.1.1, Fin.cons p.1.2.val p.2)) _ from (by fun_prop))
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        intro j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simpa only [Fin.cons_zero, S, Metric.mem_sphere, dist_eq_norm] using p.1.2.property
        · exact hp.2 k
      apply compact_circleIntegral_continuous _ _ (hR 0)
      rw [continuousOn_iff_continuous_domRestrict]
      convert ht.comp (show Continuous (fun p : ↥(Set.univ ×ˢ S) ↦
        (p.val.1, (⟨p.val.2, p.property.2⟩ : S))) from (by fun_prop)) using 1
      rfl

/-- A continuous boundary integrand has a continuous partially integrated head
slice, and hence is integrable on that head circle. -/
theorem boundary_partial_circleIntegrable (d : ℕ) (a : ComplexModel (d + 1))
    (R : Fin (d + 1) → ℝ) (hR : ∀ j, 0 ≤ R j) (F : ComplexModel (d + 1) → ℂ)
    (hF : ContinuousOn F (distinguishedBoundary a R)) :
    CircleIntegrable (fun z ↦ iteratedCircleIntegral d (fun j ↦ a j.succ)
      (fun j ↦ R j.succ) (fun w ↦ F (Fin.cons z w))) (a 0) (R 0) := by
  apply ContinuousOn.circleIntegrable (hR 0)
  rw [continuousOn_iff_continuous_domRestrict]
  have : CompactSpace (Metric.sphere (a 0) (R 0)) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (a 0) (R 0))
  apply compact_iteratedIntegral_continuous d _ _ (fun j ↦ hR j.succ)
  apply hF.comp (show ContinuousOn (fun p : ↥(Metric.sphere (a 0) (R 0)) × ComplexModel d ↦
    Fin.cons p.1.val p.2) _ from (by fun_prop))
  intro p hp j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa only [Fin.cons_zero, Metric.mem_sphere, dist_eq_norm] using p.1.property
  · exact hp.2 k

/-- Subtraction commutes with successive circle integration for continuous
boundary integrands. This proves the actual error identity before estimating it. -/
theorem boundary_integral_sub (d : ℕ) (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) (F G : ComplexModel d → ℂ)
    (hF : ContinuousOn F (distinguishedBoundary a R))
    (hG : ContinuousOn G (distinguishedBoundary a R)) :
    iteratedCircleIntegral d a R (fun z ↦ F z - G z) =
      iteratedCircleIntegral d a R F - iteratedCircleIntegral d a R G := by
  induction d with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedCircleIntegral]
      have hslice (z : ℂ) (hz : z ∈ Metric.sphere (a 0) (R 0))
          (H : ComplexModel (n + 1) → ℂ) (hH : ContinuousOn H (distinguishedBoundary a R)) :
          ContinuousOn (fun w ↦ H (Fin.cons z w))
            (distinguishedBoundary (fun j ↦ a j.succ) (fun j ↦ R j.succ)) := by
        apply hH.comp (by fun_prop)
        intro w hw j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simpa only [Fin.cons_zero, Metric.mem_sphere, dist_eq_norm] using hz
        · exact hw k
      calc
        _ = circleIntegral (fun z ↦ iteratedCircleIntegral n (fun j ↦ a j.succ)
            (fun j ↦ R j.succ) (fun w ↦ F (Fin.cons z w)) -
          iteratedCircleIntegral n (fun j ↦ a j.succ) (fun j ↦ R j.succ)
            (fun w ↦ G (Fin.cons z w))) (a 0) (R 0) := by
          apply circleIntegral.integral_congr (hR 0)
          intro z hz
          exact ih _ _ (fun j ↦ hR j.succ) _ _ (hslice z hz F hF) (hslice z hz G hG)
        _ = _ := circleIntegral.integral_sub
          (boundary_partial_circleIntegrable n a R hR F hF)
          (boundary_partial_circleIntegrable n a R hR G hG)

/-- Finite sums commute with successive integration of continuous boundary
integrands. No reordering of circle coordinates is used. -/
theorem boundary_integral_sum (d : ℕ) (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) {ι : Type*} (t : Finset ι) (F : ι → ComplexModel d → ℂ)
    (hF : ∀ i ∈ t, ContinuousOn (F i) (distinguishedBoundary a R)) :
    iteratedCircleIntegral d a R (fun z ↦ ∑ i ∈ t, F i z) =
      ∑ i ∈ t, iteratedCircleIntegral d a R (F i) := by
  classical
  induction d with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedCircleIntegral]
      have hslice (z : ℂ) (hz : z ∈ Metric.sphere (a 0) (R 0)) (i : ι) (hi : i ∈ t) :
          ContinuousOn (fun w ↦ F i (Fin.cons z w))
            (distinguishedBoundary (fun j ↦ a j.succ) (fun j ↦ R j.succ)) := by
        apply (hF i hi).comp (by fun_prop)
        intro w hw j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simpa only [Fin.cons_zero, Metric.mem_sphere, dist_eq_norm] using hz
        · exact hw k
      calc
        _ = circleIntegral (fun z ↦ ∑ i ∈ t,
          iteratedCircleIntegral n (fun j ↦ a j.succ) (fun j ↦ R j.succ)
            (fun w ↦ F i (Fin.cons z w))) (a 0) (R 0) := by
          apply circleIntegral.integral_congr (hR 0)
          intro z hz
          exact ih _ _ (fun j ↦ hR j.succ) _ (fun i hi ↦ hslice z hz i hi)
        _ = _ := circleIntegral.integral_fun_sum
          (fun i hi ↦ boundary_partial_circleIntegrable n a R hR (F i) (hF i hi))

/-- The normalization cancels the `2π` factors in the fixed-order circle bound. -/
theorem normalized_integral_norm_le {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 ≤ R j) (F : ComplexModel d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ z ∈ distinguishedBoundary a R, ‖F z‖ ≤ C) :
    ‖(2 * (Real.pi : ℂ) * Complex.I) ^ (-(d : ℤ)) * iteratedCircleIntegral d a R F‖ ≤
      (∏ j, R j) * C := by
  rw [norm_mul]
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I) ^ (-(d : ℤ))‖ =
      ((2 * Real.pi) ^ d)⁻¹ := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, zpow_neg, zpow_natCast]
  rw [hn]
  have hb := iterated_norm_le d a R hR F C hC hF
  calc
    _ ≤ ((2 * Real.pi) ^ d)⁻¹ * ((∏ j, 2 * Real.pi * R j) * C) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg Real.two_pi_pos.le _))
    _ = (∏ j, R j) * C := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      field_simp

/-- Cauchy's exact coefficient estimate follows from the boundary maximum and
normalization of the successive-circle bound. -/
theorem coefficient_norm_le {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (h : ComplexModel d → ℂ)
    (hh : ContinuousOn h (distinguishedBoundary a R)) (α : Fin d → ℕ) :
    ‖coefficient a R h α‖ ≤ boundaryMaximum a R h * ∏ j, (R j) ^ (-(α j : ℤ)) := by
  obtain ⟨hM, _, hmax⟩ := boundaryMaximum_spec a R (fun j ↦ (hR j).le) h hh
  have hb := normalized_integral_norm_le a R (fun j ↦ (hR j).le)
    (fun z ↦ h z * ∏ j, (z j - a j) ^ (-((α j : ℤ) + 1)))
    (boundaryMaximum a R h * ∏ j, R j ^ (-((α j : ℤ) + 1)))
    (mul_nonneg hM (Finset.prod_nonneg (fun j _ ↦ zpow_nonneg (hR j).le _)))
    (by
      intro z hz
      simp only [norm_mul, norm_prod, norm_zpow]
      simp_rw [show ∀ j, ‖z j - a j‖ = R j from hz]
      exact mul_le_mul_of_nonneg_right (hmax z hz)
        (Finset.prod_nonneg (fun j _ ↦ zpow_nonneg (hR j).le _)))
  change ‖coefficient a R h α‖ ≤ _ at hb
  calc
    _ ≤ (∏ j, R j) * (boundaryMaximum a R h * ∏ j, R j ^ (-((α j : ℤ) + 1))) := hb
    _ = _ := by
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [zpow_neg, zpow_add₀ (ne_of_gt (hR j)), zpow_natCast, zpow_one,
        mul_inv_rev, zpow_neg, zpow_natCast]
      field_simp [ne_of_gt (hR j)]

/-- The coefficient estimate provides the smaller-polydisc geometric majorant. -/
theorem seriesTerm_norm_le {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (_hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (h : ComplexModel d → ℂ) (hh : ContinuousOn h (distinguishedBoundary a R))
    (w : ComplexModel d) (hw : w ∈ closedPolydisc a r) (α : Fin d → ℕ) :
    ‖seriesTerm a R h w α‖ ≤ boundaryMaximum a R h * ∏ j, (r j / R j) ^ α j := by
  obtain ⟨hM, _, _⟩ := boundaryMaximum_spec a R (fun j ↦ (hR j).le) h hh
  unfold seriesTerm monomial
  rw [norm_mul, norm_prod]
  calc
    _ ≤ (boundaryMaximum a R h * ∏ j, R j ^ (-(α j : ℤ))) *
        ∏ j, ‖(w j - a j) ^ α j‖ :=
      mul_le_mul_of_nonneg_right (coefficient_norm_le a R hR h hh α)
        (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
    _ ≤ (boundaryMaximum a R h * ∏ j, R j ^ (-(α j : ℤ))) *
        ∏ j, r j ^ α j := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hM (Finset.prod_nonneg (fun j _ ↦ zpow_nonneg (hR j).le _)))
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro j _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hw j) _
    _ = _ := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      rw [zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv, mul_comm]

/-- The coefficient sum converges absolutely at every smaller-polydisc point
and uniformly for the net of all finite subsets. -/
theorem coefficient_series_convergence {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (h : ComplexModel d → ℂ) (hh : ContinuousOn h (distinguishedBoundary a R)) :
    (∀ w ∈ closedPolydisc a r, Summable (fun α : Fin d → ℕ ↦ ‖seriesTerm a R h w α‖)) ∧
    TendstoUniformlyOn
      (fun t : Finset (Fin d → ℕ) ↦ fun w ↦ ∑ α ∈ t, seriesTerm a R h w α)
      (fun w ↦ ∑' α : Fin d → ℕ, seriesTerm a R h w α) Filter.atTop (closedPolydisc a r) := by
  have hq (j : Fin d) : 0 ≤ r j / R j ∧ r j / R j < 1 :=
    ⟨div_nonneg (hr j).1 (hR j).le, (div_lt_one (hR j)).mpr (hr j).2⟩
  have hs := (summable_geometric_product (fun j ↦ r j / R j) hq).mul_left
    (boundaryMaximum a R h)
  refine ⟨?_, tendstoUniformlyOn_tsum hs (fun α w hw ↦ seriesTerm_norm_le a R r hR hr h hh w hw α)⟩
  intro w hw
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun α ↦
    seriesTerm_norm_le a R r hR hr h hh w hw α) hs

/-- The interior kernel is continuous in the boundary variable. -/
theorem kernel_continuousOn {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (w : ComplexModel d) (hw : w ∈ openPolydisc a R) :
    ContinuousOn (fun z ↦ kernel z w) (distinguishedBoundary a R) := by
  unfold kernel
  apply continuousOn_finsetProd
  intro j _
  apply ((continuous_apply j).continuousOn.sub continuousOn_const).zpow₀
  intro z hz
  left
  change z j - w j ≠ 0
  intro he
  have heq : z j = w j := sub_eq_zero.mp he
  have hzw := hz j
  rw [heq] at hzw
  linarith [hw j]

/-- Each kernel summand is continuous on the original boundary. -/
theorem kernelTerm_continuousOn {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (w : ComplexModel d) (α : Fin d → ℕ) :
    ContinuousOn (fun z ↦ kernelTerm a z w α) (distinguishedBoundary a R) := by
  unfold kernelTerm
  apply continuousOn_finsetProd
  intro j _
  apply continuousOn_const.mul
  apply ((continuous_apply j).continuousOn.sub continuousOn_const).zpow₀
  intro z hz
  left
  change z j - a j ≠ 0
  intro he
  have hza := hz j
  rw [he, norm_zero] at hza
  linarith [hR j]

/-- Integrating a finite geometric-kernel sum gives exactly the finite sum of
Cauchy coefficients times centered monomials. -/
theorem integrated_finite_kernel_sum {d : ℕ} (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (h : ComplexModel d → ℂ)
    (hh : ContinuousOn h (distinguishedBoundary a R)) (w : ComplexModel d)
    (t : Finset (Fin d → ℕ)) :
    (2 * (Real.pi : ℂ) * Complex.I) ^ (-(d : ℤ)) *
      iteratedCircleIntegral d a R (fun z ↦ h z * ∑ α ∈ t, kernelTerm a z w α) =
      ∑ α ∈ t, seriesTerm a R h w α := by
  classical
  simp_rw [Finset.mul_sum]
  rw [boundary_integral_sum d a R (fun j ↦ (hR j).le) t
    (fun α z ↦ h z * kernelTerm a z w α)
    (fun α _ ↦ hh.mul (kernelTerm_continuousOn a R hR w α)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  have heq : (fun z ↦ h z * kernelTerm a z w α) =
      (fun z ↦ monomial a w α * (h z * ∏ j, (z j - a j) ^ (-((α j : ℤ) + 1)))) := by
    ext z
    simp only [kernelTerm, monomial, Finset.prod_mul_distrib]
    ring
  rw [heq, HolomorphicAnosov.PolydiscCauchy.iteratedCircleIntegral_const_mul]
  unfold seriesTerm coefficient
  ring

/-- The uniform kernel error survives multiplication by continuous boundary
values and fixed-order integration. Finite-sum interchange and subtraction have already
been justified by boundary continuity, so this estimates the actual Cauchy transform. -/
theorem integrated_series_uniform {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (h : ComplexModel d → ℂ) (hh : ContinuousOn h (distinguishedBoundary a R)) :
    TendstoUniformlyOn
      (fun t : Finset (Fin d → ℕ) ↦ fun w ↦ ∑ α ∈ t, seriesTerm a R h w α)
      (cauchyTransform a R h) Filter.atTop (closedPolydisc a r) := by
  classical
  obtain ⟨hM, _, hmax⟩ := boundaryMaximum_spec a R (fun j ↦ (hR j).le) h hh
  let C : ℝ := (∏ j, R j) * boundaryMaximum a R h
  have hC : 0 ≤ C := mul_nonneg (Finset.prod_nonneg (fun j _ ↦ (hR j).le)) hM
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hk := Metric.tendstoUniformlyOn_iff.mp (kernel_series_uniform a R r hR hr) δ hδ
  filter_upwards [hk] with t ht w hw
  have hwo : w ∈ openPolydisc a R := fun j ↦ (hw j).trans_lt (hr j).2
  have hcont : ContinuousOn (fun z ↦ h z * ∑ α ∈ t, kernelTerm a z w α)
      (distinguishedBoundary a R) := by
    apply hh.mul
    exact continuousOn_finsetSum t (fun α _ ↦ kernelTerm_continuousOn a R hR w α)
  have hcontK : ContinuousOn (fun z ↦ h z * kernel z w) (distinguishedBoundary a R) :=
    hh.mul (kernel_continuousOn a R w hwo)
  have herror : ∀ z ∈ distinguishedBoundary a R,
      ‖h z * (∑ α ∈ t, kernelTerm a z w α) - h z * kernel z w‖ ≤
        boundaryMaximum a R h * δ := by
    intro z hz
    rw [← mul_sub, norm_mul]
    have hnorm : ‖(∑ α ∈ t, kernelTerm a z w α) - kernel z w‖ ≤ δ := by
      have := ht (z, w) ⟨hz, hw⟩
      simpa only [dist_eq_norm, norm_sub_rev] using this.le
    exact mul_le_mul (hmax z hz) hnorm (norm_nonneg _) hM
  have hb := normalized_integral_norm_le a R (fun j ↦ (hR j).le)
    (fun z ↦ h z * (∑ α ∈ t, kernelTerm a z w α) - h z * kernel z w)
    (boundaryMaximum a R h * δ) (mul_nonneg hM hδ.le) herror
  rw [boundary_integral_sub d a R (fun j ↦ (hR j).le) _ _ hcont hcontK,
    mul_sub, integrated_finite_kernel_sum a R hR h hh w t] at hb
  change ‖(∑ α ∈ t, seriesTerm a R h w α) - cauchyTransform a R h w‖ ≤ _ at hb
  have hsmall : (∏ j, R j) * (boundaryMaximum a R h * δ) < ε := by
    change (∏ j, R j) * (boundaryMaximum a R h * (ε / (C + 1))) < ε
    rw [← mul_assoc]
    change C * (ε / (C + 1)) < ε
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  simpa only [dist_eq_norm, norm_sub_rev] using hb.trans_lt hsmall

/-- Uniqueness of the two finite-sum-net limits identifies the coefficient sum
with the actual Cauchy transform throughout each smaller closed polydisc. -/
theorem cauchyTransform_eq_tsum {d : ℕ} (a : ComplexModel d) (R r : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hr : ∀ j, 0 ≤ r j ∧ r j < R j)
    (h : ComplexModel d → ℂ) (hh : ContinuousOn h (distinguishedBoundary a R))
    (w : ComplexModel d) (hw : w ∈ closedPolydisc a r) :
    cauchyTransform a R h w = ∑' α : Fin d → ℕ, seriesTerm a R h w α :=
  tendsto_nhds_unique
    ((integrated_series_uniform a R r hR hr h hh).tendsto_at hw)
    ((coefficient_series_convergence a R r hR hr h hh).2.tendsto_at hw)

/-- The boundary Cauchy transform equals its absolutely convergent multi-index
series, uniformly on every smaller closed polydisc, with the precise Cauchy estimate.

Only `ContinuousOn h (distinguishedBoundary a R)` is assumed. All finite sums
are indexed by the directed net of *all* finite subsets of `Fin d → ℕ`, rather
than by a chosen rectangular or total-degree truncation. The kernel conclusion
uses the product set of the original boundary and a smaller closed polydisc.
The theorem asserts no convergence at a coordinate radius equal to `R j`.

Source: Demailly, June 21, 2012 edition, I §3.B, p.22, the geometric expansion
after (3.8), coefficient formula (3.9), and coefficient estimate (3.11).

Full natural-language proof of the DAG node:

1. Each positive-radius circle is nonempty, containing `a j + R j`, and compact.
Their finite product Γ is nonempty and compact. Continuity of h on Γ implies
that its norm attains a finite nonnegative maximum M; this equals the real
supremum in `boundaryMaximum`. Every coefficient and interior-kernel boundary
integrand is continuous, since the boundary denominators never vanish.

2. For a continuous integrand F on Γ, each boundary slice is circle-integrable.
Partial integrals remain continuous in the remaining boundary variables:
parameterize each circle by θ in [0,2π], include its continuous factor
i R exp(iθ), and use uniform continuity on the compact angle/parameter product.
The difference of two integrals is bounded by the supremum of the difference
times the circle length. Compact integrability and integral subtraction justify
the difference before estimating it. Repeating the circle estimate in the
specified order gives |I_R(F)| ≤ (∏j 2πR_j) sup_Γ |F|, without a permutation of
coordinates. For the coefficient integrand, the supremum is at most
M ∏j R_j^(-α_j-1). The normalization has norm (2π)^(-d), so cancellation gives
|c_α| ≤ M ∏j R_j^(-α_j).

3. Given 0 ≤ r_j < R_j, put q_j=r_j/R_j in [0,1). The family
α ↦ ∏j q_j^(α_j) is summable, with sum ∏j (1-q_j)^(-1). Split
Fin(k+1)→ℕ into ℕ × (Fin k→ℕ) inductively, apply each real geometric series,
and use the product-sum theorem for norm-summable families. These are bijective
reindexings of unconditional sums. The argument includes q_j=0 and uses 0^0=1.

4. On Γ × Pbar(a,r), each ratio (w_j-a_j)/(ζ_j-a_j) has norm at most q_j<1.
The complex geometric series times (ζ_j-a_j)^(-1) sums to (ζ_j-w_j)^(-1),
with term norm at most R_j^(-1) q_j^n. Repeated multiplication of absolutely
summable series, and the same finite-index bijections, give the multi-index
kernel identity. Its terms are uniformly bounded by
(∏j R_j^(-1)) ∏j q_j^(α_j). Norm comparison gives absolute summability, and
the arbitrary-index uniform-series theorem gives uniform convergence of the
finite-sum net on this boundary/product set.

5. Multiplication by h preserves uniform convergence, with majorant M times
the preceding bound. Pass finite sums through each circle integral and pull
out the w-monomials; all boundary summands and their partial integrals are
continuous as in step2. The normalized integral of a finite kernel sum is
exactly the finite coefficient sum. Its error is bounded by
(2π)^(-d)(∏j 2πR_j) times the uniform boundary error and tends uniformly to
zero in w. To justify subtraction for the iterated integral, unfold each
circle integral into its angle integral on the compact box [0,2π]^d.
Continuous angle integrands are integrable; the product-integral theorem,
applied by induction on d, identifies the specified successive order, and
integral subtraction supplies the error identity.

6. The coefficient estimate bounds each series term on Pbar(a,r) by
M ∏j q_j^(α_j). The real geometric majorant from step3 gives absolute
summability and uniform convergence of all finite coefficient sums. Uniqueness
of limits identifies their sum with the Cauchy transform from step5. For an
arbitrary w in the open polydisc take r_j=|w_j-a_j|; these radii satisfy all
smaller-polydisc hypotheses. This proves the pointwise identity throughout
the open polydisc, without requiring h to be holomorphic.
-/
theorem polydisc_boundary_cauchy_series
    {d : ℕ} (hd : 1 ≤ d) (a : ComplexModel d) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (h : ComplexModel d → ℂ)
    (hh : ContinuousOn h (distinguishedBoundary a R)) :
    (0 ≤ boundaryMaximum a R h ∧
      (∃ ζ ∈ distinguishedBoundary a R, ‖h ζ‖ = boundaryMaximum a R h) ∧
      (∀ ζ ∈ distinguishedBoundary a R, ‖h ζ‖ ≤ boundaryMaximum a R h) ∧
      (∀ α : Fin d → ℕ, ‖coefficient a R h α‖ ≤
        boundaryMaximum a R h * ∏ j, (R j) ^ (-(α j : ℤ)))) ∧
    (∀ w ∈ openPolydisc a R,
      Summable (fun α : Fin d → ℕ => ‖seriesTerm a R h w α‖) ∧
      cauchyTransform a R h w = ∑' α : Fin d → ℕ, seriesTerm a R h w α) ∧
    (∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j < R j) →
      TendstoUniformlyOn
        (fun t : Finset (Fin d → ℕ) => fun w => ∑ α ∈ t, seriesTerm a R h w α)
        (cauchyTransform a R h) Filter.atTop (closedPolydisc a r)) ∧
    (∀ r : Fin d → ℝ, (∀ j, 0 ≤ r j ∧ r j < R j) →
      (∀ p : ComplexModel d × ComplexModel d,
        p ∈ distinguishedBoundary a R ×ˢ closedPolydisc a r →
        Summable (fun α : Fin d → ℕ => ‖kernelTerm a p.1 p.2 α‖) ∧
        kernel p.1 p.2 = ∑' α : Fin d → ℕ, kernelTerm a p.1 p.2 α) ∧
      TendstoUniformlyOn
        (fun t : Finset (Fin d → ℕ) => fun p : ComplexModel d × ComplexModel d =>
          ∑ α ∈ t, kernelTerm a p.1 p.2 α)
        (fun p : ComplexModel d × ComplexModel d => kernel p.1 p.2) Filter.atTop
        (distinguishedBoundary a R ×ˢ closedPolydisc a r)) := by
  by_cases hd0 : d = 0
  · subst d
    omega
  obtain ⟨hM, hmax, hbound⟩ := boundaryMaximum_spec a R (fun j ↦ (hR j).le) h hh
  refine ⟨⟨hM, hmax, hbound, coefficient_norm_le a R hR h hh⟩, ?_, ?_, ?_⟩
  · intro w hw
    let r : Fin d → ℝ := fun j ↦ ‖w j - a j‖
    have hr : ∀ j, 0 ≤ r j ∧ r j < R j := fun j ↦ ⟨norm_nonneg _, hw j⟩
    have hwr : w ∈ closedPolydisc a r := fun _ ↦ le_rfl
    exact ⟨(coefficient_series_convergence a R r hR hr h hh).1 w hwr,
      cauchyTransform_eq_tsum a R r hR hr h hh w hwr⟩
  · intro r hr
    exact integrated_series_uniform a R r hR hr h hh
  · intro r hr
    exact ⟨fun p hp ↦ kernel_series_pointwise a R r hR hr p.1 p.2 hp.1 hp.2,
      kernel_series_uniform a R r hR hr⟩


end

end HolomorphicAnosov.PolydiscBoundaryCauchySeries

