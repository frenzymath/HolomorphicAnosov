import HolomorphicAnosov.Analysis.Regularity.JourneUniformCoefficientLimits
import HolomorphicAnosov.Analysis.Regularity.JourneMixedMonomial
import HolomorphicAnosov.Analysis.Regularity.JourneLowHighBootstrap
import HolomorphicAnosov.Analysis.Regularity.JourneRegraphProjection
import HolomorphicAnosov.Analysis.Regularity.JourneCrossedGridRemainder
import HolomorphicAnosov.Analysis.Regularity.JourneUniformRechartedSlope
import HolomorphicAnosov.Analysis.Regularity.JourneCompactUniformization
import HolomorphicAnosov.Analysis.Regularity.JourneTransverseMarkedPlaqueCommonCore
import HolomorphicAnosov.Analysis.Regularity.JournePlaqueFirstDerivativeHolder
import HolomorphicAnosov.Analysis.Regularity.JourneInverseDerivativeHolder
import HolomorphicAnosov.Analysis.Regularity.JournePlaqueReceivingCore

/-!
# Journé J2–J11 controlled intermediate-function construction

This module names the remaining construction in
`journe_transverse_leaf_polynomial_approximation`.  Its mathematical source is
Journé, *A Regularity Lemma for Functions of Several Variables* (1988),
pp. 188–192, especially the inverse/reconstruction steps on pp. 188–190 and
the finite coefficient induction (7)–(11) on pp. 191–192.  Journé prints the
scalar two-dimensional argument and explicitly leaves higher-dimensional
modifications implicit; the present proposition records the exact
positive-block-dimensional contract used by the parent, including the common
marked-plaque inverse data and original-coordinate conclusion.

The proof constructs uniform recharted graph families, interpolates on actual
crossed tensor grids, and proves the low/high coefficient recurrence at
geometric physical scales. The limiting degree-n polynomial approximates
the chart function with order n+alpha; composition with the same inverse chart
and the affine-line jet theorem give the stated original-coordinate bounds.
Compactness makes the constants uniform on the original center set.
-/

noncomputable section
namespace HolomorphicAnosov
namespace JourneLeafPolynomialApproximation
open Set
open scoped NNReal

/-- The first inverse-chart coordinate is the fixed frame projection. -/
theorem GraphBox.chart_symm_fst {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (a : Block N) (ha : a ∈ b.image) :
    ((b.chart.symm ⟨a, ha⟩).val).1 = (b.frame.symm (a - b.base)).1 := by
  have h := b.chart_formula (b.chart.symm ⟨a, ha⟩)
  simp only [Homeomorph.apply_symm_apply] at h
  have hcoord := congrArg (fun z ↦ (b.frame.symm (z - b.base)).1) h
  simpa only [add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply] using hcoord.symm

/-- Reconstructing a point from the inverse chart and its plaque. -/
theorem GraphBox.plaque_chart_symm {d c N n : ℕ} {α : ℝ} {Ω : Set (Block N)}
    (b : GraphBox d c N n α Ω) (a : Block N) (ha : a ∈ b.image) :
    b.plaque (b.chart.symm ⟨a, ha⟩).val.2 (b.chart.symm ⟨a, ha⟩).val.1 = a := by
  have h := b.chart_formula (b.chart.symm ⟨a, ha⟩)
  simpa only [Homeomorph.apply_symm_apply, GraphBox.plaque] using h.symm

/-- The leaf coordinate has the Lipschitz bound of the inverse fixed frame. -/
theorem GraphBox.chart_symm_fst_dist_le {d c N n : ℕ} {α : ℝ}
    {Ω : Set (Block N)} (b : GraphBox d c N n α Ω)
    (a y : Block N) (ha : a ∈ b.image) (hy : y ∈ b.image) :
    dist (b.chart.symm ⟨y, hy⟩).val.1 (b.chart.symm ⟨a, ha⟩).val.1 ≤
      ‖b.frame.symm.toContinuousLinearMap‖ * dist y a := by
  rw [b.chart_symm_fst y hy, b.chart_symm_fst a ha, dist_eq_norm, dist_eq_norm]
  have hfst : ‖(b.frame.symm (y-a)).1‖ ≤ ‖b.frame.symm (y-a)‖ := le_max_left _ _
  calc
    _ = ‖(b.frame.symm (y-a)).1‖ := by
      congr 1
      simp only [map_sub, Prod.fst_sub]
      abel
    _ ≤ ‖b.frame.symm (y-a)‖ := hfst
    _ ≤ ‖b.frame.symm.toContinuousLinearMap‖ * ‖y-a‖ :=
      b.frame.symm.toContinuousLinearMap.le_opNorm _

/-- Collect the existing individual monomial bounds in the two degree ranges. -/
theorem weighted_polynomial_top_holder
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {S : Set E} (hS : IsOpen S) {n : ℕ} {α τ t A B : ℝ}
    (d : ι → ℕ) (c : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ n (f i) S)
    (hlow : ∀ i, d i ≤ n → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (f i) x-iteratedFDeriv ℝ n (f i) y‖ ≤ A*‖x-y‖^α)
    (hhigh : ∀ i, n < d i → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (f i) x-iteratedFDeriv ℝ n (f i) y‖ ≤
        (B*t^((d i:ℝ)-τ))*‖x-y‖^α) :
    ContDiffOn ℝ n (fun x ↦ ∑ i, c i*f i x) S ∧
      ∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*f i x) x-
          iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*f i x) y‖ ≤
          (A*lowCoefficientMagnitude d n c+B*highCoefficientMagnitude d n τ t c)*‖x-y‖^α := by
  classical
  let K := fun i ↦ if d i ≤ n then A else B*t^((d i:ℝ)-τ)
  have H := finite_weighted_sum_top_holder_bound hS Finset.univ f c K
    (fun i _ ↦ hf i) (fun i _ ↦ by
      dsimp [K]
      split_ifs with hi
      · exact hlow i hi
      · exact hhigh i (by omega))
  have he : (∑ i, |c i| *K i) = A*lowCoefficientMagnitude d n c+
      B*highCoefficientMagnitude d n τ t c := by
    unfold lowCoefficientMagnitude highCoefficientMagnitude
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [K]
    by_cases hi : d i ≤ n
    · simp only [ite_eq_left hi,ite_eq_right (by omega : ¬ n < d i),mul_zero,add_zero]
      ring
    · simp only [ite_eq_right hi,ite_eq_left (by omega : n < d i),mul_zero,zero_add]
      ring
  simpa only [smul_eq_mul,he] using H

/-- Swapping whole blocks merely reindexes the same finite polynomial. -/
theorem block_polynomial_swap {p q n : ℕ}
    (c : BlockBidegreeIndex p q n → ℝ) (z : Block p × Block q) :
    (∑ i : BlockBidegreeIndex q p n, c i.swap*blockBimonomial i z.swap) =
      ∑ i, c i*blockBimonomial i z := by
  apply Fintype.sum_equiv (Equiv.prodComm _ _)
  intro i
  simp only [Equiv.prodComm_apply,blockBimonomial,Prod.fst_swap,Prod.snd_swap]
  ring

/-- The low and scale-normalized high magnitudes are invariant under swapping blocks. -/
theorem block_coefficient_magnitudes_swap {p q n : ℕ}
    (c : BlockBidegreeIndex p q n → ℝ) (τ t : ℝ) :
    lowCoefficientMagnitude (@blockBidegree q p n) n (fun i ↦ c i.swap) =
      lowCoefficientMagnitude blockBidegree n c ∧
    highCoefficientMagnitude (@blockBidegree q p n) n τ t (fun i ↦ c i.swap) =
      highCoefficientMagnitude blockBidegree n τ t c := by
  classical
  constructor
  · unfold lowCoefficientMagnitude
    apply Fintype.sum_equiv (Equiv.prodComm _ _)
    intro i
    simp only [Equiv.prodComm_apply,blockBidegree,Prod.fst_swap,Prod.snd_swap,Nat.add_comm]
    rfl
  · unfold highCoefficientMagnitude
    apply Fintype.sum_equiv (Equiv.prodComm _ _)
    intro i
    simp only [Equiv.prodComm_apply,blockBidegree,Prod.fst_swap,Prod.snd_swap,Nat.add_comm]
    rfl

/-- The actual residual on a small-slope graph has a low/high coefficient
Hölder bound. The high part carries the small normalized graph factor. -/
theorem graph_polynomial_residual_holder
    {p q n : ℕ} (hn : 1 ≤ n) {α M K ε δ t R r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (_hK : 0 ≤ K)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ) (htM : t*M ≤ δ) (hpowM : t^α*M ≤ δ)
    (φ : Block q → Block p) (f : Block q → ℝ)
    (hφ : HasFiniteHolderBounds n α M φ (Metric.ball 0 r))
    (hf : HasFiniteHolderBounds n α K f (Metric.ball 0 r))
    (hslope : ∀ x ∈ Metric.ball 0 r, ‖fderiv ℝ φ x‖ ≤ ε)
    (hanchor : ‖φ 0‖ ≤ t*R)
    (hm : ∀ z ∈ Metric.ball (0:Block q) R, t • z ∈ Metric.ball 0 r)
    (c : BlockBidegreeIndex p q n → ℝ) :
    let A := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n
    let B := (2:ℝ)^(2*n+1)*(n:ℝ)*((2:ℝ)^(2*n+1)*(R+1))^n*
      ((2:ℝ)^(2*n+1)*(R+1))^n
    let S := (fun x : Block q ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R
    let F := fun x ↦ f x-∑ i, c i*blockBimonomial i (φ x,x)
    ContDiffOn ℝ n F S ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n F x-iteratedFDeriv ℝ n F y‖ ≤
        (K+A*lowCoefficientMagnitude blockBidegree n c+
          (B*δ)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t c)*‖x-y‖^α := by
  classical
  intro A B S F
  have hM0 : 0 ≤ M := by linarith
  have hS : IsOpen S := Metric.isOpen_ball.preimage (continuous_const_smul t⁻¹)
  have hsub : S ⊆ Metric.ball 0 r := by
    intro x hx
    have H := hm (t⁻¹ • x) hx
    simpa only [smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using H
  have hid : HasFiniteHolderBounds n α M (id : Block q → Block q) (Metric.ball 0 r) :=
    (finiteHolderBounds_id_ball n hn α r).mono_bound (max_le (hr1.trans hM) hM)
  have hmon (i : BlockBidegreeIndex p q n) : HasFiniteHolderBounds n α A
      (fun x ↦ blockBimonomial i (φ x,x)) (Metric.ball 0 r) :=
    block_bimonomial_graph_holder_bound hn i Metric.isOpen_ball (convex_ball _ _)
      hα hα1 hM φ id
      (fun j ↦ block_coordinate_holder_bound hM0 Metric.isOpen_ball hφ j)
      (fun j ↦ block_coordinate_holder_bound hM0 Metric.isOpen_ball hid j)
  have hhigh (i : BlockBidegreeIndex p q n) : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) x-
        iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) y‖ ≤
        (B*δ*t^((blockBidegree i:ℝ)-((n:ℝ)+α)))*‖x-y‖^α := by
    have H := small_slope_block_monomial_top_holder hn i Metric.isOpen_ball
      (convex_ball _ _) (Metric.mem_ball_self hr) hα hα1 hM0 hε hδ hδ1 ht ht1 hR
      hεR hεδ htM hpowM φ hφ hslope hanchor hm
    have hbase : 1 ≤ (2:ℝ)^(2*n+1)*(R+1) := by
      have hp : (1:ℝ) ≤ 2^(2*n+1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hdeg : ((i.1.val.sum fun _ e ↦ e : ℕ):ℝ) ≤ (n:ℝ) := by
      exact_mod_cast i.1.property
    have hconst : (2:ℝ)^(2*n+1)*((i.1.val.sum fun _ e ↦ e : ℕ):ℝ)*
        ((2:ℝ)^(2*n+1)*(R+1))^(i.1.val.sum fun _ e ↦ e)*
        ((2:ℝ)^(2*n+1)*(R+1))^(i.2.val.sum fun _ e ↦ e) ≤ B := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hdeg (by positivity)
        · exact pow_le_pow_right₀ hbase i.1.property
        · positivity
        · positivity
      · exact pow_le_pow_right₀ hbase i.2.property
      · positivity
      · positivity
    intro x hx y hy
    apply (H.2 x hx y hy).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    have he : (blockBidegree i:ℝ)-(n:ℝ)-α = (blockBidegree i:ℝ)-((n:ℝ)+α) := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconst hδ)
      (Real.rpow_nonneg ht.le ((blockBidegree i:ℝ)-((n:ℝ)+α)))]
  obtain ⟨hP,hPH⟩ := weighted_polynomial_top_holder hS blockBidegree c
    (fun i x ↦ blockBimonomial i (φ x,x)) (fun i ↦ (hmon i).1.mono hsub)
    (fun i _ x hx y hy ↦ (hmon i).2.2 x (hsub hx) y (hsub hy))
    (fun i _ ↦ hhigh i)
  refine ⟨(hf.1.mono hsub).sub hP,?_⟩
  intro x hx y hy
  have he (z : Block q) (hz : z ∈ S) : iteratedFDeriv ℝ n F z =
      iteratedFDeriv ℝ n f z-iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*blockBimonomial i (φ x,x)) z :=
    iteratedFDeriv_sub_apply (hf.1.contDiffAt (Metric.isOpen_ball.mem_nhds (hsub hz)))
      (hP.contDiffAt (hS.mem_nhds hz))
  rw [he x hx,he y hy]
  have heq : iteratedFDeriv ℝ n f x-
      iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*blockBimonomial i (φ x,x)) x-
      (iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*blockBimonomial i (φ x,x)) y) =
      (iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y)-
      (iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*blockBimonomial i (φ x,x)) x-
        iteratedFDeriv ℝ n (fun x ↦ ∑ i, c i*blockBimonomial i (φ x,x)) y) := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by nlinarith [hf.2.2 x (hsub hx) y (hsub hy),hPH x hx y hy])

/-- The same residual bound on the other family follows by swapping whole blocks. -/
theorem horizontal_graph_polynomial_residual_holder
    {p q n : ℕ} (hn : 1 ≤ n) {α M K ε δ t R r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ) (htM : t*M ≤ δ) (hpowM : t^α*M ≤ δ)
    (φ : Block p → Block q) (f : Block p → ℝ)
    (hφ : HasFiniteHolderBounds n α M φ (Metric.ball 0 r))
    (hf : HasFiniteHolderBounds n α K f (Metric.ball 0 r))
    (hslope : ∀ x ∈ Metric.ball 0 r, ‖fderiv ℝ φ x‖ ≤ ε)
    (hanchor : ‖φ 0‖ ≤ t*R)
    (hm : ∀ z ∈ Metric.ball (0:Block p) R, t • z ∈ Metric.ball 0 r)
    (c : BlockBidegreeIndex p q n → ℝ) :
    let A := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n
    let B := (2:ℝ)^(2*n+1)*(n:ℝ)*((2:ℝ)^(2*n+1)*(R+1))^n*
      ((2:ℝ)^(2*n+1)*(R+1))^n
    let S := (fun x : Block p ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R
    let F := fun x ↦ f x-∑ i, c i*blockBimonomial i (x,φ x)
    ContDiffOn ℝ n F S ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n F x-iteratedFDeriv ℝ n F y‖ ≤
        (K+A*lowCoefficientMagnitude blockBidegree n c+
          (B*δ)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t c)*‖x-y‖^α := by
  intro A B S F
  have H := graph_polynomial_residual_holder hn hα hα1 hM hK hr hr1 hε hδ hδ1
    ht ht1 hR hεR hεδ htM hpowM φ f hφ hf hslope hanchor hm (fun i ↦ c i.swap)
  dsimp only at H
  have he (x : Block p) :
      (∑ i : BlockBidegreeIndex q p n, c i.swap*blockBimonomial i (φ x,x)) =
        ∑ i, c i*blockBimonomial i (x,φ x) := block_polynomial_swap c (x,φ x)
  simp_rw [he] at H
  rw [(block_coefficient_magnitudes_swap c ((n:ℝ)+α) t).1,
    (block_coefficient_magnitudes_swap c ((n:ℝ)+α) t).2] at H
  exact H

/-- Rescale an actual top Hölder estimate to the fixed sampling ball. -/
theorem top_holder_rescale_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {α K t R : ℝ} (ht : 0 < t) (f : E → ℝ)
    (hf : ContDiffOn ℝ n f ((fun x ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R))
    (hH : ∀ x, t⁻¹ • x ∈ Metric.ball (0:E) R →
      ∀ y, t⁻¹ • y ∈ Metric.ball (0:E) R →
      ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤ K*‖x-y‖^α) :
    ContDiffOn ℝ n (fun x ↦ f (t • x)) (Metric.ball 0 R) ∧
      ∀ x ∈ Metric.ball (0:E) R, ∀ y ∈ Metric.ball 0 R,
        ‖iteratedFDeriv ℝ n (fun x ↦ f (t • x)) x-
          iteratedFDeriv ℝ n (fun x ↦ f (t • x)) y‖ ≤
          (t^((n:ℝ)+α)*K)*‖x-y‖^α := by
  have hS : IsOpen ((fun x : E ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R) :=
    Metric.isOpen_ball.preimage (continuous_const_smul t⁻¹)
  have hm (x : E) (hx : x ∈ Metric.ball 0 R) :
      t • x ∈ ((fun x : E ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R) := by
    simpa only [Set.mem_preimage,smul_smul,inv_mul_cancel₀ ht.ne',one_smul] using hx
  refine ⟨hf.comp (contDiffOn_id.const_smul t) (fun _ hx ↦ hm _ hx),?_⟩
  intro x hx y hy
  have H := scalar_rescale_top_holder hS hf hH t 1 (hm x hx) (hm y hy)
  simpa only [one_smul,abs_one,one_mul,abs_of_pos ht,← Real.rpow_natCast,
    ← Real.rpow_add ht] using H

/-- Finite sums add full Hölder bounds. -/
private theorem finite_sum_holder_uniform
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    {n : ℕ} (hn : 1 ≤ n) {α K : ℝ} {S : Set E} (hS : IsOpen S)
    (f : ι → E → F) (hf : ∀ i, HasFiniteHolderBounds n α K (f i) S) :
    HasFiniteHolderBounds n α ((Fintype.card ι:ℝ)*K) (fun x ↦ ∑ i, f i x) S := by
  classical
  have H (s : Finset ι) : HasFiniteHolderBounds n α ((s.card:ℝ)*K)
      (fun x ↦ ∑ i ∈ s, f i x) S := by
    induction s using Finset.induction_on with
    | empty => simpa using finiteHolderBounds_const n hn α S (0:F)
    | @insert i s hi ih =>
      have H := (hf i).add hS ih
      simpa only [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,
        Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using H
  simpa only [Finset.card_univ] using H Finset.univ

/-- Simultaneous dilation of the input and output preserves a graph's slope. -/
private theorem normalized_graph_slope
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {t ε : ℝ} (ht : 0 < t) (f : E → F) (u v : E)
    (hf : ‖f (t • u)-f (t • v)‖ ≤ ε*‖t • u-t • v‖) :
    ‖t⁻¹ • (f (t • u)-f 0)-t⁻¹ • (f (t • v)-f 0)‖ ≤ ε*‖u-v‖ := by
  have he : (f (t • u)-f 0)-(f (t • v)-f 0) = f (t • u)-f (t • v) := by abel
  rw [← smul_sub,he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  calc
    _ ≤ t⁻¹*(ε*‖t • u-t • v‖) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = ε*‖u-v‖ := by
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg ht.le]
      field_simp

/-- The physical graph residual, evaluated at scale `t`, is precisely the
residual function needed by crossed-grid sampling. Its top Hölder constant gains
`t^(n+α)` by scalar rescaling. -/
theorem sampled_horizontal_residual_holder
    {p q n : ℕ} (hn : 1 ≤ n) {α M K ε δ t R r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ) (htM : t*M ≤ δ) (hpowM : t^α*M ≤ δ)
    (φ : Block p → Block q) (g : Block p × Block q → ℝ)
    (hφ : HasFiniteHolderBounds n α M φ (Metric.ball 0 r))
    (hg : HasFiniteHolderBounds n α K (fun u ↦ g (u,φ u)) (Metric.ball 0 r))
    (hslope : ∀ x ∈ Metric.ball 0 r, ‖fderiv ℝ φ x‖ ≤ ε)
    (hanchor : ‖φ 0‖ ≤ t*R)
    (hm : ∀ z ∈ Metric.ball (0:Block p) R, t • z ∈ Metric.ball 0 r)
    (c : BlockBidegreeIndex p q n → ℝ) :
    let A := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n
    let B := (2:ℝ)^(2*n+1)*(n:ℝ)*((2:ℝ)^(2*n+1)*(R+1))^n*
      ((2:ℝ)^(2*n+1)*(R+1))^n
    let F := fun z : Block p × Block q ↦ g (t • z)-∑ i, c i*blockBimonomial i (t • z)
    let Q := fun u : Block p ↦ (u,t⁻¹ • φ (t • u))
    ContDiffOn ℝ n (F ∘ Q) (Metric.ball 0 R) ∧
      ∀ u ∈ Metric.ball (0:Block p) R, ∀ v ∈ Metric.ball 0 R,
        ‖iteratedFDeriv ℝ n (F ∘ Q) u-iteratedFDeriv ℝ n (F ∘ Q) v‖ ≤
          (t^((n:ℝ)+α)*(K+A*lowCoefficientMagnitude blockBidegree n c+
            (B*δ)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t c))*‖u-v‖^α := by
  intro A B F Q
  have H := horizontal_graph_polynomial_residual_holder hn hα hα1 hM hK hr hr1
    hε hδ hδ1 ht ht1 hR hεR hεδ htM hpowM φ (fun u ↦ g (u,φ u)) hφ hg
    hslope hanchor hm c
  dsimp only at H
  have Hscaled := top_holder_rescale_ball ht
    (fun u ↦ g (u,φ u)-∑ i, c i*blockBimonomial i (u,φ u)) H.1 H.2
  have he : F ∘ Q = fun u ↦ g (t • u,φ (t • u))-
      ∑ i, c i*blockBimonomial i (t • u,φ (t • u)) := by
    funext u
    simp only [F,Q,Function.comp_apply,Prod.smul_mk,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  rw [he]
  exact Hscaled

/-- The physical graph residual, evaluated at scale `t`, is precisely the
residual function needed by crossed-grid sampling. Its top Hölder constant gains
`t^(n+α)` by scalar rescaling. -/
theorem sampled_vertical_residual_holder
    {p q n : ℕ} (hn : 1 ≤ n) {α M K ε δ t R r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ) (htM : t*M ≤ δ) (hpowM : t^α*M ≤ δ)
    (φ : Block q → Block p) (g : Block p × Block q → ℝ)
    (hφ : HasFiniteHolderBounds n α M φ (Metric.ball 0 r))
    (hg : HasFiniteHolderBounds n α K (fun u ↦ g (φ u,u)) (Metric.ball 0 r))
    (hslope : ∀ x ∈ Metric.ball 0 r, ‖fderiv ℝ φ x‖ ≤ ε)
    (hanchor : ‖φ 0‖ ≤ t*R)
    (hm : ∀ z ∈ Metric.ball (0:Block q) R, t • z ∈ Metric.ball 0 r)
    (c : BlockBidegreeIndex p q n → ℝ) :
    let A := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n
    let B := (2:ℝ)^(2*n+1)*(n:ℝ)*((2:ℝ)^(2*n+1)*(R+1))^n*
      ((2:ℝ)^(2*n+1)*(R+1))^n
    let F := fun z : Block p × Block q ↦ g (t • z)-∑ i, c i*blockBimonomial i (t • z)
    let Q := fun u : Block q ↦ (t⁻¹ • φ (t • u),u)
    ContDiffOn ℝ n (F ∘ Q) (Metric.ball 0 R) ∧
      ∀ u ∈ Metric.ball (0:Block q) R, ∀ v ∈ Metric.ball 0 R,
        ‖iteratedFDeriv ℝ n (F ∘ Q) u-iteratedFDeriv ℝ n (F ∘ Q) v‖ ≤
          (t^((n:ℝ)+α)*(K+A*lowCoefficientMagnitude blockBidegree n c+
            (B*δ)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t c))*‖u-v‖^α := by
  intro A B F Q
  have H := graph_polynomial_residual_holder hn hα hα1 hM hK hr hr1
    hε hδ hδ1 ht ht1 hR hεR hεδ htM hpowM φ (fun u ↦ g (φ u,u)) hφ hg
    hslope hanchor hm c
  dsimp only at H
  have Hscaled := top_holder_rescale_ball ht
    (fun u ↦ g (φ u,u)-∑ i, c i*blockBimonomial i (φ u,u)) H.1 H.2
  have he : F ∘ Q = fun u ↦ g (φ (t • u),t • u)-
      ∑ i, c i*blockBimonomial i (φ (t • u),t • u) := by
    funext u
    simp only [F,Q,Function.comp_apply,Prod.smul_mk,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  rw [he]
  exact Hscaled

set_option maxHeartbeats 3200000 in
/-- Source-backed J2–J11 proposition: marked transverse plaques and their
common inverse charts produce a smooth intermediate function with controlled
line jets, uniformly over the centre neighborhood.  The conclusion is exactly
the `hconstruction` contract used in the parent theorem. -/
theorem journe_j2_j11_controlled_jet_construction
    {p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    {Ω : Set (Block (p + q))} (_hΩ : IsOpen Ω)
    {α : ℝ} (hαpos : 0 < α) (hαlt : α < 1)
    (F₁ : GraphFoliation p q (p + q) n α Ω)
    (F₂ : GraphFoliation q p (p + q) n α Ω)
    (htransverse : AreTransverse F₁ F₂)
    (h : Block (p + q) → ℝ) (_hh : ContinuousOn h Ω)
    (hh₁ : HasLeafwiseHolderBounds F₁ h)
    (hh₂ : HasLeafwiseHolderBounds F₂ h)
    (i : F₁.Index) (j : F₂.Index) (a₀ : Block (p + q))
    (_hi : a₀ ∈ (F₁.box i).image) (_hj : a₀ ∈ (F₂.box j).image)
    (W : Set (Block (p + q))) (_hW : IsOpen W) (_haW : a₀ ∈ W)
    (hsub : W ⊆ (F₁.box i).image ∩ (F₂.box j).image)
    (rCore ρCore : ℝ) (KCore : ℝ≥0)
    (_hrCore : 0 < rCore) (hρCore : 0 < ρCore) (_hKCore : 0 < KCore)
    (hcores : ∀ a ∈ W,
      ∀ (ha₁ : a ∈ (F₁.box i).image) (ha₂ : a ∈ (F₂.box j).image),
        let z₁ := ((F₁.box i).chart.symm ⟨a, ha₁⟩).val
        let z₂ := ((F₂.box j).chart.symm ⟨a, ha₂⟩).val
        let Ψ := fun z : Block p × Block q ↦
          (F₁.box i).plaque z₁.2 z.1 + (F₂.box j).plaque z₂.2 z.2 - a
        ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p + q)),
          (e : Block p × Block q → Block (p + q)) = Ψ ∧
            e.source = Metric.ball (z₁.1, z₂.1) rCore ∧
          Ψ (z₁.1, z₂.1) = a ∧ Metric.ball a ρCore ⊆ e.target ∧
          Metric.ball a ρCore ⊆ Ω ∧
          (∀ u ∈ Metric.ball a ρCore, ∀ v ∈ Metric.ball a ρCore,
            ‖e.symm u - e.symm v‖ ≤ (KCore : ℝ) * ‖u - v‖) ∧
          ∀ z ∈ e.source,
            (z.1, z₁.2) ∈ Metric.ball 0 (F₁.box i).leafRadius ×ˢ
              Metric.ball 0 (F₁.box i).transverseRadius ∧
            (z.2, z₂.2) ∈ Metric.ball 0 (F₂.box j).leafRadius ×ˢ
              Metric.ball 0 (F₂.box j).transverseRadius) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
      ∀ a ∈ W, ∃ T : (j : Fin (n + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ Block (p + q)) ℝ,
        ∃ k : Block (p + q) → ℝ,
        Metric.ball a r ⊆ Ω ∧ ∀ y ∈ Metric.ball a r,
          |h y - k y| ≤ C * ‖y - a‖ ^ ((n : ℝ) + α) ∧
          let g : ℝ → ℝ := fun t ↦ k (a + t • (y - a))
          ContDiffOn ℝ n g (Set.Icc 0 1) ∧
          (∀ j : ℕ, ∀ hj : j < n,
            iteratedDerivWithin j g (Set.Icc 0 1) 0 =
              T ⟨j, Nat.lt_trans hj (Nat.lt_succ_self n)⟩ (fun _ ↦ y - a)) ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedDerivWithin n g (Set.Icc 0 1) t -
              T ⟨n, Nat.lt_succ_self n⟩ (fun _ ↦ y - a)‖ ≤
                C * ‖y - a‖ ^ ((n : ℝ) + α) := by
  obtain ⟨J₁, hJ₁, hfull₁⟩ := graphBox_plaque_holder_bound (F₁.box i) hn
  have hWbound : W ⊆ Metric.closedBall (0 : Block (p + q)) J₁ := by
    intro a ha
    have hai := (hsub ha).1
    have hw := ((F₁.box i).chart.symm ⟨a, hai⟩).property.2
    have hx := ((F₁.box i).chart.symm ⟨a, hai⟩).property.1
    have hb := (hfull₁ _ hw).2.1 0 (Nat.zero_le n) _ hx
    rw [norm_iteratedFDeriv_zero, GraphBox.plaque_chart_symm] at hb
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  have hWcompact : IsCompact (closure W) :=
    (isCompact_closedBall (0 : Block (p + q)) J₁).of_isClosed_subset isClosed_closure
      (closure_minimal hWbound Metric.isClosed_closedBall)
  have hclosure_balls : ∀ a ∈ closure W, Metric.ball a (ρCore / 2) ⊆ Ω := by
    intro a ha y hy
    obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp ha (ρCore / 2) (half_pos hρCore)
    obtain ⟨_, _, _, _, _, hbΩ, _, _⟩ :=
      hcores b hb (hsub hb).1 (hsub hb).2
    apply hbΩ
    rw [Metric.mem_ball] at hy ⊢
    exact (dist_triangle y a b).trans_lt (by linarith)
  have hclosure_sub : closure W ⊆ Ω := by
    intro a ha
    exact hclosure_balls a ha (Metric.mem_ball_self (half_pos hρCore))
  let P : Block (p + q) → ℝ → ℝ → Prop := fun a C r ↦
    ∃ T : (j : Fin (n + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin j.val ↦ Block (p + q)) ℝ,
      ∃ k : Block (p + q) → ℝ,
      Metric.ball a r ⊆ Ω ∧ ∀ y ∈ Metric.ball a r,
        |h y - k y| ≤ C * ‖y - a‖ ^ ((n : ℝ) + α) ∧
        let g : ℝ → ℝ := fun t ↦ k (a + t • (y - a))
        ContDiffOn ℝ n g (Set.Icc 0 1) ∧
        (∀ j : ℕ, ∀ hj : j < n,
          iteratedDerivWithin j g (Set.Icc 0 1) 0 =
            T ⟨j, Nat.lt_trans hj (Nat.lt_succ_self n)⟩ (fun _ ↦ y - a)) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedDerivWithin n g (Set.Icc 0 1) t -
            T ⟨n, Nat.lt_succ_self n⟩ (fun _ ↦ y - a)‖ ≤
              C * ‖y - a‖ ^ ((n : ℝ) + α)
  have hPmono : ∀ a C D r s, C ≤ D → 0 < s → s ≤ r → P a C r → P a D s := by
    intro a C D r s hCD _ hsr hP
    obtain ⟨T, k, hball, hbound⟩ := hP
    refine ⟨T, k, (Metric.ball_subset_ball hsr).trans hball, ?_⟩
    intro y hy
    obtain ⟨happrox, hsmooth, hjets, htop⟩ := hbound y (Metric.ball_subset_ball hsr hy)
    have hmul : C * ‖y-a‖ ^ ((n : ℝ)+α) ≤ D * ‖y-a‖ ^ ((n : ℝ)+α) :=
      mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg (norm_nonneg _) _)
    exact ⟨happrox.trans hmul, hsmooth, hjets, fun t ht ↦ (htop t ht).trans hmul⟩
  suffices hlocal : ∀ x ∈ closure W, ∃ U : Set (Block (p + q)),
      IsOpen U ∧ x ∈ U ∧ ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ a ∈ U, P a C r by
    obtain ⟨C, r, hC, hr, hglobal⟩ :=
      compact_uniformize_constants_radius hWcompact P hPmono hlocal
    exact ⟨C, hC, r, hr, fun a ha ↦ hglobal a (subset_closure ha)⟩
  intro x hx
  clear * - hp hq hn _hΩ hαpos hαlt F₁ F₂ htransverse h _hh hh₁ hh₂ hclosure_sub hx P
  obtain ⟨i', hi'⟩ := F₁.cover x (hclosure_sub hx)
  obtain ⟨j', hj'⟩ := F₂.cover x (hclosure_sub hx)
  obtain ⟨U, hU, hxU, hsubU, rU, ρU, KU, hrU, hρU, hKU, hcoresU⟩ :=
    transverse_marked_plaque_common_core hp hn F₁ F₂ htransverse i' j' x hi' hj'
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hsource_margins : ∀ a ∈ U,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
        Metric.ball ((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1 rU ⊆
          Metric.ball 0 (F₁.box i').leafRadius ∧
        Metric.ball ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1 rU ⊆
          Metric.ball 0 (F₂.box j').leafRadius := by
    intro a ha ha₁ ha₂
    obtain ⟨e, _, hs, _, _, _, _, hd⟩ := hcoresU a ha ha₁ ha₂
    constructor
    · intro x hx
      have hz : (x, ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1) ∈ e.source := by
        rw [hs, Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)]
        exact hx
      exact (hd _ hz).1.1
    · intro x hx
      have hz : (((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1, x) ∈ e.source := by
        rw [hs, Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
        exact hx
      exact (hd _ hz).2.1
  let L₁ := ‖(F₁.box i').frame.symm.toContinuousLinearMap‖
  let L₂ := ‖(F₂.box j').frame.symm.toContinuousLinearMap‖
  let η := min (ρU / 2) (rU / (2 * (L₁ + L₂ + 1)))
  have hη : 0 < η := by dsimp [η, L₁, L₂]; positivity
  have hηρ : η ≤ ρU / 2 := min_le_left _ _
  have hLη : (L₁ + L₂) * η ≤ rU / 2 := by
    have hden : 0 < 2 * (L₁ + L₂ + 1) := by dsimp [L₁, L₂]; positivity
    have h := (le_div_iff₀ hden).mp (min_le_right (ρU / 2)
      (rU / (2 * (L₁ + L₂ + 1))))
    change η * (2 * (L₁ + L₂ + 1)) ≤ rU at h
    nlinarith
  have hmoved_source_margins : ∀ a ∈ U,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      ∀ y ∈ Metric.ball a η,
      ∀ (hy₁ : y ∈ (F₁.box i').image) (hy₂ : y ∈ (F₂.box j').image),
        Metric.ball ((F₁.box i').chart.symm ⟨y, hy₁⟩).val.1 (rU / 2) ⊆
          Metric.ball 0 (F₁.box i').leafRadius ∧
        Metric.ball ((F₂.box j').chart.symm ⟨y, hy₂⟩).val.1 (rU / 2) ⊆
          Metric.ball 0 (F₂.box j').leafRadius := by
    intro a ha ha₁ ha₂ y hy hy₁ hy₂
    obtain ⟨hm₁, hm₂⟩ := hsource_margins a ha ha₁ ha₂
    have hy' : dist y a ≤ η := (Metric.mem_ball.mp hy).le
    have hd₁ := ((F₁.box i').chart_symm_fst_dist_le a y ha₁ hy₁).trans
      (mul_le_mul_of_nonneg_left hy' (norm_nonneg _))
    have hd₂ := ((F₂.box j').chart_symm_fst_dist_le a y ha₂ hy₂).trans
      (mul_le_mul_of_nonneg_left hy' (norm_nonneg _))
    have h₁ : L₁ * η ≤ rU / 2 := by
      have := mul_nonneg (show 0 ≤ L₂ from norm_nonneg _) hη.le
      nlinarith
    have h₂ : L₂ * η ≤ rU / 2 := by
      have := mul_nonneg (show 0 ≤ L₁ from norm_nonneg _) hη.le
      nlinarith
    constructor
    · apply Set.Subset.trans (Metric.ball_subset_ball' (by linarith [hd₁.trans h₁])) hm₁
    · apply Set.Subset.trans (Metric.ball_subset_ball' (by linarith [hd₂.trans h₂])) hm₂
  obtain ⟨C₁, hC₁, hhold₁⟩ := graphBox_plaque_fderiv_holder_bound
    (F₁.box i') hn hαpos hαlt.le
  obtain ⟨C₂, hC₂, hhold₂⟩ := graphBox_plaque_fderiv_holder_bound
    (F₂.box j') hn hαpos hαlt.le
  obtain ⟨J₁, hJ₁, hfull₁⟩ := graphBox_plaque_holder_bound (F₁.box i') hn
  obtain ⟨J₂, hJ₂, hfull₂⟩ := graphBox_plaque_holder_bound (F₂.box j') hn
  let Jsum := 2 * J₁ + J₂
  let Rsource := max (F₁.box i').leafRadius (F₂.box j').leafRadius
  have hJsum : 0 ≤ Jsum := by dsimp [Jsum]; positivity
  have hRsource : 0 ≤ Rsource := le_trans (F₁.box i').leafRadius_pos.le (le_max_left _ _)
  obtain ⟨Cfull, hCfull, Hfull⟩ := inverse_function_holder_bound
    (E := Block p × Block q) (F := Block (p+q)) n α Jsum KU Rsource
    hαpos hαlt hJsum KU.coe_nonneg hRsource
  obtain ⟨r₁, B₁, hr₁, hB₁, Hrechart₁⟩ := holder_rechart_receiving_core
    (D := Block p) (E := Block (p+q)) (F := Block p × Block q)
    n hn α J₁ Cfull (rU/2) ρU hαpos hαlt hJ₁ hCfull (by positivity) hρU
  obtain ⟨r₂, B₂, hr₂, hB₂, Hrechart₂⟩ := holder_rechart_receiving_core
    (D := Block q) (E := Block (p+q)) (F := Block p × Block q)
    n hn α J₂ Cfull (rU/2) ρU hαpos hαlt hJ₂ hCfull (by positivity) hρU
  let Cinv := (KU : ℝ) * KU * (C₁ + C₂) * (KU : ℝ) ^ α
  have _hinverse_core : ∀ a ∈ U,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      let z₁ := ((F₁.box i').chart.symm ⟨a, ha₁⟩).val
      let z₂ := ((F₂.box j').chart.symm ⟨a, ha₂⟩).val
      let Ψ := fun z : Block p × Block q ↦
        (F₁.box i').plaque z₁.2 z.1 + (F₂.box j').plaque z₂.2 z.2 - a
      ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p + q)),
        (e : _ → _) = Ψ ∧
        e.source = Metric.ball (z₁.1, z₂.1) rU ∧ e (z₁.1, z₂.1) = a ∧
        Metric.ball a ρU ⊆ e.target ∧
        (∀ u ∈ Metric.ball a ρU, ∀ v ∈ Metric.ball a ρU,
          ‖e.symm u - e.symm v‖ ≤ (KU : ℝ) * ‖u-v‖) ∧
        ContDiffOn ℝ n e.symm (Metric.ball a ρU) ∧
        (∀ u ∈ Metric.ball a ρU, ∀ v ∈ Metric.ball a ρU,
          ‖fderiv ℝ e.symm u - fderiv ℝ e.symm v‖ ≤ Cinv * ‖u - v‖ ^ α) ∧
        HasFiniteHolderBounds n α Cfull e.symm (Metric.ball a ρU) ∧
        (fderiv ℝ e.symm a).comp (fderiv ℝ ((F₁.box i').plaque z₁.2) z₁.1) =
          ContinuousLinearMap.inl ℝ (Block p) (Block q) ∧
        (fderiv ℝ e.symm a).comp (fderiv ℝ ((F₂.box j').plaque z₂.2) z₂.1) =
          ContinuousLinearMap.inr ℝ (Block p) (Block q) ∧
        (∀ w ∈ Metric.ball 0 (F₁.box i').transverseRadius, ∀ x : Block p,
          Metric.ball x (rU/2) ⊆ Metric.ball 0 (F₁.box i').leafRadius →
          (F₁.box i').plaque w x ∈ Metric.ball a (ρU/2) →
          MapsTo ((F₁.box i').plaque w) (Metric.ball x r₁) (Metric.ball a ρU) ∧
          HasFiniteHolderBounds n α B₁ (e.symm ∘ (F₁.box i').plaque w) (Metric.ball x r₁)) ∧
        (∀ w ∈ Metric.ball 0 (F₂.box j').transverseRadius, ∀ x : Block q,
          Metric.ball x (rU/2) ⊆ Metric.ball 0 (F₂.box j').leafRadius →
          (F₂.box j').plaque w x ∈ Metric.ball a (ρU/2) →
          MapsTo ((F₂.box j').plaque w) (Metric.ball x r₂) (Metric.ball a ρU) ∧
          HasFiniteHolderBounds n α B₂ (e.symm ∘ (F₂.box j').plaque w) (Metric.ball x r₂)) := by
    intro a ha ha₁ ha₂
    obtain ⟨e, he, hs, hcenter, htarget, hΩball, hinv, hdomain⟩ := hcoresU a ha ha₁ ha₂
    have hx : (((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1,
        ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1) ∈ e.source := by
      rw [hs]
      exact Metric.mem_ball_self hrU
    have hecenter : e (((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1,
        ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1) = a := by
      rw [he]
      exact hcenter
    have hsmooth : ContDiffOn ℝ n e e.source := by
      rw [he]
      intro z hz
      obtain ⟨hz₁, hz₂⟩ := hdomain z hz
      obtain ⟨K₁, _, hb₁⟩ := (F₁.box i').graph_bounds
      obtain ⟨K₂, _, hb₂⟩ := (F₂.box j').graph_bounds
      have hP : ContDiffAt ℝ n ((F₁.box i').plaque
          ((F₁.box i').chart.symm ⟨a, ha₁⟩).val.2) z.1 := by
        have hg := ((hb₁ _ hz₁.2).1).contDiffAt
          (Metric.isOpen_ball.mem_nhds hz₁.1)
        exact contDiffAt_const.add ((F₁.box i').frame.contDiff.contDiffAt.comp z.1
          (contDiffAt_id.prodMk hg))
      have hQ : ContDiffAt ℝ n ((F₂.box j').plaque
          ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.2) z.2 := by
        have hg := ((hb₂ _ hz₂.2).1).contDiffAt
          (Metric.isOpen_ball.mem_nhds hz₂.1)
        exact contDiffAt_const.add ((F₂.box j').frame.contDiff.contDiffAt.comp z.2
          (contDiffAt_id.prodMk hg))
      exact (((hP.comp z contDiffAt_fst).add (hQ.comp z contDiffAt_snd)).sub
        contDiffAt_const).contDiffWithinAt
    have hinverse_smooth := contDiffOn_inverse_of_lipschitzOn
      (show Module.finrank ℝ (Block p × Block q) = Module.finrank ℝ (Block (p + q)) by
        simp [Block, Module.finrank_prod]) e hn hsmooth Metric.isOpen_ball htarget hinv
    let P := (F₁.box i').plaque ((F₁.box i').chart.symm ⟨a, ha₁⟩).val.2
    let Q := (F₂.box j').plaque ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.2
    let fstL := ContinuousLinearMap.fst ℝ (Block p) (Block q)
    let sndL := ContinuousLinearMap.snd ℝ (Block p) (Block q)
    have hformula (z : Block p × Block q) (hz : z ∈ e.source) :
        fderiv ℝ e z = (fderiv ℝ P z.1).comp fstL + (fderiv ℝ Q z.2).comp sndL := by
      obtain ⟨hz₁, hz₂⟩ := hdomain z hz
      have hdP : DifferentiableAt ℝ P z.1 :=
        (graphBox_plaque_hasFDerivAt (F₁.box i') hn hz₁.2 hz₁.1).differentiableAt
      have hdQ : DifferentiableAt ℝ Q z.2 :=
        (graphBox_plaque_hasFDerivAt (F₂.box j') hn hz₂.2 hz₂.1).differentiableAt
      rw [he]
      exact (((hdP.hasFDerivAt.comp z fstL.hasFDerivAt).add
        (hdQ.hasFDerivAt.comp z sndL.hasFDerivAt)).sub_const a).fderiv
    have hleftCenter : (fderiv ℝ e.symm a).comp
        (fderiv ℝ e (((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1,
          ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1)) =
        ContinuousLinearMap.id ℝ (Block p × Block q) := by
      have hdE := (hsmooth.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
        (by exact_mod_cast (show n ≠ 0 by omega))
      have hdI := (hinverse_smooth.contDiffAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρU))).differentiableAt
        (by exact_mod_cast (show n ≠ 0 by omega))
      have hc := hdI.hasFDerivAt
      rw [← hecenter] at hc
      have hcomp := hc.comp _ hdE.hasFDerivAt
      rw [hecenter] at hcomp
      apply HasFDerivAt.unique _ (hasFDerivAt_id
        (((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1,
          ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1))
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds hx] with z hz
      exact (e.left_inv hz).symm
    have hleftP : (fderiv ℝ e.symm a).comp
        (fderiv ℝ P ((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1) =
        ContinuousLinearMap.inl ℝ (Block p) (Block q) := by
      have h := congrArg (fun L : (Block p × Block q) →L[ℝ] (Block p × Block q) ↦
        L.comp (ContinuousLinearMap.inl ℝ (Block p) (Block q))) hleftCenter
      rw [hformula _ hx] at h
      simpa [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.add_comp,
        fstL, sndL] using h
    have hleftQ : (fderiv ℝ e.symm a).comp
        (fderiv ℝ Q ((F₂.box j').chart.symm ⟨a, ha₂⟩).val.1) =
        ContinuousLinearMap.inr ℝ (Block p) (Block q) := by
      have h := congrArg (fun L : (Block p × Block q) →L[ℝ] (Block p × Block q) ↦
        L.comp (ContinuousLinearMap.inr ℝ (Block p) (Block q))) hleftCenter
      rw [hformula _ hx] at h
      simpa [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.add_comp,
        fstL, sndL] using h
    have hforward (β B₁ B₂ : ℝ) (hβ : 0 ≤ β) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
        (hholdP : ∀ x ∈ Metric.ball 0 (F₁.box i').leafRadius,
          ∀ y ∈ Metric.ball 0 (F₁.box i').leafRadius,
          ‖fderiv ℝ P x - fderiv ℝ P y‖ ≤ B₁ * ‖x - y‖ ^ β)
        (hholdQ : ∀ x ∈ Metric.ball 0 (F₂.box j').leafRadius,
          ∀ y ∈ Metric.ball 0 (F₂.box j').leafRadius,
          ‖fderiv ℝ Q x - fderiv ℝ Q y‖ ≤ B₂ * ‖x - y‖ ^ β) : ∀ z ∈ e.source, ∀ z' ∈ e.source,
        ‖fderiv ℝ e z - fderiv ℝ e z'‖ ≤ (B₁ + B₂) * ‖z - z'‖ ^ β := by
      intro z hz z' hz'
      obtain ⟨hz₁, hz₂⟩ := hdomain z hz
      obtain ⟨hz₁', hz₂'⟩ := hdomain z' hz'
      have hP := hholdP _ hz₁.1 _ hz₁'.1
      have hQ := hholdQ _ hz₂.1 _ hz₂'.1
      have hpn : ‖z.1 - z'.1‖ ≤ ‖z - z'‖ := by
        exact le_max_left _ _
      have hqn : ‖z.2 - z'.2‖ ≤ ‖z - z'‖ := by
        exact le_max_right _ _
      have hp : ‖fderiv ℝ P z.1 - fderiv ℝ P z'.1‖ ≤ B₁ * ‖z - z'‖ ^ β :=
        hP.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hpn hβ) hB₁)
      have hq : ‖fderiv ℝ Q z.2 - fderiv ℝ Q z'.2‖ ≤ B₂ * ‖z - z'‖ ^ β :=
        hQ.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hqn hβ) hB₂)
      rw [hformula z hz, hformula z' hz']
      have hid : (fderiv ℝ P z.1).comp fstL + (fderiv ℝ Q z.2).comp sndL -
          ((fderiv ℝ P z'.1).comp fstL + (fderiv ℝ Q z'.2).comp sndL) =
          (fderiv ℝ P z.1 - fderiv ℝ P z'.1).comp fstL +
          (fderiv ℝ Q z.2 - fderiv ℝ Q z'.2).comp sndL := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp]
        abel
      rw [hid]
      calc
        _ ≤ ‖(fderiv ℝ P z.1 - fderiv ℝ P z'.1).comp fstL‖ +
            ‖(fderiv ℝ Q z.2 - fderiv ℝ Q z'.2).comp sndL‖ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ P z.1 - fderiv ℝ P z'.1‖ * ‖fstL‖ +
            ‖fderiv ℝ Q z.2 - fderiv ℝ Q z'.2‖ * ‖sndL‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (B₁ * ‖z - z'‖ ^ β) * 1 + (B₂ * ‖z - z'‖ ^ β) * 1 := by
          apply add_le_add
          · exact mul_le_mul hp (ContinuousLinearMap.norm_fst_le ℝ (Block p) (Block q))
              (norm_nonneg _) (by positivity)
          · exact mul_le_mul hq (ContinuousLinearMap.norm_snd_le ℝ (Block p) (Block q))
              (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hw₁ := ((F₁.box i').chart.symm ⟨a, ha₁⟩).property.2
    have hw₂ := ((F₂.box j').chart.symm ⟨a, ha₂⟩).property.2
    have hfholder := hforward α C₁ C₂ hαpos.le hC₁ hC₂ (hhold₁ _ hw₁) (hhold₂ _ hw₂)
    have hInvHolder := inverse_fderiv_holder_bound e Metric.isOpen_ball htarget
      (hsmooth.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega)))
      (hinverse_smooth.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega)))
      (show (0 : ℝ) ≤ KU from KU.coe_nonneg) (add_nonneg hC₁ hC₂) hαpos.le hinv
      (fun u hu v hv ↦ hfholder _ (e.map_target (htarget hu)) _ (e.map_target (htarget hv)))
    have hFullForward : HasFiniteHolderBounds n α Jsum e e.source := by
      have hp := (hfull₁ _ hw₁).comp_linear_contraction Metric.isOpen_ball e.open_source
        hαpos.le hJ₁ fstL (ContinuousLinearMap.norm_fst_le ℝ (Block p) (Block q))
        (fun z hz ↦ (hdomain z hz).1.1)
      have hq := (hfull₂ _ hw₂).comp_linear_contraction Metric.isOpen_ball e.open_source
        hαpos.le hJ₂ sndL (ContinuousLinearMap.norm_snd_le ℝ (Block p) (Block q))
        (fun z hz ↦ (hdomain z hz).2.1)
      have hbase : ‖a‖ ≤ J₁ := by
        have hP := (F₁.box i').chart_formula ((F₁.box i').chart.symm ⟨a, ha₁⟩)
        simp only [Homeomorph.apply_symm_apply] at hP
        have hb := (hfull₁ _ hw₁).2.1 0 (Nat.zero_le n)
          ((F₁.box i').chart.symm ⟨a, ha₁⟩).val.1
          ((F₁.box i').chart.symm ⟨a, ha₁⟩).property.1
        simpa only [norm_iteratedFDeriv_zero, GraphBox.plaque, ← hP] using hb
      have hsum := ((hp.add e.open_source hq).add e.open_source
        (finiteHolderBounds_const n hn α e.source (-a))).mono_bound
          (show J₁ + J₂ + ‖-a‖ ≤ Jsum by rw [norm_neg]; dsimp [Jsum]; linarith)
      rw [he]
      exact hsum
    have hInverseValues : ∀ y ∈ Metric.ball a ρU, ‖e.symm y‖ ≤ Rsource := by
      intro y hy
      obtain ⟨hz₁, hz₂⟩ := hdomain (e.symm y) (e.map_target (htarget hy))
      apply max_le
      · exact (show ‖(e.symm y).1‖ < (F₁.box i').leafRadius by
          simpa only [Metric.mem_ball, dist_zero_right] using hz₁.1).le.trans (le_max_left _ _)
      · exact (show ‖(e.symm y).2‖ < (F₂.box j').leafRadius by
          simpa only [Metric.mem_ball, dist_zero_right] using hz₂.1).le.trans (le_max_right _ _)
    obtain ⟨hFullJets, hFullHolder⟩ := Hfull e.source (Metric.ball a ρU)
      e.open_source (by rw [hs]; exact convex_ball _ _) Metric.isOpen_ball (convex_ball _ _)
      e e.symm hsmooth hinverse_smooth (fun y hy ↦ e.map_target (htarget hy))
      (fun x hx ↦ e.left_inv hx) (fun y hy ↦ e.right_inv (htarget hy))
      hinv hInverseValues hFullForward.2.1 hFullForward.2.2
    have hfullInv : HasFiniteHolderBounds n α Cfull e.symm (Metric.ball a ρU) :=
      ⟨hinverse_smooth, hFullJets, hFullHolder⟩
    refine ⟨e, he, hs, hecenter, htarget, hinv,
      hinverse_smooth, hInvHolder, hfullInv, hleftP, hleftQ, ?_, ?_⟩
    · intro w hw x hmargin hreceiving
      exact (Hrechart₁ (Metric.ball 0 (F₁.box i').leafRadius) Metric.isOpen_ball
        (convex_ball _ _) ((F₁.box i').plaque w) e.symm x a (hfull₁ w hw) hfullInv
        hmargin hreceiving).2
    · intro w hw x hmargin hreceiving
      exact (Hrechart₂ (Metric.ball 0 (F₂.box j').leafRadius) Metric.isOpen_ball
        (convex_ball _ _) ((F₂.box j').plaque w) e.symm x a (hfull₂ w hw) hfullInv
        hmargin hreceiving).2
  obtain ⟨Kleaf₁,hKleaf₁,hleaf₁⟩ := hh₁ i'
  obtain ⟨Kleaf₂,hKleaf₂,hleaf₂⟩ := hh₂ j'
  have : Nonempty (Fin p) := ⟨⟨0,by omega⟩⟩
  have : Nonempty (Fin q) := ⟨⟨0,by omega⟩⟩
  obtain ⟨Cregraph₁,hCregraph₁,Hregraph₁⟩ := regraph_centered_with_function
    (D := Block p) (E := Block q) hn hαpos hαlt hB₁ hKleaf₁ hRsource hRsource
  obtain ⟨Cregraph₂,hCregraph₂,Hregraph₂⟩ := regraph_centered_with_function
    (D := Block q) (E := Block p) hn hαpos hαlt hB₂ hKleaf₂ hRsource hRsource
  have hsmall_slopes : ∀ σ : ℝ, 0 < σ →
      ∃ V : Set (Block (p+q)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ s : ℝ, 0 < s ∧ s ≤ rU/2 ∧ ∀ a ∈ V,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p+q)),
        (e : _ → _) = (fun z ↦
          (F₁.box i').plaque ((F₁.box i').chart.symm ⟨a,ha₁⟩).val.2 z.1 +
          (F₂.box j').plaque ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.2 z.2 - a) ∧
        e.source = Metric.ball (((F₁.box i').chart.symm ⟨a,ha₁⟩).val.1,
          ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.1) rU ∧
        e (((F₁.box i').chart.symm ⟨a,ha₁⟩).val.1,
          ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.1) = a ∧
        Metric.ball a ρU ⊆ e.target ∧
        (∀ u ∈ Metric.ball a ρU, ∀ v ∈ Metric.ball a ρU,
          ‖e.symm u-e.symm v‖ ≤ (KU:ℝ)*‖u-v‖) ∧
        HasFiniteHolderBounds n α Cfull e.symm (Metric.ball a ρU) ∧
        ∀ y ∈ V, ∀ (hy₁ : y ∈ (F₁.box i').image) (hy₂ : y ∈ (F₂.box j').image),
          HasFiniteHolderBounds n α B₁ (e.symm ∘ (F₁.box i').plaque
            ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.2)
            (Metric.ball ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.1 s) ∧
          HasFiniteHolderBounds n α B₂ (e.symm ∘ (F₂.box j').plaque
            ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.2)
            (Metric.ball ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.1 s) ∧
          HasFiniteHolderBounds n α Kleaf₁ (h ∘ (F₁.box i').plaque
            ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.2)
            (Metric.ball ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.1 s) ∧
          HasFiniteHolderBounds n α Kleaf₂ (h ∘ (F₂.box j').plaque
            ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.2)
            (Metric.ball ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.1 s) ∧
          (∀ u ∈ Metric.ball ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.1 s,
            (F₁.box i').plaque ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.2 u ∈ Metric.ball a ρU ∧
            ‖fderiv ℝ (e.symm ∘ (F₁.box i').plaque
              ((F₁.box i').chart.symm ⟨y,hy₁⟩).val.2) u-
              ContinuousLinearMap.inl ℝ (Block p) (Block q)‖ ≤ σ) ∧
          (∀ u ∈ Metric.ball ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.1 s,
            (F₂.box j').plaque ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.2 u ∈ Metric.ball a ρU ∧
            ‖fderiv ℝ (e.symm ∘ (F₂.box j').plaque
              ((F₂.box j').chart.symm ⟨y,hy₂⟩).val.2) u-
              ContinuousLinearMap.inr ℝ (Block p) (Block q)‖ ≤ σ) := by
    intro σ hσ
    have hCinv : 0 ≤ Cinv := by dsimp [Cinv]; positivity
    obtain ⟨V₁,hV₁,hxV₁,hV₁sub,s₁,hs₁,H₁⟩ := uniform_recharted_plaque_slope
      (F := Block p × Block q) (F₁.box i') hn hi' hCfull hCinv hαpos hρU hσ
    obtain ⟨V₂,hV₂,hxV₂,hV₂sub,s₂,hs₂,H₂⟩ := uniform_recharted_plaque_slope
      (F := Block p × Block q) (F₂.box j') hn hj' hCfull hCinv hαpos hρU hσ
    let V := (V₁ ∩ (V₂ ∩ U)) ∩ Metric.ball x (η/4)
    let s := min (min s₁ s₂) (min r₁ (min r₂ (rU/2)))
    have hs : 0 < s := lt_min (lt_min hs₁ hs₂) (lt_min hr₁ (lt_min hr₂ (by positivity)))
    have hss₁ : s ≤ s₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hss₂ : s ≤ s₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hsr₁ : s ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
    have hsr₂ : s ≤ r₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsrU : s ≤ rU/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨V,(hV₁.inter (hV₂.inter hU)).inter Metric.isOpen_ball,
      ⟨⟨hxV₁,hxV₂,hxU⟩,Metric.mem_ball_self (by positivity)⟩,
      fun a ha ↦ ha.1.2.2,s,hs,hsrU,?_⟩
    intro a ha ha₁ ha₂
    obtain ⟨e,he,hesource,hecenter,hetarget,heinvlip,hesmooth,hInvHolder,hfull,hleftP,hleftQ,hchart₁,hchart₂⟩ :=
      _hinverse_core a ha.1.2.2 ha₁ ha₂
    have hdiff : DifferentiableOn ℝ e.symm (Metric.ball a ρU) :=
      hesmooth.differentiableOn (by simp; omega)
    have hnorm : ‖fderiv ℝ e.symm a‖ ≤ Cfull := by
      simpa only [norm_iteratedFDeriv_one] using hfull.2.1 1 hn a (Metric.mem_ball_self hρU)
    have hholder (z) (hz : z ∈ Metric.ball a ρU) :
        ‖fderiv ℝ e.symm z-fderiv ℝ e.symm a‖ ≤ Cinv*‖z-a‖^α :=
      hInvHolder z hz a (Metric.mem_ball_self hρU)
    refine ⟨e,he,hesource,hecenter,hetarget,heinvlip,hfull,?_⟩
    intro y hy hy₁ hy₂
    have hya : y ∈ Metric.ball a η := by
      have H := dist_triangle y x a
      have hyx := Metric.mem_ball.mp hy.2
      have hax := Metric.mem_ball.mp ha.2
      rw [dist_comm x a] at H
      rw [Metric.mem_ball]
      linarith
    obtain ⟨hm₁,hm₂⟩ := hmoved_source_margins a ha.1.2.2 ha₁ ha₂ y hya hy₁ hy₂
    have hyρ : y ∈ Metric.ball a (ρU/2) := Metric.ball_subset_ball hηρ hya
    have hc₁ := hchart₁ _ ((F₁.box i').chart.symm ⟨y,hy₁⟩).property.2 _ hm₁
      (by simpa only [GraphBox.plaque_chart_symm] using hyρ)
    have hc₂ := hchart₂ _ ((F₂.box j').chart.symm ⟨y,hy₂⟩).property.2 _ hm₂
      (by simpa only [GraphBox.plaque_chart_symm] using hyρ)
    refine ⟨hc₁.2.mono (Metric.ball_subset_ball hsr₁),
      hc₂.2.mono (Metric.ball_subset_ball hsr₂),
      (hleaf₁ _ ((F₁.box i').chart.symm ⟨y,hy₁⟩).property.2).mono
        ((Metric.ball_subset_ball hsrU).trans hm₁),
      (hleaf₂ _ ((F₂.box j').chart.symm ⟨y,hy₂⟩).property.2).mono
        ((Metric.ball_subset_ball hsrU).trans hm₂),?_,?_⟩
    · intro u hu
      have H := H₁ a ha.1.1 ha₁ y hy.1.1 hy₁ u
        (Metric.ball_subset_ball hss₁ hu)
      exact ⟨H.2.1,H.2.2 e.symm _ hdiff hnorm hholder hleftP⟩
    · intro u hu
      have H := H₂ a ha.1.2.1 ha₂ y hy.1.2.1 hy₂ u
        (Metric.ball_subset_ball hss₂ hu)
      exact ⟨H.2.1,H.2.2 e.symm _ hdiff hnorm hholder hleftQ⟩
  have hforward_distance : ∀ a ∈ U,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      let z₁ := ((F₁.box i').chart.symm ⟨a,ha₁⟩).val
      let z₂ := ((F₂.box j').chart.symm ⟨a,ha₂⟩).val
      ∀ z ∈ Metric.ball (z₁.1,z₂.1) rU,
        ‖((F₁.box i').plaque z₁.2 z.1+(F₂.box j').plaque z₂.2 z.2-a)-a‖ ≤
          (J₁+J₂)*‖z-(z₁.1,z₂.1)‖ := by
    intro a ha ha₁ ha₂ z₁ z₂ z hz
    obtain ⟨hm₁,hm₂⟩ := hsource_margins a ha ha₁ ha₂
    have hz₁ : z.1 ∈ Metric.ball z₁.1 rU := by
      exact lt_of_le_of_lt (show dist z.1 z₁.1 ≤ dist z (z₁.1,z₂.1) from le_max_left _ _) hz
    have hz₂ : z.2 ∈ Metric.ball z₂.1 rU := by
      exact lt_of_le_of_lt (show dist z.2 z₂.1 ≤ dist z (z₁.1,z₂.1) from le_max_right _ _) hz
    have HP := hfull₁ z₁.2 ((F₁.box i').chart.symm ⟨a,ha₁⟩).property.2
    have HQ := hfull₂ z₂.2 ((F₂.box j').chart.symm ⟨a,ha₂⟩).property.2
    have hp := (convex_ball (0:Block p) (F₁.box i').leafRadius).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ (HP.1.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt
        (by simp; omega))
      (fun w hw ↦ by simpa only [norm_iteratedFDeriv_one] using HP.2.1 1 hn w hw)
      ((F₁.box i').chart.symm ⟨a,ha₁⟩).property.1 (hm₁ hz₁)
    have hq := (convex_ball (0:Block q) (F₂.box j').leafRadius).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ (HQ.1.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt
        (by simp; omega))
      (fun w hw ↦ by simpa only [norm_iteratedFDeriv_one] using HQ.2.1 1 hn w hw)
      ((F₂.box j').chart.symm ⟨a,ha₂⟩).property.1 (hm₂ hz₂)
    have hp' : ‖(F₁.box i').plaque z₁.2 z.1-a‖ ≤ (J₁)*‖z-(z₁.1,z₂.1)‖ := by
      simpa only [z₁,GraphBox.plaque_chart_symm] using
        hp.trans (mul_le_mul_of_nonneg_left
          (show ‖z.1-z₁.1‖ ≤ ‖z-(z₁.1,z₂.1)‖ from le_max_left _ _) hJ₁)
    have hq' : ‖(F₂.box j').plaque z₂.2 z.2-a‖ ≤ (J₂)*‖z-(z₁.1,z₂.1)‖ := by
      simpa only [z₂,GraphBox.plaque_chart_symm] using
        hq.trans (mul_le_mul_of_nonneg_left
          (show ‖z.2-z₂.1‖ ≤ ‖z-(z₁.1,z₂.1)‖ from le_max_right _ _) hJ₂)
    have heq : (F₁.box i').plaque z₁.2 z.1+(F₂.box j').plaque z₂.2 z.2-a-a =
        ((F₁.box i').plaque z₁.2 z.1-a)+((F₂.box j').plaque z₂.2 z.2-a) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by nlinarith only [hp',hq'])
  have hgraph_families : ∀ σ : ℝ, 0 < σ → σ ≤ 1/4 →
      ∃ V : Set (Block (p+q)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ s : ℝ, 0 < s ∧ ∀ a ∈ V,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      let z₀ := (((F₁.box i').chart.symm ⟨a,ha₁⟩).val.1,
        ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.1)
      ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p+q)),
        (e : _ → _) = (fun z ↦
          (F₁.box i').plaque ((F₁.box i').chart.symm ⟨a,ha₁⟩).val.2 z.1 +
          (F₂.box j').plaque ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.2 z.2 - a) ∧
        e.source = Metric.ball z₀ rU ∧ e z₀ = a ∧
        Metric.ball a ρU ⊆ e.target ∧
        (∀ u ∈ Metric.ball a ρU, ∀ v ∈ Metric.ball a ρU,
          ‖e.symm u-e.symm v‖ ≤ (KU:ℝ)*‖u-v‖) ∧
        HasFiniteHolderBounds n α Cfull e.symm (Metric.ball a ρU) ∧
        ∀ y ∈ V, ‖e.symm y-z₀‖ ≤ s/16 →
          ∃ φ : Block p → Block q, ∃ ψ : Block q → Block p,
            φ ((e.symm y).1-z₀.1) = (e.symm y).2-z₀.2 ∧
            ψ ((e.symm y).2-z₀.2) = (e.symm y).1-z₀.1 ∧
            HasFiniteHolderBounds n α Cregraph₁ φ (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₂ ψ (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₁
              (fun u ↦ h (e (z₀+(u,φ u)))) (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₂
              (fun v ↦ h (e (z₀+(ψ v,v)))) (Metric.ball 0 (s/8)) ∧
            (∀ u ∈ Metric.ball (0:Block p) (s/8), ∀ v ∈ Metric.ball 0 (s/8),
              ‖φ u-φ v‖ ≤ (2*σ)*‖u-v‖) ∧
            (∀ u ∈ Metric.ball (0:Block q) (s/8), ∀ v ∈ Metric.ball 0 (s/8),
              ‖ψ u-ψ v‖ ≤ (2*σ)*‖u-v‖) := by
    intro σ hσ hσq
    obtain ⟨V,hV,hxV,hVU,s,hs,hsr,Hs⟩ := hsmall_slopes σ hσ
    refine ⟨V,hV,hxV,hVU,s,hs,?_⟩
    intro a ha ha₁ ha₂ z₀
    obtain ⟨e,he,hes,hea,het,helip,hefull,He⟩ := Hs a ha ha₁ ha₂
    refine ⟨e,he,hes,hea,het,helip,hefull,?_⟩
    intro y hy hnear
    have hy₁ := (hsubU (hVU hy)).1
    have hy₂ := (hsubU (hVU hy)).2
    let y₁ := ((F₁.box i').chart.symm ⟨y,hy₁⟩).val
    let y₂ := ((F₂.box j').chart.symm ⟨y,hy₂⟩).val
    let Q₁ := e.symm ∘ (F₁.box i').plaque y₁.2
    let Q₂ := e.symm ∘ (F₂.box j').plaque y₂.2
    have hz₀ : ‖z₀‖ ≤ Rsource := by
      apply max_le
      · exact (mem_ball_zero_iff.mp ((F₁.box i').chart.symm ⟨a,ha₁⟩).property.1).le.trans
          (le_max_left _ _)
      · exact (mem_ball_zero_iff.mp ((F₂.box j').chart.symm ⟨a,ha₂⟩).property.1).le.trans
          (le_max_right _ _)
    obtain ⟨hm₁,hm₂⟩ := hsource_margins y (hVU hy) hy₁ hy₂
    have hsru : s ≤ rU := hsr.trans (by linarith)
    have hsource₁ : ∀ z ∈ Metric.ball y₁.1 s, ‖z‖ ≤ Rsource := by
      intro z hz
      exact (mem_ball_zero_iff.mp (hm₁ (Metric.ball_subset_ball hsru hz))).le.trans
        (le_max_left _ _)
    have hsource₂ : ∀ z ∈ Metric.ball y₂.1 s, ‖z‖ ≤ Rsource := by
      intro z hz
      exact (mem_ball_zero_iff.mp (hm₂ (Metric.ball_subset_ball hsru hz))).le.trans
        (le_max_right _ _)
    obtain ⟨hQ₁,hQ₂,hf₁,hf₂,hD₁,hD₂⟩ := He y hy hy₁ hy₂
    have hQ₁center : Q₁ y₁.1 = e.symm y := by
      simp only [Q₁,Function.comp_apply,y₁,GraphBox.plaque_chart_symm]
    have hQ₂center : Q₂ y₂.1 = e.symm y := by
      simp only [Q₂,Function.comp_apply,y₂,GraphBox.plaque_chart_symm]
    obtain ⟨φ,hφanchor,hφ,hφscalar,hφlip,_⟩ := Hregraph₁ Q₁
      (h ∘ (F₁.box i').plaque y₁.2) (h ∘ e) y₁.1 z₀ s hs hz₀
      (by rw [hQ₁center]; exact hnear) hsource₁ σ hσ.le hσq hQ₁ hf₁
      (fun z hz ↦ by
        change h (e (e.symm ((F₁.box i').plaque y₁.2 z))) = _
        rw [e.right_inv (het ((hD₁ z hz).1))]; rfl)
      (fun z hz ↦ (hD₁ z hz).2)
    obtain ⟨hQ₂swap,hD₂swap⟩ := regraph_swap_bounds hn hB₂ Metric.isOpen_ball Q₂ hQ₂
      (fun z hz ↦ (hD₂ z hz).2)
    obtain ⟨ψ,hψanchor,hψ,hψscalar,hψlip,_⟩ := Hregraph₂ (fun z ↦ (Q₂ z).swap)
      (h ∘ (F₂.box j').plaque y₂.2) (fun z ↦ h (e z.swap)) y₂.1 z₀.swap s hs
      (by change ‖(LinearIsometryEquiv.prodComm ℝ (Block p) (Block q)) z₀‖ ≤ Rsource
          rw [LinearIsometryEquiv.norm_map]; exact hz₀)
      (by rw [hQ₂center]; change ‖(e.symm y-z₀).swap‖ ≤ s/16
          change ‖(LinearIsometryEquiv.prodComm ℝ (Block p) (Block q)) (e.symm y-z₀)‖ ≤ s/16
          rw [LinearIsometryEquiv.norm_map]; exact hnear)
      hsource₂ σ hσ.le hσq hQ₂swap hf₂
      (fun z hz ↦ by
        change h (e (e.symm ((F₂.box j').plaque y₂.2 z))) = _
        rw [e.right_inv (het ((hD₂ z hz).1))]; rfl) hD₂swap
    refine ⟨φ,ψ,?_,?_,hφ,hψ,hφscalar,?_,hφlip,hψlip⟩
    · simpa only [hQ₁center] using hφanchor
    · simpa only [hQ₂center,Prod.fst_swap,Prod.snd_swap] using hψanchor
    · exact hψscalar
  have hcoordinate_families : ∀ σ : ℝ, 0 < σ → σ ≤ 1/4 →
      ∃ V : Set (Block (p+q)), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ s κ : ℝ, 0 < s ∧ 0 < κ ∧ ∀ a ∈ V,
      ∀ (ha₁ : a ∈ (F₁.box i').image) (ha₂ : a ∈ (F₂.box j').image),
      let z₀ := (((F₁.box i').chart.symm ⟨a,ha₁⟩).val.1,
        ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.1)
      ∃ e : OpenPartialHomeomorph (Block p × Block q) (Block (p+q)),
        e.source = Metric.ball z₀ rU ∧ e z₀ = a ∧
        Metric.ball a ρU ⊆ e.target ∧
        (∀ u ∈ Metric.ball a ρU, ∀ v ∈ Metric.ball a ρU,
          ‖e.symm u-e.symm v‖ ≤ (KU:ℝ)*‖u-v‖) ∧
        HasFiniteHolderBounds n α Cfull e.symm (Metric.ball a ρU) ∧
        ∀ w : Block p × Block q, ‖w‖ ≤ κ →
          ∃ φ : Block p → Block q, ∃ ψ : Block q → Block p,
            φ w.1 = w.2 ∧ ψ w.2 = w.1 ∧
            HasFiniteHolderBounds n α Cregraph₁ φ (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₂ ψ (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₁
              (fun u ↦ h (e (z₀+(u,φ u)))) (Metric.ball 0 (s/8)) ∧
            HasFiniteHolderBounds n α Cregraph₂
              (fun v ↦ h (e (z₀+(ψ v,v)))) (Metric.ball 0 (s/8)) ∧
            (∀ u ∈ Metric.ball (0:Block p) (s/8), ∀ v ∈ Metric.ball 0 (s/8),
              ‖φ u-φ v‖ ≤ (2*σ)*‖u-v‖) ∧
            (∀ u ∈ Metric.ball (0:Block q) (s/8), ∀ v ∈ Metric.ball 0 (s/8),
              ‖ψ u-ψ v‖ ≤ (2*σ)*‖u-v‖) := by
    intro σ hσ hσq
    obtain ⟨V,hV,hxV,hVU,s,hs,Hs⟩ := hgraph_families σ hσ hσq
    obtain ⟨β,hβ,hβV⟩ := Metric.isOpen_iff.mp hV x hxV
    let κ := min (rU/2) (min (s/16) (β/(4*(J₁+J₂+1))))
    have hκ : 0 < κ := by dsimp [κ]; positivity
    have hκr : κ ≤ rU/2 := min_le_left _ _
    have hκs : κ ≤ s/16 := (min_le_right _ _).trans (min_le_left _ _)
    have hκβ : (J₁+J₂)*κ ≤ β/4 := by
      have hden : 0 < 4*(J₁+J₂+1) := by positivity
      have H := (le_div_iff₀ hden).mp
        (show κ ≤ β/(4*(J₁+J₂+1)) from
          (min_le_right _ _).trans (min_le_right _ _))
      nlinarith only [H,hκ]
    have hVsmall : Metric.ball x (β/4) ⊆ V :=
      (Metric.ball_subset_ball (by linarith)).trans hβV
    refine ⟨Metric.ball x (β/4),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),
      hVsmall.trans hVU,s,κ,hs,hκ,?_⟩
    intro a ha ha₁ ha₂ z₀
    obtain ⟨e,he,hes,hea,het,helip,hefull,He⟩ := Hs a (hVsmall ha) ha₁ ha₂
    refine ⟨e,hes,hea,het,helip,hefull,?_⟩
    intro w hw
    have hzw : z₀+w ∈ Metric.ball z₀ rU := by
      rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
      exact hw.trans_lt (hκr.trans_lt (by linarith))
    have hleft : e.symm (e (z₀+w)) = z₀+w :=
      e.left_inv (by simpa only [hes] using hzw)
    have hdist : ‖e (z₀+w)-a‖ ≤ β/4 := by
      have H := hforward_distance a (hVU (hVsmall ha)) ha₁ ha₂ (z₀+w) hzw
      have heval := congrFun he (z₀+w)
      change ‖((F₁.box i').plaque ((F₁.box i').chart.symm ⟨a,ha₁⟩).val.2 (z₀+w).1 +
        (F₂.box j').plaque ((F₂.box j').chart.symm ⟨a,ha₂⟩).val.2 (z₀+w).2-a)-a‖ ≤
        (J₁+J₂)*‖z₀+w-z₀‖ at H
      rw [← heval] at H
      rw [add_sub_cancel_left] at H
      exact H.trans ((mul_le_mul_of_nonneg_left hw (add_nonneg hJ₁ hJ₂)).trans hκβ)
    have hyV : e (z₀+w) ∈ V := by
      apply hβV
      have Ha := Metric.mem_ball.mp ha
      have H := dist_triangle (e (z₀+w)) a x
      rw [dist_eq_norm (e (z₀+w)) a] at H
      rw [Metric.mem_ball]
      linarith
    have hnear : ‖e.symm (e (z₀+w))-z₀‖ ≤ s/16 := by
      rw [hleft,add_sub_cancel_left]
      exact hw.trans hκs
    obtain ⟨φ,ψ,hφa,hψa,hφ,hψ,hφs,hψs,hφl,hψl⟩ := He _ hyV hnear
    refine ⟨φ,ψ,?_,?_,hφ,hψ,hφs,hψs,hφl,hψl⟩
    · simpa only [hleft,z₀,Prod.fst_add,Prod.snd_add,add_sub_cancel_left] using hφa
    · simpa only [hleft,z₀,Prod.fst_add,Prod.snd_add,add_sub_cancel_left] using hψa
  -- Fix the actual whole-block polynomial sampling grids and their inverse.
  obtain ⟨I,instI,A,EA,hEA⟩ := block_unisolvent_samples p n
  obtain ⟨J,instJ,B,EB,hEB⟩ := block_unisolvent_samples q n
  let R : ℝ := 4*(‖A‖+‖B‖+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hA (i : I) : ‖A i‖ ≤ R/2 := by
    have := norm_le_pi_norm A i
    have := norm_nonneg B
    dsimp [R]
    linarith
  have hB (j : J) : ‖B j‖ ≤ R/2 := by
    have := norm_le_pi_norm B j
    have := norm_nonneg A
    dsimp [R]
    linarith
  clear_value R
  obtain ⟨Egrid,hEgrid⟩ := block_tensor_grid_evaluation A B EA EB hEA hEB
  obtain ⟨δgrid,Cgrid,hδgrid,hCgrid,Hgrid⟩ := stable_scaled_interpolant
    blockBimonomial block_bimonomial_continuous blockBidegree
    block_bimonomial_homogeneous (fun ij : I × J ↦ (A ij.1,B ij.2)) Egrid hEgrid
  obtain ⟨εgrid,Lgrid,hεgrid,hεgridq,hLgrid,Hresidual⟩ :=
    small_slope_grid_remainder hn A B EA EB hEA hEB R hR hA hB
  let M := max 1 (max Cregraph₁ Cregraph₂)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  let Amon := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n
  let Bmon := (2:ℝ)^(2*n+1)*(n:ℝ)*((2:ℝ)^(2*n+1)*(2*R+1))^n*
    ((2:ℝ)^(2*n+1)*(2*R+1))^n
  let Ecoef := max M (max Amon Bmon)
  let Astep := Cgrid*(Lgrid+1)^2*R^((n:ℝ)+α)*Ecoef
  have hAmon : 0 ≤ Amon := by dsimp [Amon]; positivity
  have hBmon : 0 ≤ Bmon := by dsimp [Bmon]; positivity
  have hEcoef : 0 ≤ Ecoef := hM0.trans (le_max_left _ _)
  have hAstep : 0 ≤ Astep := by dsimp [Astep]; positivity
  let θ := min (1/8:ℝ) ((1/4:ℝ)^((1-α)⁻¹))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθeight : θ ≤ 1/8 := min_le_left _ _
  have hθlt : θ < 1 := hθeight.trans_lt (by norm_num)
  have hθsmall : θ^(1-α) ≤ 1/4 := by
    calc
      θ^(1-α) ≤ ((1/4:ℝ)^((1-α)⁻¹))^(1-α) :=
        Real.rpow_le_rpow hθ.le (min_le_right _ _) (by linarith only [hαlt])
      _ = 1/4 := Real.rpow_inv_rpow (by norm_num) (by linarith only [hαlt])
  clear_value θ
  let Bstep := Astep*θ^(-((n:ℝ)+α))
  have hBstep : 0 ≤ Bstep := by dsimp [Bstep]; positivity
  let δmon := min 1 (1/(4*(Bstep+1)))
  have hδmon : 0 < δmon := by dsimp [δmon]; positivity
  have hδmon1 : δmon ≤ 1 := min_le_left _ _
  have hsmallproduct : Bstep*δmon ≤ 1/4 := by
    have H := (le_div_iff₀ (show 0 < 4*(Bstep+1) by positivity)).mp
      (show δmon ≤ 1/(4*(Bstep+1)) from min_le_right _ _)
    nlinarith only [H,hδmon]
  clear_value δmon
  let σ := min (1/8:ℝ) (min (εgrid/2) (min (δgrid/(4*R)) (δmon/(4*R+2))))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσq : σ ≤ 1/4 := (min_le_left _ _).trans (by norm_num)
  have hσε : 2*σ ≤ εgrid := by
    have H : σ ≤ εgrid/2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hσgrid : (2*σ)*R < δgrid := by
    have H : σ ≤ δgrid/(4*R) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have H' := (le_div_iff₀ (show 0 < 4*R by positivity)).mp H
    nlinarith only [H',hδgrid]
  have hσδ : (2*σ)*(2*R) ≤ δmon ∧ 2*σ ≤ δmon := by
    have H : σ ≤ δmon/(4*R+2) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have H' := (le_div_iff₀ (show 0 < 4*R+2 by positivity)).mp H
    constructor <;> nlinarith only [H',hσ,mul_pos hσ hR]
  obtain ⟨V,hV,hxV,hVU,s,κ,hs,hκ,Hfamilies⟩ := hcoordinate_families σ hσ hσq
  clear hcoordinate_families hgraph_families hsmall_slopes hforward_distance
    _hinverse_core
  clear * - Hfamilies V hV hxV hVU s κ hs hκ hsubU ρU KU hrU hρU hcoresU
    Rsource Cfull F₁ F₂ i' j' hn hαpos hαlt h Cregraph₁ Cregraph₂
    I instI A EA hEA J instJ B EB hEB R hR hA hB Egrid hEgrid δgrid Cgrid
    hδgrid hCgrid Hgrid εgrid Lgrid hεgrid hεgridq hLgrid Hresidual M hM hM0
    Amon Bmon Ecoef Astep hAmon hBmon hEcoef hAstep θ hθ hθ1 hθeight hθlt hθsmall
    Bstep hBstep δmon hδmon hδmon1 hsmallproduct σ hσ hσq hσε hσgrid hσδ
  let rgraph := min 1 (s/8)
  have hrgraph : 0 < rgraph := by dsimp [rgraph]; positivity
  have hrgraph1 : rgraph ≤ 1 := min_le_left _ _
  let D := 1+6*Bstep
  have hD : 1 ≤ D := by dsimp [D]; linarith
  let ρ := θ^α
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hθ _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hθ.le hθlt hαpos
  let εmax := (1-ρ)/(3+D)
  have hεmax : 0 < εmax := by dsimp [εmax]; positivity
  let tmax := min 1 (min (κ/(2*R)) (min (rgraph/(4*R))
    (min (δmon/(M+1)) (min ((δmon/(M+1))^(α⁻¹))
      ((εmax/(Astep*(θ^n)⁻¹+1))^(α⁻¹))))))
  have htmax : 0 < tmax := by dsimp [tmax]; positivity
  have htmax1 : tmax ≤ 1 := min_le_left _ _
  have htmaxκ : tmax*R ≤ κ/2 := by
    have H : tmax ≤ κ/(2*R) := (min_le_right _ _).trans (min_le_left _ _)
    have H' := (le_div_iff₀ (show 0 < 2*R by positivity)).mp H
    nlinarith only [H']
  have htmaxr : tmax*(2*R) ≤ rgraph/2 := by
    have H : tmax ≤ rgraph/(4*R) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have H' := (le_div_iff₀ (show 0 < 4*R by positivity)).mp H
    nlinarith only [H']
  have htmaxM : tmax*M ≤ δmon := by
    have H : tmax ≤ δmon/(M+1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have H' := (le_div_iff₀ (show 0 < M+1 by positivity)).mp H
    nlinarith only [H',htmax]
  have htmaxαM : tmax^α*M ≤ δmon := by
    have H : tmax ≤ (δmon/(M+1))^(α⁻¹) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have H' := Real.rpow_le_rpow htmax.le H hαpos.le
    rw [Real.rpow_inv_rpow (by positivity) hαpos.ne'] at H'
    have H'' := (le_div_iff₀ (show 0 < M+1 by positivity)).mp H'
    nlinarith only [H'',Real.rpow_pos_of_pos htmax α]
  have htmaxε : Astep*(θ^n)⁻¹*tmax^α ≤ εmax := by
    have H : tmax ≤ (εmax/(Astep*(θ^n)⁻¹+1))^(α⁻¹) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have H' := Real.rpow_le_rpow htmax.le H hαpos.le
    rw [Real.rpow_inv_rpow (by positivity) hαpos.ne'] at H'
    have H'' := (le_div_iff₀ (show 0 < Astep*(θ^n)⁻¹+1 by positivity)).mp H'
    nlinarith only [H'',Real.rpow_pos_of_pos htmax α]
  have hcontract : (θ^(1-α)+Bstep*δmon)*D+3*Bstep ≤ D := by
    have H : θ^(1-α)+Bstep*δmon ≤ 1/2 := by linarith only [hθsmall,hsmallproduct]
    have HD : 0 ≤ D := by linarith only [hD]
    have H' := mul_le_mul_of_nonneg_right H HD
    dsimp [D] at H' ⊢
    nlinarith only [H']
  have hsmall : (Astep*(θ^n)⁻¹*tmax^α)*(3+D)/(1-ρ) ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right htmaxε (show 0 ≤ 3+D by linarith only [hD])
    have he : εmax*(3+D) = 1-ρ :=
      div_mul_cancel₀ _ (by linarith only [hD])
    rw [he] at H
    exact (div_le_one (by linarith only [hρ1])).mpr H
  have hscales (t : ℝ) (ht : 0 < t) (htt : t ≤ tmax) :
      t ≤ 1 ∧ t*R ≤ κ/2 ∧ t*(2*R) ≤ rgraph/2 ∧ t*M ≤ δmon ∧ t^α*M ≤ δmon := by
    exact ⟨htt.trans htmax1,
      (mul_le_mul_of_nonneg_right htt hR.le).trans htmaxκ,
      (mul_le_mul_of_nonneg_right htt (by positivity)).trans htmaxr,
      (mul_le_mul_of_nonneg_right htt hM0).trans htmaxM,
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le htt hαpos.le) hM0).trans htmaxαM⟩
  clear_value tmax σ
  classical
  let zbase (a : V) : Block p × Block q :=
    (((F₁.box i').chart.symm ⟨a,(hsubU (hVU a.property)).1⟩).val.1,
      ((F₂.box j').chart.symm ⟨a,(hsubU (hVU a.property)).2⟩).val.1)
  have Hfamilies' (a : V) := Hfamilies a a.property
    (hsubU (hVU a.property)).1 (hsubU (hVU a.property)).2
  choose e hes hea het helip hefull Hgraph using Hfamilies'
  let Scale := {t : ℝ // 0 < t ∧ t ≤ tmax}
  have hrow_anchor (t : Scale) (j : J) : ‖((0 : Block p),t.val • B j)‖ ≤ κ := by
    have H := (hscales t.val t.property.1 t.property.2).2.1
    simp only [Prod.norm_def,norm_zero,norm_smul,Real.norm_of_nonneg t.property.1.le]
    apply max_le hκ.le
    have hb := mul_le_mul_of_nonneg_left (hB j) t.property.1.le
    nlinarith only [hb,H,hκ]
  have hcol_anchor (t : Scale) (i : I) : ‖(t.val • A i,(0 : Block q))‖ ≤ κ := by
    have H := (hscales t.val t.property.1 t.property.2).2.1
    simp only [Prod.norm_def,norm_zero,norm_smul,Real.norm_of_nonneg t.property.1.le]
    apply max_le ?_ hκ.le
    have ha := mul_le_mul_of_nonneg_left (hA i) t.property.1.le
    nlinarith only [ha,H,hκ]
  have Hrows (a : V) (t : Scale) (j : J) :=
    Hgraph a ((0 : Block p),t.val • B j) (hrow_anchor t j)
  have Hcols (a : V) (t : Scale) (i : I) :=
    Hgraph a (t.val • A i,(0 : Block q)) (hcol_anchor t i)
  choose φ ψrow hφanchor hψrowanchor hφfull hψrowfull hφscalar hψrowscalar
    hφlip hψrowlip using Hrows
  choose φcol ψ hφcolanchor hψanchor hφcolfull hψfull hφcolscalar hψscalar
    hφcollip hψlip using Hcols
  have hrgraph_s : rgraph ≤ s/8 := min_le_right _ _
  clear_value rgraph
  have hm_p (t : Scale) (z : Block p) (hz : z ∈ Metric.ball 0 (2*R)) :
      t.val • z ∈ Metric.ball 0 rgraph := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg t.property.1.le]
    have hz' : ‖z‖ < 2*R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have H := (hscales t.val t.property.1 t.property.2).2.2.1
    exact (mul_lt_mul_of_pos_left hz' t.property.1).trans_le (H.trans (by linarith only [hrgraph]))
  have hm_q (t : Scale) (z : Block q) (hz : z ∈ Metric.ball 0 (2*R)) :
      t.val • z ∈ Metric.ball 0 rgraph := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg t.property.1.le]
    have hz' : ‖z‖ < 2*R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have H := (hscales t.val t.property.1 t.property.2).2.2.1
    exact (mul_lt_mul_of_pos_left hz' t.property.1).trans_le (H.trans (by linarith only [hrgraph]))
  have hφslope (a : V) (t : Scale) (j : J) (u : Block p)
      (hu : u ∈ Metric.ball 0 rgraph) : ‖fderiv ℝ (φ a t j) u‖ ≤ 2*σ := by
    have hu' := Metric.ball_subset_ball hrgraph_s hu
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    filter_upwards [Metric.isOpen_ball.mem_nhds hu'] with v hv
    exact hφlip a t j v hv u hu'
  have hψslope (a : V) (t : Scale) (i : I) (u : Block q)
      (hu : u ∈ Metric.ball 0 rgraph) : ‖fderiv ℝ (ψ a t i) u‖ ≤ 2*σ := by
    have hu' := Metric.ball_subset_ball hrgraph_s hu
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    filter_upwards [Metric.isOpen_ball.mem_nhds hu'] with v hv
    exact hψlip a t i v hv u hu'
  have hφzero (a : V) (t : Scale) (j : J) : ‖φ a t j 0‖ ≤ t.val*(2*R) := by
    rw [hφanchor a t j,norm_smul,Real.norm_of_nonneg t.property.1.le]
    apply mul_le_mul_of_nonneg_left _ t.property.1.le
    exact (hB j).trans (by linarith only [hR])
  have hψzero (a : V) (t : Scale) (i : I) : ‖ψ a t i 0‖ ≤ t.val*(2*R) := by
    rw [hψanchor a t i,norm_smul,Real.norm_of_nonneg t.property.1.le]
    apply mul_le_mul_of_nonneg_left _ t.property.1.le
    exact (hA i).trans (by linarith only [hR])
  have hM₁ : Cregraph₁ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM₂ : Cregraph₂ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  clear_value M
  have Hrow (a : V) (t : Scale) (j : J) (c : BlockBidegreeIndex p q n → ℝ) :=
    sampled_horizontal_residual_holder hn hαpos hαlt hM hM0 hrgraph hrgraph1
      (show 0 ≤ 2*σ by positivity) hδmon.le hδmon1 t.property.1
      (hscales t.val t.property.1 t.property.2).1 (show 0 < 2*R by positivity)
      hσδ.1 hσδ.2 (hscales t.val t.property.1 t.property.2).2.2.2.1
      (hscales t.val t.property.1 t.property.2).2.2.2.2
      (φ a t j) (fun z ↦ h (e a (zbase a+z)))
      (((hφfull a t j).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₁)
      (((hφscalar a t j).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₁)
      (hφslope a t j) (hφzero a t j) (hm_p t) c
  have Hcol (a : V) (t : Scale) (i : I) (c : BlockBidegreeIndex p q n → ℝ) :=
    sampled_vertical_residual_holder hn hαpos hαlt hM hM0 hrgraph hrgraph1
      (show 0 ≤ 2*σ by positivity) hδmon.le hδmon1 t.property.1
      (hscales t.val t.property.1 t.property.2).1 (show 0 < 2*R by positivity)
      hσδ.1 hσδ.2 (hscales t.val t.property.1 t.property.2).2.2.2.1
      (hscales t.val t.property.1 t.property.2).2.2.2.2
      (ψ a t i) (fun z ↦ h (e a (zbase a+z)))
      (((hψfull a t i).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₂)
      (((hψscalar a t i).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₂)
      (hψslope a t i) (hψzero a t i) (hm_q t) c
  let Φ (a : V) (t : Scale) (j : J) (u : Block p) :=
    t.val⁻¹ • (φ a t j (t.val • u)-φ a t j 0)
  let Ψ (a : V) (t : Scale) (i : I) (v : Block q) :=
    t.val⁻¹ • (ψ a t i (t.val • v)-ψ a t i 0)
  have hΦ0 (a : V) (t : Scale) (j : J) : Φ a t j 0 = 0 := by
    simp only [Φ,smul_zero,sub_self]
  have hΨ0 (a : V) (t : Scale) (i : I) : Ψ a t i 0 = 0 := by
    simp only [Ψ,smul_zero,sub_self]
  have hΦlip (a : V) (t : Scale) (j : J) :
      ∀ u ∈ Metric.closedBall (0 : Block p) R, ∀ v ∈ Metric.closedBall 0 R,
        ‖Φ a t j u-Φ a t j v‖ ≤ (2*σ)*‖u-v‖ := by
    intro u hu v hv
    have hu' : u ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖u‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
      linarith only [H,hR]
    have hv' : v ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
      linarith only [H,hR]
    exact normalized_graph_slope t.property.1 (φ a t j) u v
      (hφlip a t j _ (Metric.ball_subset_ball hrgraph_s (hm_p t u hu'))
        _ (Metric.ball_subset_ball hrgraph_s (hm_p t v hv')))
  have hΨlip (a : V) (t : Scale) (i : I) :
      ∀ u ∈ Metric.closedBall (0 : Block q) R, ∀ v ∈ Metric.closedBall 0 R,
        ‖Ψ a t i u-Ψ a t i v‖ ≤ (2*σ)*‖u-v‖ := by
    intro u hu v hv
    have hu' : u ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖u‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
      linarith only [H,hR]
    have hv' : v ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
      linarith only [H,hR]
    exact normalized_graph_slope t.property.1 (ψ a t i) u v
      (hψlip a t i _ (Metric.ball_subset_ball hrgraph_s (hm_q t u hu'))
        _ (Metric.ball_subset_ball hrgraph_s (hm_q t v hv')))
  have Hcrossed (a : V) (t : Scale) := Hresidual (2*σ) (by positivity) hσε
    (Φ a t) (Ψ a t) (hΦ0 a t) (hΨ0 a t) (hΦlip a t) (hΨlip a t)
  choose grid hgrid_equations hgrid_close Hgrid_remainder using Hcrossed
  have Hinterpolant (a : V) (t : Scale) := Hgrid (grid a t)
    ((hgrid_close a t).trans_lt hσgrid) t.val t.property.1
      (fun z ↦ h (e a (zbase a+z)))
  choose coeff hcoeff_interpolates hcoeff_weighted using Hinterpolant
  let Target := {w : Block p × Block q // ‖w‖ ≤ R/4}
  have htarget_anchor (t : Scale) (w : Target) : ‖t.val • w.val‖ ≤ κ := by
    rw [norm_smul,Real.norm_of_nonneg t.property.1.le]
    have H := (hscales t.val t.property.1 t.property.2).2.1
    have Hw := mul_le_mul_of_nonneg_left w.property t.property.1.le
    nlinarith only [Hw,H,hκ]
  have Htargets (a : V) (t : Scale) (w : Target) :=
    Hgraph a (t.val • w.val) (htarget_anchor t w)
  choose φtarget ψtarget hφtargetanchor hψtargetanchor hφtargetfull hψtargetfull
    hφtargetscalar hψtargetscalar hφtargetlip hψtargetlip using Htargets
  have htarget_coord (w : Target) : ‖w.val.1‖ ≤ R/4 ∧ ‖w.val.2‖ ≤ R/4 :=
    ⟨(le_max_left _ _).trans w.property,(le_max_right _ _).trans w.property⟩
  have htarget_mem (w : Target) : w.val.2 ∈ Metric.ball 0 (2*R) := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith only [(htarget_coord w).2,hR]
  have hψtargetzero (a : V) (t : Scale) (w : Target) :
      ‖ψtarget a t w 0‖ ≤ t.val*(2*R) := by
    have H := hψtargetlip a t w 0 (Metric.mem_ball_self (by linarith only [hs]))
      (t.val • w.val.2) (Metric.ball_subset_ball hrgraph_s (hm_q t _ (htarget_mem w)))
    have He : ψtarget a t w (t.val • w.val.2) = t.val • w.val.1 :=
      hψtargetanchor a t w
    rw [He,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg t.property.1.le] at H
    have Hnorm : ‖ψtarget a t w 0‖ ≤
        (2*σ)*(t.val*‖w.val.2‖)+‖t.val • w.val.1‖ := by
      calc
        _ = ‖(ψtarget a t w 0-t.val • w.val.1)+t.val • w.val.1‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖ψtarget a t w 0-t.val • w.val.1‖+‖t.val • w.val.1‖ := norm_add_le _ _
        _ ≤ _ := add_le_add H le_rfl
    rw [norm_smul,Real.norm_of_nonneg t.property.1.le] at Hnorm
    have H₁ := mul_le_mul_of_nonneg_left (htarget_coord w).1 t.property.1.le
    have H₂ := mul_le_mul_of_nonneg_left (htarget_coord w).2 t.property.1.le
    have H₃ := mul_le_mul_of_nonneg_left H₂ (show 0 ≤ 2*σ by positivity)
    have Hσ := mul_le_mul_of_nonneg_right hσq (mul_nonneg t.property.1.le hR.le)
    nlinarith only [Hnorm,H₁,H₃,Hσ,mul_pos t.property.1 hR]
  have hψtargetslope (a : V) (t : Scale) (w : Target) (u : Block q)
      (hu : u ∈ Metric.ball 0 rgraph) : ‖fderiv ℝ (ψtarget a t w) u‖ ≤ 2*σ := by
    have hu' := Metric.ball_subset_ball hrgraph_s hu
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    filter_upwards [Metric.isOpen_ball.mem_nhds hu'] with v hv
    exact hψtargetlip a t w v hv u hu'
  have Htarget (a : V) (t : Scale) (w : Target) (c : BlockBidegreeIndex p q n → ℝ) :=
    sampled_vertical_residual_holder hn hαpos hαlt hM hM0 hrgraph hrgraph1
      (show 0 ≤ 2*σ by positivity) hδmon.le hδmon1 t.property.1
      (hscales t.val t.property.1 t.property.2).1 (show 0 < 2*R by positivity)
      hσδ.1 hσδ.2 (hscales t.val t.property.1 t.property.2).2.2.2.1
      (hscales t.val t.property.1 t.property.2).2.2.2.2
      (ψtarget a t w) (fun z ↦ h (e a (zbase a+z)))
      (((hψtargetfull a t w).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₂)
      (((hψtargetscalar a t w).mono (Metric.ball_subset_ball hrgraph_s)).mono_bound hM₂)
      (hψtargetslope a t w) (hψtargetzero a t w) (hm_q t) c
  let Ψtarget (a : V) (t : Scale) (w : Target) (v : Block q) :=
    t.val⁻¹ • (ψtarget a t w (t.val • v)-ψtarget a t w 0)
  have hΨtarget0 (a : V) (t : Scale) (w : Target) : Ψtarget a t w 0 = 0 := by
    simp only [Ψtarget,smul_zero,sub_self]
  have hΨtargetlip (a : V) (t : Scale) (w : Target) :
      ∀ u ∈ Metric.closedBall (0 : Block q) R, ∀ v ∈ Metric.closedBall 0 R,
        ‖Ψtarget a t w u-Ψtarget a t w v‖ ≤ (2*σ)*‖u-v‖ := by
    intro u hu v hv
    have hu' : u ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖u‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
      linarith only [H,hR]
    have hv' : v ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
      linarith only [H,hR]
    exact normalized_graph_slope t.property.1 (ψtarget a t w) u v
      (hψtargetlip a t w _ (Metric.ball_subset_ball hrgraph_s (hm_q t u hu'))
        _ (Metric.ball_subset_ball hrgraph_s (hm_q t v hv')))
  let Fres (a : V) (t : Scale) (c : BlockBidegreeIndex p q n → ℝ)
      (z : Block p × Block q) := h (e a (zbase a+t.val • z))-
        ∑ i, c i*blockBimonomial i (t.val • z)
  let Kres (t : Scale) (c : BlockBidegreeIndex p q n → ℝ) :=
    t.val^((n:ℝ)+α)*(M+Amon*lowCoefficientMagnitude blockBidegree n c+
      (Bmon*δmon)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c)
  have hKres (t : Scale) (c : BlockBidegreeIndex p q n → ℝ) : 0 ≤ Kres t c := by
    have hlow : 0 ≤ lowCoefficientMagnitude blockBidegree n c := by
      unfold lowCoefficientMagnitude
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    have hhigh : 0 ≤ highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c := by
      unfold highCoefficientMagnitude
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg t.property.1.le _)
      · exact le_rfl
    dsimp only [Kres]
    exact mul_nonneg (Real.rpow_nonneg t.property.1.le _)
      (add_nonneg (add_nonneg hM0 (mul_nonneg hAmon hlow))
        (mul_nonneg (mul_nonneg hBmon hδmon.le) hhigh))
  have hΦeval (a : V) (t : Scale) (j : J) (u : Block p) :
      B j+Φ a t j u = t.val⁻¹ • φ a t j (t.val • u) := by
    dsimp [Φ]
    rw [smul_sub,hφanchor a t j,smul_smul,inv_mul_cancel₀ t.property.1.ne',one_smul]
    abel
  have hΨtargeteval (a : V) (t : Scale) (w : Target) (v : Block q) :
      w.val.1-Ψtarget a t w w.val.2+Ψtarget a t w v =
        t.val⁻¹ • ψtarget a t w (t.val • v) := by
    have He : ψtarget a t w (t.val • w.val.2) = t.val • w.val.1 :=
      hψtargetanchor a t w
    dsimp [Ψtarget]
    rw [He,smul_sub,smul_sub,smul_smul,
      inv_mul_cancel₀ t.property.1.ne',one_smul]
    abel
  have Herror (a : V) (t : Scale) (w : Target) :
      |Fres a t (coeff a t) w.val| ≤ (Lgrid+1)^2*Kres t (coeff a t)*R^((n:ℝ)+α) := by
    have Hr (j : J) :
        ContDiffOn ℝ n (fun u ↦ Fres a t (coeff a t) (u,B j+Φ a t j u))
          (Metric.ball 0 (2*R)) ∧
        ∀ u ∈ Metric.ball (0:Block p) (2*R), ∀ v ∈ Metric.ball 0 (2*R),
          ‖iteratedFDeriv ℝ n (fun u ↦ Fres a t (coeff a t) (u,B j+Φ a t j u)) u-
            iteratedFDeriv ℝ n (fun u ↦ Fres a t (coeff a t) (u,B j+Φ a t j u)) v‖ ≤
            Kres t (coeff a t)*‖u-v‖^α := by
      simpa only [Fres,Kres,Amon,Bmon,Function.comp_def,hΦeval] using Hrow a t j (coeff a t)
    have Hv :
        ContDiffOn ℝ n (Fres a t (coeff a t) ∘
          (fun v ↦ (w.val.1-Ψtarget a t w w.val.2+Ψtarget a t w v,v)))
          (Metric.ball 0 (2*R)) ∧
        ∀ u ∈ Metric.ball (0:Block q) (2*R), ∀ v ∈ Metric.ball 0 (2*R),
          ‖iteratedFDeriv ℝ n (Fres a t (coeff a t) ∘
              (fun v ↦ (w.val.1-Ψtarget a t w w.val.2+Ψtarget a t w v,v))) u-
            iteratedFDeriv ℝ n (Fres a t (coeff a t) ∘
              (fun v ↦ (w.val.1-Ψtarget a t w w.val.2+Ψtarget a t w v,v))) v‖ ≤
            Kres t (coeff a t)*‖u-v‖^α := by
      simpa only [Fres,Kres,Amon,Bmon,Function.comp_def,hΨtargeteval] using
        Htarget a t w (coeff a t)
    exact Hgrid_remainder a t (Fres a t (coeff a t)) α (Kres t (coeff a t))
      hαpos.le (hKres t (coeff a t))
      (fun i j ↦ by dsimp [Fres]; rw [hcoeff_interpolates a t (i,j),sub_self])
      (fun j ↦ (Hr j).1) (fun j ↦ (Hr j).2) w.val w.property
      (Ψtarget a t w) (hΨtarget0 a t w) (hΨtargetlip a t w) Hv.1 Hv.2
  clear_value Amon Bmon
  have hgrid_norm (a : V) (t : Scale) (k : I × J) : ‖grid a t k‖ ≤ R := by
    have Hd : ‖grid a t k-(A k.1,B k.2)‖ ≤ (2*σ)*R :=
      (norm_le_pi_norm (grid a t-(fun ij : I × J ↦ (A ij.1,B ij.2))) k).trans (hgrid_close a t)
    have Hb : ‖(A k.1,B k.2)‖ ≤ R/2 := max_le (hA k.1) (hB k.2)
    have Hσ := mul_le_mul_of_nonneg_right hσq hR.le
    calc
      _ = ‖(grid a t k-(A k.1,B k.2))+(A k.1,B k.2)‖ := by rw [sub_add_cancel]
      _ ≤ ‖grid a t k-(A k.1,B k.2)‖+‖(A k.1,B k.2)‖ := norm_add_le _ _
      _ ≤ (2*σ)*R+R/2 := add_le_add Hd Hb
      _ ≤ R := by nlinarith only [Hσ]
  let nextScale (t : Scale) : Scale := ⟨θ*t.val,mul_pos hθ t.property.1,
    (mul_le_mul_of_nonneg_right hθ1 t.property.1.le).trans (by simpa using t.property.2)⟩
  have hnext_target (a : V) (t : Scale) (k : I × J) :
      ‖θ • grid a (nextScale t) k‖ ≤ R/4 := by
    rw [norm_smul,Real.norm_of_nonneg hθ.le]
    have H := mul_le_mul_of_nonneg_left (hgrid_norm a (nextScale t) k) hθ.le
    have Hθ := mul_le_mul_of_nonneg_right hθeight hR.le
    nlinarith only [H,Hθ,hR]
  have hKres_upper (t : Scale) (c : BlockBidegreeIndex p q n → ℝ) :
      Kres t c ≤ t.val^((n:ℝ)+α)*Ecoef*(1+lowCoefficientMagnitude blockBidegree n c+
        δmon*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c) := by
    have hlow : 0 ≤ lowCoefficientMagnitude blockBidegree n c := by
      unfold lowCoefficientMagnitude
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    have hhigh : 0 ≤ highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c := by
      unfold highCoefficientMagnitude
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg t.property.1.le _)
      · exact le_rfl
    have hE₁ : M ≤ Ecoef := le_max_left _ _
    have hE₂ : Amon ≤ Ecoef := (le_max_left _ _).trans (le_max_right _ _)
    have hE₃ : Bmon ≤ Ecoef := (le_max_right _ _).trans (le_max_right _ _)
    have Hb : M+Amon*lowCoefficientMagnitude blockBidegree n c+
        (Bmon*δmon)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c ≤
        Ecoef*(1+lowCoefficientMagnitude blockBidegree n c+
          δmon*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c) := by
      calc
        _ ≤ Ecoef+Ecoef*lowCoefficientMagnitude blockBidegree n c+
            (Ecoef*δmon)*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val c :=
          add_le_add (add_le_add hE₁ (mul_le_mul_of_nonneg_right hE₂ hlow))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE₃ hδmon.le) hhigh)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left Hb (Real.rpow_nonneg t.property.1.le _)).trans_eq (by ring)
  clear_value Ecoef
  have Hstep (a : V) (t : Scale) :
      ∑ i, |coeff a (nextScale t) i-coeff a t i| *(θ*t.val)^blockBidegree i ≤
        Astep*t.val^((n:ℝ)+α)*(1+lowCoefficientMagnitude blockBidegree n (coeff a t)+
          δmon*highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) t.val (coeff a t)) := by
    let E := (Lgrid+1)^2*Kres t (coeff a t)*R^((n:ℝ)+α)
    have hE : 0 ≤ E := mul_nonneg (mul_nonneg (sq_nonneg _) (hKres t (coeff a t)))
      (Real.rpow_nonneg hR.le _)
    have Hsample (k : I × J) :
        |h (e a (zbase a+(nextScale t).val • grid a (nextScale t) k))-
          ∑ i, coeff a t i*blockBimonomial i ((nextScale t).val • grid a (nextScale t) k)| ≤ E := by
      have H := Herror a t ⟨θ • grid a (nextScale t) k,hnext_target a t k⟩
      have He : t.val • (θ • grid a (nextScale t) k) =
          (nextScale t).val • grid a (nextScale t) k := by
        simp only [nextScale,smul_smul,mul_comm]
      simpa only [Fres,He] using H
    have H := hcoeff_weighted a (nextScale t) (coeff a t) E hE Hsample
    apply H.trans
    have Hb := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hKres_upper t (coeff a t)) (sq_nonneg (Lgrid+1)))
        (Real.rpow_nonneg hR.le ((n:ℝ)+α))) hCgrid
    exact Hb.trans_eq (by dsimp [Astep]; ring)
  have Hrecurrence (a : V) (t : Scale) := weighted_increment_low_high_recurrence
    blockBidegree n α (coeff a t) (coeff a (nextScale t)) t.property.1
      (hscales t.val t.property.1 t.property.2).1 hθ hθ1 hAstep hδmon1 (Hstep a t)
  clear_value Astep
  have hsample_value (a : V) (t : Scale) (k : I × J) :
      |h (e a (zbase a+t.val • grid a t k))| ≤ M := by
    have hx : (grid a t k).1 ∈ Metric.ball 0 (2*R) := by
      rw [Metric.mem_ball,dist_zero_right]
      have H := (le_max_left _ _).trans (hgrid_norm a t k)
      linarith only [H,hR]
    have H := (hφscalar a t k.2).2.1 0 (Nat.zero_le n) (t.val • (grid a t k).1)
      (Metric.ball_subset_ball hrgraph_s (hm_p t _ hx))
    rw [norm_iteratedFDeriv_zero] at H
    have He : t.val • grid a t k =
        (t.val • (grid a t k).1,φ a t k.2 (t.val • (grid a t k).1)) := by
      apply Prod.ext
      · rfl
      · change t.val • (grid a t k).2 = _
        rw [(hgrid_equations a t k.1 k.2).2,hΦeval,smul_smul,
          mul_inv_cancel₀ t.property.1.ne',one_smul]
    rw [He]
    exact H.trans hM₁
  have Hweighted0 (a : V) (t : Scale) :
      ∑ i, |coeff a t i| *t.val^blockBidegree i ≤ Cgrid*M := by
    have H := hcoeff_weighted a t (fun _ ↦ 0) M hM0 (fun k ↦ by
      simpa only [zero_mul,Finset.sum_const_zero,sub_zero] using hsample_value a t k)
    simpa only [sub_zero] using H
  let scale (m : ℕ) : Scale := ⟨tmax*θ^m,mul_pos htmax (pow_pos hθ m),
    (mul_le_mul_of_nonneg_left (pow_le_one₀ hθ.le hθ1) htmax.le).trans_eq (mul_one tmax)⟩
  have hscale0 : (scale 0).val = tmax := by simp only [scale,pow_zero,mul_one]
  have hscale_next (m : ℕ) : scale (m+1) = nextScale (scale m) := by
    apply Subtype.ext
    dsimp [scale,nextScale]
    rw [pow_succ]
    ring
  let initialBound (i : BlockBidegreeIndex p q n) := Cgrid*M*(tmax^blockBidegree i)⁻¹
  have hinitialBound (i : BlockBidegreeIndex p q n) : 0 ≤ initialBound i := by
    dsimp [initialBound]
    positivity
  have hcoeff_initial (a : V) (i : BlockBidegreeIndex p q n) :
      |coeff a (scale 0) i| ≤ initialBound i := by
    have H := (Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) ↦ mul_nonneg (abs_nonneg (coeff a (scale 0) j))
        (pow_nonneg (scale 0).property.1.le _)) (Finset.mem_univ i)).trans (Hweighted0 a (scale 0))
    rw [hscale0] at H
    exact (le_div_iff₀ (pow_pos htmax _)).mpr H
  let Minit := 1+(∑ i, initialBound i)+
    ∑ i, initialBound i*tmax^((blockBidegree i:ℝ)-((n:ℝ)+α))
  have hsumInitial : 0 ≤ ∑ i, initialBound i := Finset.sum_nonneg (fun i _ ↦ hinitialBound i)
  have hsumInitialHigh : 0 ≤ ∑ i, initialBound i*tmax^((blockBidegree i:ℝ)-((n:ℝ)+α)) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hinitialBound i) (Real.rpow_nonneg htmax.le _))
  have hMinit : 1 ≤ Minit := by dsimp [Minit]; linarith only [hsumInitial,hsumInitialHigh]
  have hLinit (a : V) : lowCoefficientMagnitude blockBidegree n (coeff a (scale 0)) ≤ Minit := by
    have H : lowCoefficientMagnitude blockBidegree n (coeff a (scale 0)) ≤ ∑ i, initialBound i := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact hcoeff_initial a i
      · exact hinitialBound i
    exact H.trans (by dsimp [Minit]; linarith only [hsumInitialHigh])
  have hHinit (a : V) :
      highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) (scale 0).val (coeff a (scale 0)) ≤ D*Minit := by
    have H : highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) (scale 0).val
        (coeff a (scale 0)) ≤ ∑ i, initialBound i*tmax^((blockBidegree i:ℝ)-((n:ℝ)+α)) := by
      unfold highCoefficientMagnitude
      rw [hscale0]
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hcoeff_initial a i) (Real.rpow_nonneg htmax.le _)
      · exact mul_nonneg (hinitialBound i) (Real.rpow_nonneg htmax.le _)
    apply H.trans
    have HD := mul_le_mul_of_nonneg_right hD (show 0 ≤ Minit by linarith only [hMinit])
    dsimp [Minit] at HD ⊢
    nlinarith only [HD,hsumInitial]
  clear_value Minit
  have hscale_power (m : ℕ) : (scale m).val^α = tmax^α*ρ^m := by
    dsimp [scale,ρ]
    rw [Real.mul_rpow htmax.le (pow_nonneg hθ.le _),← Real.rpow_pow_comm hθ.le]
  have Hbootstrap (a : V) : ∀ m,
      lowCoefficientMagnitude blockBidegree n (coeff a (scale m)) ≤ 2*Minit ∧
      highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) (scale m).val (coeff a (scale m)) ≤ D*Minit := by
    apply low_high_coefficient_bootstrap
      (fun m ↦ lowCoefficientMagnitude blockBidegree n (coeff a (scale m)))
      (fun m ↦ highCoefficientMagnitude blockBidegree n ((n:ℝ)+α) (scale m).val (coeff a (scale m)))
      (show 0 ≤ Astep*(θ^n)⁻¹*tmax^α by positivity) hBstep
      (show 0 ≤ θ^(1-α)+Bstep*δmon by positivity) hρ.le hρ1 hMinit hD
      hcontract hsmall (hLinit a) (hHinit a)
    · intro m
      have H := (Hrecurrence a (scale m)).1
      rw [← hscale_next,hscale_power] at H
      convert H using 1; ring
    · intro m
      have H := (Hrecurrence a (scale m)).2
      change _ ≤ (θ^(1-α)+Bstep*δmon)*_+Bstep*(1+_) at H
      simpa only [hscale_next] using H
  clear_value Bstep D
  let Cstep := Astep*(1+2*Minit+δmon*(D*Minit))
  have hCstep : 0 ≤ Cstep := by
    have hMi : 0 ≤ Minit := le_trans (by norm_num) hMinit
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    dsimp [Cstep]
    positivity
  have Hstep_uniform (a : V) (m : ℕ) :
      ∑ i, |coeff a (scale (m+1)) i-coeff a (scale m) i| *
          (θ*(scale m).val)^blockBidegree i ≤ Cstep*(scale m).val^((n:ℝ)+α) := by
    rw [hscale_next]
    have H := Hstep a (scale m)
    have Hb := add_le_add (add_le_add (le_refl (1:ℝ)) (Hbootstrap a m).1)
      (mul_le_mul_of_nonneg_left (Hbootstrap a m).2 hδmon.le)
    have H' := mul_le_mul_of_nonneg_left Hb
      (mul_nonneg hAstep (Real.rpow_nonneg (scale m).property.1.le ((n:ℝ)+α)))
    exact H.trans (H'.trans_eq (by dsimp [Cstep]; ring))
  clear_value Cstep
  have Hcoefficient_step (a : V) (m : ℕ) (i : BlockBidegreeIndex p q n) :
      |coeff a (scale m) i-coeff a (scale (m+1)) i| ≤
        Cstep*(θ^blockBidegree i)⁻¹*(scale m).val^((n:ℝ)+α-(blockBidegree i:ℝ)) := by
    have H := (Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) ↦ mul_nonneg
        (abs_nonneg (coeff a (scale (m+1)) j-coeff a (scale m) j))
        (pow_nonneg (mul_nonneg hθ.le (scale m).property.1.le) _))
      (Finset.mem_univ i)).trans (Hstep_uniform a m)
    rw [abs_sub_comm] at H
    apply (mul_le_mul_iff_left₀ (pow_pos (mul_pos hθ (scale m).property.1) (blockBidegree i))).mp
    apply H.trans_eq
    rw [mul_pow,Real.rpow_sub (scale m).property.1,Real.rpow_natCast]
    field_simp [(scale m).property.1.ne']
  let LowIndex := {i : BlockBidegreeIndex p q n // blockBidegree i ≤ n}
  let β (i : LowIndex) := (n:ℝ)+α-(blockBidegree i.val:ℝ)
  let Ccoef (i : LowIndex) := Cstep*(θ^blockBidegree i.val)⁻¹*tmax^(β i)
  let ratio (i : LowIndex) := θ^(β i)
  have hβ (i : LowIndex) : 0 < β i := by
    have Hi : (blockBidegree i.val:ℝ) ≤ (n:ℝ) := by exact_mod_cast i.property
    dsimp [β]
    linarith only [Hi,hαpos]
  have hratio (i : LowIndex) : ratio i < 1 :=
    Real.rpow_lt_one hθ.le hθlt (hβ i)
  have Hcoefficient_geometric (a : V) (m : ℕ) (i : LowIndex) :
      |coeff a (scale m) i.val-coeff a (scale (m+1)) i.val| ≤ Ccoef i*ratio i^m := by
    have H := Hcoefficient_step a m i.val
    have He : (scale m).val^(β i) = tmax^(β i)*ratio i^m := by
      dsimp [scale,ratio]
      rw [Real.mul_rpow htmax.le (pow_nonneg hθ.le _),← Real.rpow_pow_comm hθ.le]
    change _ ≤ Cstep*(θ^blockBidegree i.val)⁻¹*(scale m).val^(β i) at H
    rw [He] at H
    exact H.trans_eq (by dsimp [Ccoef]; ring)
  obtain ⟨limitCoeff,hlimitCoeff,hcoefficient_tail,hweighted_tail⟩ :=
    uniform_geometric_coefficient_limits
      (fun (a : V) m (i : LowIndex) ↦ coeff a (scale m) i.val)
      Ccoef ratio hratio Hcoefficient_geometric
  have hlimitCoeff_bound (a : V) (i : LowIndex) : |limitCoeff a i| ≤ 2*Minit := by
    apply le_of_tendsto (hlimitCoeff a i).abs
    apply Filter.Eventually.of_forall
    intro m
    have H : |coeff a (scale m) i.val| ≤ lowCoefficientMagnitude blockBidegree n (coeff a (scale m)) := by
      have H := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) ↦ show 0 ≤ (if blockBidegree j ≤ n then |coeff a (scale m) j| else 0) from by
          split_ifs <;> positivity) (Finset.mem_univ i.val)
      simpa only [lowCoefficientMagnitude,ite_eq_left i.property] using H
    exact H.trans (Hbootstrap a m).1
  let lall (a : V) (i : BlockBidegreeIndex p q n) :=
    if hi : blockBidegree i ≤ n then limitCoeff a ⟨i,hi⟩ else 0
  let Btail (i : BlockBidegreeIndex p q n) := if hi : blockBidegree i ≤ n then
    Cstep*(θ^blockBidegree i)⁻¹/(1-ratio ⟨i,hi⟩) else D*Minit
  have hBtail (i : BlockBidegreeIndex p q n) : 0 ≤ Btail i := by
    dsimp [Btail]
    split_ifs with hi
    · exact div_nonneg (mul_nonneg hCstep (inv_nonneg.mpr (pow_nonneg hθ.le _)))
        (sub_pos.mpr (hratio ⟨i,hi⟩)).le
    · exact mul_nonneg (le_trans (by norm_num) hD) (le_trans (by norm_num) hMinit)
  have hlall (a : V) (i : BlockBidegreeIndex p q n) : |lall a i| ≤ 2*Minit := by
    dsimp [lall]
    split_ifs with hi
    · exact hlimitCoeff_bound a ⟨i,hi⟩
    · rw [abs_zero]
      linarith only [hMinit]
  have Htail_all (a : V) (m : ℕ) (i : BlockBidegreeIndex p q n) :
      |coeff a (scale m) i-lall a i| ≤
        Btail i*(scale m).val^((n:ℝ)+α-(blockBidegree i:ℝ)) := by
    by_cases hi : blockBidegree i ≤ n
    · have H := hcoefficient_tail a m ⟨i,hi⟩
      have He : (scale m).val^(β ⟨i,hi⟩) = tmax^(β ⟨i,hi⟩)*ratio ⟨i,hi⟩^m := by
        dsimp [scale,ratio]
        rw [Real.mul_rpow htmax.le (pow_nonneg hθ.le _),← Real.rpow_pow_comm hθ.le]
      simp only [lall,Btail,dite_eq_left hi]
      apply H.trans_eq
      change Ccoef ⟨i,hi⟩*ratio ⟨i,hi⟩^m/(1-ratio ⟨i,hi⟩) =
        Cstep*(θ^blockBidegree i)⁻¹/(1-ratio ⟨i,hi⟩)*(scale m).val^(β ⟨i,hi⟩)
      rw [He]
      dsimp [Ccoef]
      ring
    · have hii : n < blockBidegree i := by omega
      have H := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) ↦ show 0 ≤ (if n < blockBidegree j then
          |coeff a (scale m) j| *(scale m).val^((blockBidegree j:ℝ)-((n:ℝ)+α)) else 0) from by
          split_ifs
          · exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (scale m).property.1.le _)
          · exact le_rfl) (Finset.mem_univ i)
      simp only [ite_eq_left hii] at H
      have H' := H.trans (Hbootstrap a m).2
      simp only [lall,Btail,dite_eq_right hi,sub_zero]
      apply (mul_le_mul_iff_left₀
        (Real.rpow_pos_of_pos (scale m).property.1 ((blockBidegree i:ℝ)-((n:ℝ)+α)))).mp
      apply H'.trans_eq
      rw [mul_assoc,← Real.rpow_add (scale m).property.1]
      have he : (n:ℝ)+α-(blockBidegree i:ℝ)+((blockBidegree i:ℝ)-((n:ℝ)+α)) = 0 := by ring
      rw [he,Real.rpow_zero,mul_one]
  clear_value Btail
  obtain ⟨Cmono,hCmono⟩ := (isCompact_closedBall (0 : Block p × Block q) R).exists_bound_of_continuousOn
      ((continuous_pi (fun i : BlockBidegreeIndex p q n ↦ block_bimonomial_continuous i)).continuousOn)
  let Mmono := max 1 Cmono
  have hMmono : 0 ≤ Mmono := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hmonomial (i : BlockBidegreeIndex p q n) (w : Target) : |blockBimonomial i w.val| ≤ Mmono := by
    have hw : w.val ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact w.property.trans (by linarith only [hR])
    exact (norm_le_pi_norm (fun i : BlockBidegreeIndex p q n ↦ blockBimonomial i w.val) i).trans
      ((hCmono _ hw).trans (le_max_right _ _))
  let Qlimit (a : V) (z : Block p × Block q) := ∑ i, lall a i*blockBimonomial i z
  let Ctail := (∑ i, Btail i)*Mmono
  have hCtail : 0 ≤ Ctail := mul_nonneg (Finset.sum_nonneg (fun i _ ↦ hBtail i)) hMmono
  have Hpolynomial_tail (a : V) (m : ℕ) (w : Target) :
      |(∑ i, coeff a (scale m) i*blockBimonomial i ((scale m).val • w.val))-
        Qlimit a ((scale m).val • w.val)| ≤ Ctail*(scale m).val^((n:ℝ)+α) := by
    have Hterm (i : BlockBidegreeIndex p q n) :
        |(coeff a (scale m) i-lall a i)*blockBimonomial i ((scale m).val • w.val)| ≤
          (Btail i*Mmono)*(scale m).val^((n:ℝ)+α) := by
      rw [abs_mul,block_bimonomial_homogeneous,abs_mul,
        abs_of_pos (pow_pos (scale m).property.1 _)]
      calc
        _ ≤ (Btail i*(scale m).val^((n:ℝ)+α-(blockBidegree i:ℝ)))*
            ((scale m).val^blockBidegree i*Mmono) :=
          mul_le_mul (Htail_all a m i)
            (mul_le_mul_of_nonneg_left (hmonomial i w) (pow_nonneg (scale m).property.1.le _))
            (by positivity) (mul_nonneg (hBtail i) (Real.rpow_nonneg (scale m).property.1.le _))
        _ = _ := by
          rw [Real.rpow_sub (scale m).property.1,Real.rpow_natCast]
          field_simp [(scale m).property.1.ne']
    have He : (∑ i, coeff a (scale m) i*blockBimonomial i ((scale m).val • w.val))-
        Qlimit a ((scale m).val • w.val) =
        ∑ i, (coeff a (scale m) i-lall a i)*blockBimonomial i ((scale m).val • w.val) := by
      simp only [Qlimit,sub_mul,Finset.sum_sub_distrib]
    rw [He]
    calc
      _ ≤ ∑ i, |(coeff a (scale m) i-lall a i)*blockBimonomial i ((scale m).val • w.val)| :=
        by simpa only [Real.norm_eq_abs] using (norm_sum_le Finset.univ
          (fun i ↦ (coeff a (scale m) i-lall a i)*blockBimonomial i ((scale m).val • w.val)))
      _ ≤ ∑ i, (Btail i*Mmono)*(scale m).val^((n:ℝ)+α) := Finset.sum_le_sum (fun i _ ↦ Hterm i)
      _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]
  let Cerror := (Lgrid+1)^2*(M+Amon*(2*Minit)+(Bmon*δmon)*(D*Minit))*R^((n:ℝ)+α)+Ctail
  have hCerror : 0 ≤ Cerror := by
    have hMi : 0 ≤ Minit := (by norm_num : (0:ℝ) ≤ 1).trans hMinit
    have hD0 : 0 ≤ D := (by norm_num : (0:ℝ) ≤ 1).trans hD
    dsimp [Cerror]
    positivity
  have Happrox_scaled (a : V) (m : ℕ) (w : Target) :
      |h (e a (zbase a+(scale m).val • w.val))-Qlimit a ((scale m).val • w.val)| ≤
        Cerror*(scale m).val^((n:ℝ)+α) := by
    have H := Herror a (scale m) w
    have HK := add_le_add (add_le_add (le_refl M) (mul_le_mul_of_nonneg_left (Hbootstrap a m).1 hAmon))
      (mul_le_mul_of_nonneg_left (Hbootstrap a m).2 (mul_nonneg hBmon hδmon.le))
    have H' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left HK (Real.rpow_nonneg (scale m).property.1.le ((n:ℝ)+α)))
        (sq_nonneg (Lgrid+1))) (Real.rpow_nonneg hR.le ((n:ℝ)+α))
    calc
      _ ≤ |Fres a (scale m) (coeff a (scale m)) w.val|+
          |(∑ i, coeff a (scale m) i*blockBimonomial i ((scale m).val • w.val))-
            Qlimit a ((scale m).val • w.val)| := abs_sub_le _ _ _
      _ ≤ (Lgrid+1)^2*Kres (scale m) (coeff a (scale m))*R^((n:ℝ)+α)+
          Ctail*(scale m).val^((n:ℝ)+α) := add_le_add H (Hpolynomial_tail a m w)
      _ ≤ _ := (add_le_add H' le_rfl).trans_eq (by dsimp [Cerror]; ring)
  have hτ : 0 < (n:ℝ)+α := by positivity
  let rchart := tmax*R/4
  have hrchart : 0 < rchart := by dsimp [rchart]; positivity
  let Cchart := Cerror*(4/(θ*R))^((n:ℝ)+α)
  have hCchart : 0 ≤ Cchart := mul_nonneg hCerror (Real.rpow_nonneg (by positivity) _)
  have Happrox_chart (a : V) (z : Block p × Block q) (hz : ‖z‖ ≤ rchart) :
      |h (e a (zbase a+z))-Qlimit a z| ≤ Cchart*‖z‖^((n:ℝ)+α) := by
    by_cases hz0 : z = 0
    · subst z
      have htend : Filter.Tendsto
          (fun m ↦ Cerror*(scale m).val^((n:ℝ)+α)) Filter.atTop (nhds (0:ℝ)) := by
        have Ht : Filter.Tendsto (fun m : ℕ ↦ tmax*θ^m) Filter.atTop (nhds (0:ℝ)) := by
          simpa only [mul_zero] using
            (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθlt).const_mul tmax
        simpa only [scale,mul_zero] using (Ht.rpow_const_nhds_zero hτ).const_mul Cerror
      have H : |h (e a (zbase a+0))-Qlimit a 0| ≤ 0 := by
        apply ge_of_tendsto htend
        apply Filter.Eventually.of_forall
        intro m
        simpa only [smul_zero] using Happrox_scaled a m
          ⟨0,by simp only [norm_zero]; linarith only [hR]⟩
      simpa only [norm_zero,Real.zero_rpow hτ.ne',mul_zero] using H
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hden : 0 < tmax*R := mul_pos htmax hR
      obtain ⟨m,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
        (show 0 < 4*‖z‖/(tmax*R) by positivity)
        ((div_le_one hden).mpr (by dsimp [rchart] at hz; linarith only [hz])) hθ hθlt
      have hupper : ‖z‖ ≤ (scale m).val*R/4 := by
        have H := (div_le_iff₀ hden).mp hhi
        dsimp [scale]
        nlinarith only [H]
      have hlower : (scale m).val ≤ (4/(θ*R))*‖z‖ := by
        have H := (lt_div_iff₀ hden).mp hlo
        rw [pow_succ] at H
        have H' : (scale m).val ≤ (4*‖z‖)/(θ*R) := by
          apply (le_div_iff₀ (mul_pos hθ hR)).mpr
          dsimp [scale]
          nlinarith only [H]
        exact H'.trans_eq (by ring)
      have hw : ‖(scale m).val⁻¹ • z‖ ≤ R/4 := by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (scale m).property.1.le)]
        have H := mul_le_mul_of_nonneg_left hupper
          (inv_nonneg.mpr (scale m).property.1.le)
        have He : (scale m).val⁻¹*((scale m).val*R/4) = R/4 := by
          field_simp [(scale m).property.1.ne']
        exact H.trans_eq He
      have H := Happrox_scaled a m ⟨(scale m).val⁻¹ • z,hw⟩
      simp only [smul_smul,mul_inv_cancel₀ (scale m).property.1.ne',one_smul] at H
      calc
        _ ≤ Cerror*(scale m).val^((n:ℝ)+α) := H
        _ ≤ Cerror*((4/(θ*R))*‖z‖)^((n:ℝ)+α) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (scale m).property.1.le hlower hτ.le) hCerror
        _ = _ := by
          rw [Real.mul_rpow (by positivity : 0 ≤ 4/(θ*R)) (norm_nonneg z)]
          dsimp [Cchart]
          ring
  clear * - Happrox_chart Cchart hCchart rchart hrchart hτ Minit hMinit hlall
    Qlimit lall zbase e hes hea het helip hefull Cfull Rsource F₁ F₂ i' j'
    hsubU hVU hcoresU KU hρU hrU hV hxV hn hαpos hαlt
  clear_value Cchart rchart
  let Z (a : V) (y : Block (p+q)) := (e a).symm y-zbase a
  let KZ := max 1 (Cfull+Rsource)
  have hKZ : 1 ≤ KZ := le_max_left _ _
  have hKZ0 : 0 ≤ KZ := (by norm_num : (0:ℝ) ≤ 1).trans hKZ
  have hzbase (a : V) : ‖zbase a‖ ≤ Rsource := by
    apply max_le
    · exact (mem_ball_zero_iff.mp ((F₁.box i').chart.symm
        ⟨a,(hsubU (hVU a.property)).1⟩).property.1).le.trans (le_max_left _ _)
    · exact (mem_ball_zero_iff.mp ((F₂.box j').chart.symm
        ⟨a,(hsubU (hVU a.property)).2⟩).property.1).le.trans (le_max_right _ _)
  have HZ (a : V) : HasFiniteHolderBounds n α KZ (Z a) (Metric.ball a.val ρU) := by
    have H := (hefull a).add Metric.isOpen_ball
      (finiteHolderBounds_const n hn α (Metric.ball a.val ρU) (-zbase a))
    have Hb : Cfull+‖-zbase a‖ ≤ KZ := by
      rw [norm_neg]
      exact (add_le_add (le_refl Cfull) (hzbase a)).trans (le_max_right _ _)
    simpa only [Z,sub_eq_add_neg] using H.mono_bound Hb
  have HZ₁ (a : V) : HasFiniteHolderBounds n α KZ (fun y ↦ (Z a y).1)
      (Metric.ball a.val ρU) :=
    ((HZ a).clm_comp Metric.isOpen_ball (ContinuousLinearMap.fst ℝ (Block p) (Block q))).mono_bound
      (mul_le_of_le_one_left hKZ0 (ContinuousLinearMap.norm_fst_le ℝ (Block p) (Block q)))
  have HZ₂ (a : V) : HasFiniteHolderBounds n α KZ (fun y ↦ (Z a y).2)
      (Metric.ball a.val ρU) :=
    ((HZ a).clm_comp Metric.isOpen_ball (ContinuousLinearMap.snd ℝ (Block p) (Block q))).mono_bound
      (mul_le_of_le_one_left hKZ0 (ContinuousLinearMap.norm_snd_le ℝ (Block p) (Block q)))
  let Kpoly := (2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*KZ)^n*((2:ℝ)^(2*n+1)*KZ)^n
  have hKpoly : 0 ≤ Kpoly := by dsimp [Kpoly]; positivity
  have Hmono (a : V) (i : BlockBidegreeIndex p q n) :
      HasFiniteHolderBounds n α Kpoly (fun y ↦ blockBimonomial i (Z a y))
        (Metric.ball a.val ρU) :=
    block_bimonomial_graph_holder_bound hn i Metric.isOpen_ball (convex_ball _ _)
      hαpos hαlt hKZ (fun y ↦ (Z a y).1) (fun y ↦ (Z a y).2)
      (fun j ↦ block_coordinate_holder_bound hKZ0 Metric.isOpen_ball (HZ₁ a) j)
      (fun j ↦ block_coordinate_holder_bound hKZ0 Metric.isOpen_ball (HZ₂ a) j)
  let Kterm := (2:ℝ)^(2*n+1)*(2*Minit)*Kpoly
  have hKterm : 0 ≤ Kterm := by
    have hMi : 0 ≤ Minit := (by norm_num : (0:ℝ) ≤ 1).trans hMinit
    dsimp [Kterm]
    positivity
  let Kjet := (Fintype.card (BlockBidegreeIndex p q n):ℝ)*Kterm
  have hKjet : 0 ≤ Kjet := mul_nonneg (Nat.cast_nonneg _) hKterm
  let k (a : V) (y : Block (p+q)) := Qlimit a (Z a y)
  have Hk (a : V) : HasFiniteHolderBounds n α Kjet (k a) (Metric.ball a.val ρU) := by
    apply finite_sum_holder_uniform hn Metric.isOpen_ball
      (fun i y ↦ lall a i*blockBimonomial i (Z a y))
    intro i
    exact scalar_mul_holder_bound Metric.isOpen_ball (convex_ball _ _) hαpos hαlt
      (show 0 ≤ 2*Minit by linarith only [hMinit]) hKpoly
      ((finiteHolderBounds_const n hn α (Metric.ball a.val ρU) (lall a i)).mono_bound (hlall a i))
      (Hmono a i)
  let rfinal := min (ρU/2) (rchart/(2*((KU:ℝ)+1)))
  have hrfinal : 0 < rfinal := by dsimp [rfinal]; positivity
  have hrfρ : rfinal ≤ ρU := (min_le_left _ _).trans (by linarith only [hρU])
  have hrfchart : (KU:ℝ)*rfinal ≤ rchart := by
    have H := (le_div_iff₀ (show 0 < 2*((KU:ℝ)+1) by positivity)).mp
      (show rfinal ≤ rchart/(2*((KU:ℝ)+1)) from min_le_right _ _)
    nlinarith only [H,hrfinal,NNReal.coe_nonneg KU]
  let Cfinal := 1+Cchart*(KU:ℝ)^((n:ℝ)+α)+Kjet
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  have hCfinal_approx : Cchart*(KU:ℝ)^((n:ℝ)+α) ≤ Cfinal := by
    dsimp [Cfinal]
    linarith only [hKjet]
  have hCfinal_jet : Kjet ≤ Cfinal := by
    have H := mul_nonneg hCchart (Real.rpow_nonneg (NNReal.coe_nonneg KU) ((n:ℝ)+α))
    dsimp [Cfinal]
    linarith only [H]
  refine ⟨V,hV,hxV,Cfinal,rfinal,hCfinal,hrfinal,?_⟩
  intro a ha
  let av : V := ⟨a,ha⟩
  have hza : (e av).symm a = zbase av := by
    have H := (e av).left_inv (show zbase av ∈ (e av).source by
      rw [hes av]
      exact Metric.mem_ball_self hrU)
    have hecenter : e av (zbase av) = a := hea av
    rw [hecenter] at H
    exact H
  have hballΩ : Metric.ball a rfinal ⊆ Ω := by
    obtain ⟨_,_,_,_,_,HΩ,_⟩ := hcoresU a (hVU ha) (hsubU (hVU ha)).1 (hsubU (hVU ha)).2
    exact (Metric.ball_subset_ball hrfρ).trans HΩ
  refine ⟨(fun j ↦ iteratedFDeriv ℝ j.val (k av) a),k av,hballΩ,?_⟩
  intro y hy
  have hyρ : y ∈ Metric.ball a ρU := Metric.ball_subset_ball hrfρ hy
  have hZnorm : ‖Z av y‖ ≤ (KU:ℝ)*‖y-a‖ := by
    simpa only [Z,hza] using helip av y hyρ a (Metric.mem_ball_self hρU)
  have hZsmall : ‖Z av y‖ ≤ rchart := hZnorm.trans
    ((mul_le_mul_of_nonneg_left (show ‖y-a‖ ≤ rfinal from
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hy : ‖y-a‖ < rfinal).le)
      (NNReal.coe_nonneg KU)).trans hrfchart)
  have heval : e av (zbase av+Z av y) = y := by
    have He : zbase av+Z av y = (e av).symm y := by dsimp [Z]; abel
    rw [He]
    exact (e av).right_inv (het av hyρ)
  have happ := Happrox_chart av (Z av y) hZsmall
  rw [heval] at happ
  have happ' : |h y-k av y| ≤ Cfinal*‖y-a‖^((n:ℝ)+α) := by
    apply happ.trans
    calc
      Cchart*‖Z av y‖^((n:ℝ)+α) ≤ Cchart*((KU:ℝ)*‖y-a‖)^((n:ℝ)+α) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hZnorm hτ.le) hCchart
      _ = (Cchart*(KU:ℝ)^((n:ℝ)+α))*‖y-a‖^((n:ℝ)+α) := by
        rw [Real.mul_rpow (NNReal.coe_nonneg KU) (norm_nonneg _)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCfinal_approx (Real.rpow_nonneg (norm_nonneg _) _)
  have hline : ∀ t ∈ Icc (0:ℝ) 1, a+t • (y-a) ∈ Metric.ball a ρU := by
    intro t ht
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg (y-a)) ht.2).trans_lt
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hyρ)
  obtain ⟨hsmooth,hjets,htop⟩ := holder_affine_line_jets Metric.isOpen_ball
    hαpos.le hKjet (Hk av) a (y-a) hline
  exact ⟨happ',hsmooth,fun j hj ↦ hjets j hj.le,fun t ht ↦ (htop t ht).trans
    (mul_le_mul_of_nonneg_right hCfinal_jet (Real.rpow_nonneg (norm_nonneg _) _))⟩



end JourneLeafPolynomialApproximation
end HolomorphicAnosov
