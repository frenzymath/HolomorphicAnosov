import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open Filter Set
open scoped Topology BigOperators

namespace HolomorphicAnosov

/-- Compact recurrence for a finite tuple of unit complex numbers. This is the
agent-written compactness substitute for the rotation-frequency substep of
Manning (1974), Theorem A, p.425. Choose convergent powers z^(n_j). Differences
n_(2j)-n_j tend to infinity and their powers tend to one by division. -/
theorem finite_unit_powers_return
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧
      ∀ i, Tendsto (fun j ↦ z i ^ d j) atTop (𝓝 1) := by
  let S : Set (ι → ℂ) := {x | ∀ i, x i ∈ Metric.sphere 0 1}
  have hS : IsCompact S := isCompact_pi_infinite fun _ : ι ↦ isCompact_sphere (0 : ℂ) 1
  have hmem (m : ℕ) : (fun i ↦ z i ^ m) ∈ S := by
    intro i
    simp only [Metric.mem_sphere, dist_zero_right, norm_pow, hz, one_pow]
  obtain ⟨w,hw,φ,hφ,hlim⟩ := hS.tendsto_subseq hmem
  have hwne (i : ι) : w i ≠ 0 := by
    have hh := hw i
    simp only [Metric.mem_sphere, dist_zero_right] at hh
    exact norm_ne_zero_iff.mp (hh.trans_ne one_ne_zero)
  let d := fun j ↦ φ (2*j) - φ j
  have hd (j : ℕ) : j ≤ d j := by
    have hh := hφ.add_le_nat j j
    rw [← two_mul j] at hh
    dsimp [d]
    omega
  have hdtop : Tendsto d atTop atTop := tendsto_atTop_mono hd tendsto_id
  refine ⟨d,hdtop,?_⟩
  intro i
  have hi := (continuous_apply i).tendsto w |>.comp hlim
  have htwo : Tendsto (fun j : ℕ ↦ 2*j) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ by change j ≤ 2*j; omega) tendsto_id
  have hh := (hi.comp htwo).div hi (hwne i)
  have hzne : z i ≠ 0 := norm_ne_zero_iff.mp ((hz i).trans_ne one_ne_zero)
  have hpow (j : ℕ) : z i ^ d j = z i ^ φ (2*j) / z i ^ φ j := by
    dsimp only [d]
    rw [pow_sub₀ _ hzne (hφ.monotone (by omega)), div_eq_mul_inv]
  rw [div_self (hwne i)] at hh
  change Tendsto (fun j ↦ z i ^ φ (2*j) / z i ^ φ j) atTop (𝓝 1) at hh
  simpa only [← hpow] using hh

/-- A nonempty unit-circle determinant factor has no positive exponential
asymptotic. Compact recurrence gives powers d_j approaching the identity and
powers d_j+a approaching the a-th powers. A positive asymptotic first supplies
an a with positive product. Cross-multiplication of the two normalized limits
then gives c P(a)=0, a contradiction. This is an agent-written substitute for
the irrational rotation frequency argument in Manning (1974), Theorem A. -/
theorem finite_unit_product_no_exponential_limit
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ¬ Tendsto (fun m : ℕ ↦ (∏ i, ‖1 - z i ^ m‖) / r ^ m) atTop (𝓝 c) := by
  intro h
  let P := fun m : ℕ ↦ ∏ i, ‖1 - z i ^ m‖
  change Tendsto (fun m ↦ P m / r ^ m) atTop (𝓝 c) at h
  obtain ⟨a,ha⟩ := (h.eventually (eventually_gt_nhds hc)).exists
  have hPa : 0 < P a := (div_pos_iff_of_pos_right (pow_pos hr a)).mp ha
  obtain ⟨d,hd,hzlim⟩ := finite_unit_powers_return z hz
  have hda : Tendsto (fun j ↦ d j + a) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_add_right _ _) hd
  have hP0 : Tendsto (fun j ↦ P (d j)) atTop (𝓝 0) := by
    have hh := tendsto_finsetProd Finset.univ (fun i _ ↦
      ((tendsto_const_nhds (x := (1 : ℂ))).sub (hzlim i)).norm)
    simpa [P, Fintype.card_ne_zero] using hh
  have hPaLim : Tendsto (fun j ↦ P (d j + a)) atTop (𝓝 (P a)) := by
    have hh := tendsto_finsetProd Finset.univ (fun i _ ↦
      ((tendsto_const_nhds (x := (1 : ℂ))).sub ((hzlim i).mul_const (z i ^ a))).norm)
    simpa only [P, pow_add, one_mul] using hh
  have hleft := (h.comp hd).mul hPaLim
  have hright := ((h.comp hda).mul hP0).mul_const (r ^ a)
  have heq (j : ℕ) :
      (P (d j) / r ^ d j) * P (d j + a) =
      ((P (d j + a) / r ^ (d j + a)) * P (d j)) * r ^ a := by
    rw [pow_add]
    field_simp
  have hzero : c * P a = 0 := by
    apply tendsto_nhds_unique hleft
    simpa only [Function.comp_def, Pi.mul_apply, ← heq, mul_zero, zero_mul] using hright
  exact (mul_pos hc hPa).ne' hzero

/-- The expanding spectral factor after removal of its exponential magnitude
converges to one. Divide by z^m and use the geometric decay of z⁻¹. -/
theorem expanding_complex_factor_limit (z : ℂ) (hz : 1 < ‖z‖) :
    Tendsto (fun m : ℕ ↦ ‖1 - z ^ m‖ / ‖z‖ ^ m) atTop (𝓝 1) := by
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hz))
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have h := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hi).sub_const 1).norm
  have heq (m : ℕ) : ‖1 - z ^ m‖ / ‖z‖ ^ m = ‖(z⁻¹)^m - 1‖ := by
    rw [← norm_pow, ← norm_div, inv_pow]
    congr 1
    field_simp
  simpa only [heq, zero_sub, norm_neg, norm_one] using h

/-- The spectral product asymptotic in Manning's determinant calculation
excludes every unit-modulus factor. Split unit and nonunit factors. Remove the
product E of expanding magnitudes; the normalized nonunit product tends to one.
The assumed limit then gives a forbidden exponential limit for the unit part. -/
theorem spectral_product_excludes_unit
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (h : Tendsto (fun m : ℕ ↦ (∏ i, ‖1 - z i ^ m‖) / r ^ m) atTop (𝓝 c)) :
    ∀ i, ‖z i‖ ≠ 1 := by
  classical
  intro i hi
  let U := {j : ι // ‖z j‖ = 1}
  let V := {j : ι // ‖z j‖ ≠ 1}
  let : Nonempty U := ⟨⟨i,hi⟩⟩
  let e : V → ℝ := fun j ↦ if 1 < ‖z j.val‖ then ‖z j.val‖ else 1
  let E : ℝ := ∏ j, e j
  have he (j : V) : 0 < e j := by
    dsimp [e]
    split_ifs with hj
    · exact lt_trans zero_lt_one hj
    · exact zero_lt_one
  have hE : 0 < E := Finset.prod_pos (fun j _ ↦ he j)
  let Q := fun m : ℕ ↦ ∏ j : U, ‖1 - z j.val ^ m‖
  let R := fun m : ℕ ↦ ∏ j : V, ‖1 - z j.val ^ m‖
  have hfac (m : ℕ) : (∏ j, ‖1 - z j ^ m‖) = Q m * R m := by
    exact (Fintype.prod_subtype_mul_prod_subtype (fun j ↦ ‖z j‖ = 1)
      (fun j ↦ ‖1 - z j ^ m‖)).symm
  have hR : Tendsto (fun m ↦ R m / E ^ m) atTop (𝓝 1) := by
    have hj (j : V) : Tendsto (fun m : ℕ ↦ ‖1 - z j.val ^ m‖ / e j ^ m)
        atTop (𝓝 1) := by
      by_cases hgt : 1 < ‖z j.val‖
      · simpa only [e, ite_eq_left hgt] using expanding_complex_factor_limit (z j.val) hgt
      · have hlt : ‖z j.val‖ < 1 := lt_of_le_of_ne (le_of_not_gt hgt) j.property
        simpa [e, hgt] using
          ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_sub (1 : ℂ)).norm
    have hh := tendsto_finsetProd Finset.univ (fun j _ ↦ hj j)
    simpa only [Finset.prod_const_one, Finset.prod_div_distrib, ← Finset.prod_pow, E, R]
      using hh
  have hlim := h.div hR one_ne_zero
  have hevent : ∀ᶠ m : ℕ in atTop, R m / E ^ m ≠ 0 :=
    hR.eventually (eventually_ne_nhds one_ne_zero)
  have hlimQ : Tendsto (fun m ↦ Q m / (r / E) ^ m) atTop (𝓝 c) := by
    have heq : (fun m ↦ ((∏ j, ‖1 - z j ^ m‖) / r ^ m) / (R m / E ^ m))
        =ᶠ[atTop] (fun m ↦ Q m / (r / E) ^ m) := by
      filter_upwards [hevent] with m hm
      have hRm : R m ≠ 0 := by intro hzero; simp [hzero] at hm
      rw [hfac, div_pow]
      field_simp
    change Tendsto (fun m ↦ ((∏ j, ‖1 - z j ^ m‖) / r ^ m) / (R m / E ^ m))
      atTop (𝓝 (c / 1)) at hlim
    rw [div_one] at hlim
    exact hlim.congr' heq
  exact finite_unit_product_no_exponential_limit (fun j : U ↦ z j.val)
    (fun j ↦ j.property) (r / E) c (div_pos hr hE) hc hlimQ

/-- Polynomial spectral determinant identity, proved by factoring the polynomial
into constants and linear terms. The characteristic polynomial identity handles
linear terms, and multiplicativity handles their product, retaining all root
multiplicities without a triangularization hypothesis. -/
theorem matrix_det_polynomial_spectral_product
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (p : Polynomial ℂ) :
    Matrix.det (Polynomial.aeval A p) =
      (A.charpoly.roots.map (fun z ↦ p.eval z)).prod := by
  have hcard : A.charpoly.roots.card = Fintype.card ι := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  have hp := IsAlgClosed.splits p
  induction hp using Submonoid.closure_induction with
  | mem p hp =>
    obtain (⟨a,rfl⟩ | ⟨a,rfl⟩) := hp
    · simp [Algebra.algebraMap_eq_smul_one, hcard]
    · have hh := (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic A.charpoly_monic (-a)
      rw [Matrix.eval_charpoly] at hh
      have hneg : Matrix.scalar ι (-a) - A = -(A + Matrix.scalar ι a) := by
        simp [Matrix.scalar, sub_eq_add_neg]
      rw [hneg, Matrix.det_neg] at hh
      have hprod : (A.charpoly.roots.map (fun z ↦ -a - z)).prod =
          (-1 : ℂ) ^ Fintype.card ι * (A.charpoly.roots.map (fun z ↦ z + a)).prod := by
        simp_rw [show ∀ z : ℂ, -a - z = (-1) * (z+a) by intro z; ring]
        rw [Multiset.prod_map_mul]
        simp [hcard]
      rw [hprod] at hh
      have hh' := mul_left_cancel₀ (pow_ne_zero (Fintype.card ι) (neg_ne_zero.mpr one_ne_zero)) hh
      simpa [Polynomial.aeval_add, Matrix.algebraMap_eq_diagonal, Matrix.scalar] using hh'
  | one => simp
  | mul p q _ _ hp hq =>
    simp only [map_mul, Matrix.det_mul, Polynomial.eval_mul, Multiset.prod_map_mul, hp, hq]

/-- A positive pure exponential determinant asymptotic forces hyperbolicity.
The polynomial determinant identity and norm multiplicativity turn the given
limit into the finite spectral-product limit, whose unit factors were excluded
by compact recurrence. Eigenvalues are roots of the characteristic polynomial. -/
theorem matrix_hyperbolic_of_determinant_asymptotic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (h : Tendsto (fun m : ℕ ↦ ‖Matrix.det (1 - A ^ m)‖ / r ^ m) atTop (𝓝 c)) :
    ∀ μ : ℂ, Module.End.HasEigenvalue A.mulVecLin μ → ‖μ‖ ≠ 1 := by
  classical
  let l := A.charpoly.roots.toList
  let z : Fin l.length → ℂ := fun i ↦ l[i.val]
  have hprod (m : ℕ) : ‖Matrix.det (1 - A ^ m)‖ = ∏ i, ‖1 - z i ^ m‖ := by
    have hh := matrix_det_polynomial_spectral_product A (1 - Polynomial.X ^ m)
    simp only [map_sub, map_one, map_pow, Polynomial.aeval_X,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at hh
    rw [hh]
    have hnorm : ‖(A.charpoly.roots.map (fun x ↦ 1 - x^m)).prod‖ =
        (A.charpoly.roots.map (fun x ↦ ‖1 - x^m‖)).prod := by
      have hh := map_multiset_prod (normHom : ℂ →*₀ ℝ)
        (A.charpoly.roots.map (fun x ↦ 1-x^m))
      change ‖(A.charpoly.roots.map (fun x ↦ 1-x^m)).prod‖ =
        ((A.charpoly.roots.map (fun x ↦ 1-x^m)).map (fun x ↦ ‖x‖)).prod at hh
      simpa only [Multiset.map_map, Function.comp_def] using hh
    rw [hnorm]
    simpa only [z, l, Multiset.prod_map_toList] using
      (Fin.prod_univ_fun_getElem l (fun x ↦ ‖1 - x^m‖)).symm
  have hlim : Tendsto (fun m : ℕ ↦ (∏ i, ‖1 - z i ^ m‖) / r^m) atTop (𝓝 c) := by
    simpa only [hprod] using h
  have hno := spectral_product_excludes_unit z r c hr hc hlim
  intro μ hμ
  have hroot : A.charpoly.IsRoot μ := by
    simpa only [Matrix.charpoly_mulVecLin] using
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A.mulVecLin μ).mp hμ
  have hmem : μ ∈ l := Multiset.mem_toList.mpr
    ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr hroot)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
  change l[i.val] = μ at hi
  simpa only [z, hi] using hno i

/-- Even two-sided exponential comparability is impossible for a nonempty unit
spectral product. A rate above one contradicts boundedness; a rate below one
contradicts recurrence to a positive product; rate one contradicts recurrence
to the identity. This weaker counting input replaces exact asymptotics. -/
theorem finite_unit_product_no_exponential_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (r a b : ℝ) (hr : 0 < r) (ha : 0 < a) (_hb : 0 < b) :
    ¬ (∀ᶠ m : ℕ in atTop,
      a * r^m ≤ (∏ i, ‖1-z i^m‖) ∧ (∏ i, ‖1-z i^m‖) ≤ b*r^m) := by
  intro h
  let P := fun m : ℕ ↦ ∏ i, ‖1-z i^m‖
  change ∀ᶠ m : ℕ in atTop, a*r^m ≤ P m ∧ P m ≤ b*r^m at h
  obtain ⟨a₀,ha₀⟩ := h.exists
  have hPa : 0 < P a₀ := (mul_pos ha (pow_pos hr a₀)).trans_le ha₀.1
  obtain ⟨d,hd,hzlim⟩ := finite_unit_powers_return z hz
  have hda : Tendsto (fun j ↦ d j + a₀) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_add_right _ _) hd
  have hP0 : Tendsto (fun j ↦ P (d j)) atTop (𝓝 0) := by
    have hh := tendsto_finsetProd Finset.univ (fun i _ ↦
      ((tendsto_const_nhds (x := (1 : ℂ))).sub (hzlim i)).norm)
    simpa [P, Fintype.card_ne_zero] using hh
  have hPaLim : Tendsto (fun j ↦ P (d j+a₀)) atTop (𝓝 (P a₀)) := by
    have hh := tendsto_finsetProd Finset.univ (fun i _ ↦
      ((tendsto_const_nhds (x := (1 : ℂ))).sub ((hzlim i).mul_const (z i^a₀))).norm)
    simpa only [P, pow_add, one_mul] using hh
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · have hdecay : Tendsto (fun m : ℕ ↦ b*r^m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hlt).const_mul b
    have hzero : Tendsto P atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall (fun m ↦ Finset.prod_nonneg (fun i _ ↦ norm_nonneg _)))
        (h.mono fun m hm ↦ hm.2) hdecay
    exact hPa.ne' (tendsto_nhds_unique hPaLim (hzero.comp hda))
  · subst r
    have hevent : ∀ᶠ j : ℕ in atTop, a ≤ P (d j) := by
      filter_upwards [hd.eventually h] with j hj
      simpa only [one_pow,mul_one] using hj.1
    exact (not_le_of_gt ha) (ge_of_tendsto hP0 hevent)
  · have hbound (m : ℕ) : P m ≤ 2 ^ Fintype.card ι := by
      calc
        P m ≤ ∏ i : ι, (2 : ℝ) := by
          apply Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _)
          intro i _
          calc
            ‖1-z i^m‖ ≤ ‖(1 : ℂ)‖ + ‖z i^m‖ := norm_sub_le _ _
            _ = 2 := by simp [norm_pow,hz]; norm_num
        _ = _ := by simp
    have hdiverge := (tendsto_pow_atTop_atTop_of_one_lt hgt).const_mul_atTop ha
    obtain ⟨m,hm,hm'⟩ := ((hdiverge.eventually (eventually_gt_atTop
      (2 ^ Fintype.card ι : ℝ))).and h).exists
    exact (not_lt_of_ge ((hm'.1).trans (hbound m))) hm

/-- Two-sided exponential bounds on a finite spectral product exclude unit
factors. Normalize the nonunit part by its expanding rate E; it lies eventually
between one half and two. The unit part would then have two-sided exponential
bounds with rate r/E, contradicting compact recurrence. -/
theorem spectral_product_bounds_exclude_unit
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (r a b : ℝ) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b)
    (h : ∀ᶠ m : ℕ in atTop,
      a*r^m ≤ (∏ i, ‖1-z i^m‖) ∧ (∏ i, ‖1-z i^m‖) ≤ b*r^m) :
    ∀ i, ‖z i‖ ≠ 1 := by
  classical
  intro i hi
  let U := {j : ι // ‖z j‖ = 1}
  let V := {j : ι // ‖z j‖ ≠ 1}
  let : Nonempty U := ⟨⟨i,hi⟩⟩
  let e : V → ℝ := fun j ↦ if 1 < ‖z j.val‖ then ‖z j.val‖ else 1
  let E : ℝ := ∏ j, e j
  have he (j : V) : 0 < e j := by
    dsimp [e]
    split_ifs with hj
    · exact lt_trans zero_lt_one hj
    · exact zero_lt_one
  have hE : 0 < E := Finset.prod_pos (fun j _ ↦ he j)
  let Q := fun m : ℕ ↦ ∏ j : U, ‖1 - z j.val ^ m‖
  let R := fun m : ℕ ↦ ∏ j : V, ‖1 - z j.val ^ m‖
  have hfac (m : ℕ) : (∏ j, ‖1 - z j ^ m‖) = Q m * R m := by
    exact (Fintype.prod_subtype_mul_prod_subtype (fun j ↦ ‖z j‖ = 1)
      (fun j ↦ ‖1 - z j ^ m‖)).symm
  have hR : Tendsto (fun m ↦ R m / E ^ m) atTop (𝓝 1) := by
    have hj (j : V) : Tendsto (fun m : ℕ ↦ ‖1 - z j.val ^ m‖ / e j ^ m)
        atTop (𝓝 1) := by
      by_cases hgt : 1 < ‖z j.val‖
      · simpa only [e, ite_eq_left hgt] using expanding_complex_factor_limit (z j.val) hgt
      · have hlt : ‖z j.val‖ < 1 := lt_of_le_of_ne (le_of_not_gt hgt) j.property
        simpa [e, hgt] using
          ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_sub (1 : ℂ)).norm
    have hh := tendsto_finsetProd Finset.univ (fun j _ ↦ hj j)
    simpa only [Finset.prod_const_one, Finset.prod_div_distrib, ← Finset.prod_pow, E, R]
      using hh
  have hRbounds : ∀ᶠ m : ℕ in atTop, 1/2 < R m / E^m ∧ R m / E^m < 2 :=
    (hR.eventually (eventually_gt_nhds (by norm_num))).and
      (hR.eventually (eventually_lt_nhds (by norm_num)))
  apply finite_unit_product_no_exponential_bounds (fun j : U ↦ z j.val)
    (fun j ↦ j.property) (r/E) (a/2) (2*b) (div_pos hr hE)
    (by positivity) (by positivity)
  filter_upwards [h,hRbounds] with m hm hRm
  rw [hfac] at hm
  have hEm : 0 < E^m := pow_pos hE m
  have hQm : 0 ≤ Q m := Finset.prod_nonneg fun j _ ↦ norm_nonneg _
  have hRlo : E^m / 2 < R m := by
    have hh := (lt_div_iff₀ hEm).mp hRm.1
    linarith
  have hRhi : R m < 2 * E^m := (div_lt_iff₀ hEm).mp hRm.2
  have hlower : a*r^m ≤ 2*(Q m*E^m) := by nlinarith [mul_le_mul_of_nonneg_left hRhi.le hQm]
  have hupper : Q m*E^m ≤ 2*(b*r^m) := by nlinarith [mul_le_mul_of_nonneg_left hRlo.le hQm]
  constructor
  · rw [div_pow]
    calc
      a/2*(r^m/E^m) = (a*r^m/2)/E^m := by ring
      _ ≤ Q m := (div_le_iff₀ hEm).mpr (by nlinarith)
  · rw [div_pow]
    calc
      Q m ≤ (2*(b*r^m))/E^m := (le_div_iff₀ hEm).mpr hupper
      _ = (2*b)*(r^m/E^m) := by ring

/-- Two-sided exponential bounds on determinant counts already force
hyperbolicity. This is the bounded-count version of Manning's spectral argument;
it does not require a limit of the normalized counts. -/
theorem matrix_hyperbolic_of_determinant_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (r a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ᶠ m : ℕ in atTop,
      a*r^m ≤ ‖Matrix.det (1-A^m)‖ ∧ ‖Matrix.det (1-A^m)‖ ≤ b*r^m) :
    ∀ μ : ℂ, Module.End.HasEigenvalue A.mulVecLin μ → ‖μ‖ ≠ 1 := by
  classical
  let l := A.charpoly.roots.toList
  let z : Fin l.length → ℂ := fun i ↦ l[i.val]
  have hprod (m : ℕ) : ‖Matrix.det (1 - A ^ m)‖ = ∏ i, ‖1 - z i ^ m‖ := by
    have hh := matrix_det_polynomial_spectral_product A (1 - Polynomial.X ^ m)
    simp only [map_sub, map_one, map_pow, Polynomial.aeval_X,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at hh
    rw [hh]
    have hnorm : ‖(A.charpoly.roots.map (fun x ↦ 1 - x^m)).prod‖ =
        (A.charpoly.roots.map (fun x ↦ ‖1 - x^m‖)).prod := by
      have hh := map_multiset_prod (normHom : ℂ →*₀ ℝ)
        (A.charpoly.roots.map (fun x ↦ 1-x^m))
      change ‖(A.charpoly.roots.map (fun x ↦ 1-x^m)).prod‖ =
        ((A.charpoly.roots.map (fun x ↦ 1-x^m)).map (fun x ↦ ‖x‖)).prod at hh
      simpa only [Multiset.map_map, Function.comp_def] using hh
    rw [hnorm]
    simpa only [z, l, Multiset.prod_map_toList] using
      (Fin.prod_univ_fun_getElem l (fun x ↦ ‖1 - x^m‖)).symm
  have hbounds : ∀ᶠ m : ℕ in atTop,
      a*r^m ≤ (∏ i, ‖1-z i^m‖) ∧ (∏ i, ‖1-z i^m‖) ≤ b*r^m := by
    simpa only [hprod] using h
  have hno := spectral_product_bounds_exclude_unit z r a b hr ha hb hbounds
  intro μ hμ
  have hroot : A.charpoly.IsRoot μ := by
    simpa only [Matrix.charpoly_mulVecLin] using
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A.mulVecLin μ).mp hμ
  have hmem : μ ∈ l := Multiset.mem_toList.mpr
    ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr hroot)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
  change l[i.val] = μ at hi
  simpa only [z, hi] using hno i

/-- The trace of p(A) is the sum of p at the characteristic roots, retaining
multiplicity. Apply the polynomial determinant formula to 1+t p and compare
the coefficient of t. This avoids a triangularization theorem. -/
theorem matrix_trace_polynomial_spectral_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (p : Polynomial ℂ) :
    Matrix.trace (Polynomial.aeval A p) =
      (A.charpoly.roots.map (fun z ↦ p.eval z)).sum := by
  classical
  let C : Matrix ι ι ℂ := Polynomial.aeval A p
  let Q : Polynomial ℂ := Matrix.det ((1 : Matrix ι ι (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) • C.map Polynomial.C)
  let R : Polynomial ℂ := (A.charpoly.roots.map
    (fun z ↦ 1 + Polynomial.C (p.eval z) * Polynomial.X)).prod
  have heq : Q = R := by
    apply Polynomial.funext
    intro t
    have hh := matrix_det_polynomial_spectral_product A (1 + Polynomial.C t * p)
    have hQ : Q.eval t = Matrix.det (1 + t • C) := by
      change (Polynomial.evalRingHom t) ((1 + (Polynomial.X : Polynomial ℂ) • C.map Polynomial.C).det) = _
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp [mul_comm]
    rw [hQ]
    simp only [map_add, map_one, map_mul, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C] at hh
    rw [hh]
    simp only [R, Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    congr 2
    funext z
    rw [mul_comm]
  have hcoeff (s : Multiset ℂ) :
      ((s.map (fun z ↦ 1 + Polynomial.C z * Polynomial.X)).prod).coeff 0 = 1 ∧
      ((s.map (fun z ↦ 1 + Polynomial.C z * Polynomial.X)).prod).coeff 1 = s.sum := by
    induction s using Multiset.induction_on with
    | empty => simp [Polynomial.coeff_one]
    | cons z s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      constructor
      · simp [Polynomial.mul_coeff_zero, ih.1]
      · simp [Polynomial.mul_coeff_one, Polynomial.coeff_one, ih.1, ih.2, add_comm]
  have hR : R.coeff 1 = (A.charpoly.roots.map (fun z ↦ p.eval z)).sum := by
    simpa only [R, Multiset.map_map, Function.comp_def] using
      (hcoeff (A.charpoly.roots.map (fun z ↦ p.eval z))).2
  calc
    Matrix.trace (Polynomial.aeval A p) = Q.coeff 1 :=
      (Matrix.coeff_det_one_add_X_smul_one C).symm
    _ = _ := by rw [heq,hR]

/-- A stochastic convex combination attaining the unit-circle point 1 has every
positive-weight summand equal to 1. Real parts attain their common upper bound,
and the norm bound then forces the imaginary parts to vanish. -/
theorem stochastic_unit_average_eq_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (he : ∑ i, (w i : ℂ) * z i = 1) :
    ∀ i, 0 < w i → z i = 1 := by
  intro i hi
  have hre (j) : (z j).re ≤ 1 := (Complex.re_le_norm _).trans (hz j)
  have hsum : ∑ j, w j * (1 - (z j).re) = 0 := by
    have hh := congrArg Complex.re he
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.one_re] at hh
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hs, hh, sub_self]
  have hzero : w i * (1 - (z i).re) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ mul_nonneg (hw j) (sub_nonneg.mpr (hre j)))).mp hsum i (Finset.mem_univ _)
  have hr : (z i).re = 1 := by
    have := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hi)
    linarith
  have hn := Complex.normSq_eq_norm_sq (z i)
  have hn' : (z i).re ^ 2 + (z i).im ^ 2 = ‖z i‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using hn
  have him : (z i).im = 0 := by nlinarith [hz i, norm_nonneg (z i), sq_nonneg (z i).im]
  exact Complex.ext hr him

/-- Every eigenvalue of a real stochastic matrix lies in the closed unit disk. -/
theorem stochastic_eigenvalue_norm_le_one {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : ∀ i, ∑ j, (P i j : ℂ) * v j = μ * v i) : ‖μ‖ ≤ 1 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have : Nonempty ι := ⟨j⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖v j‖) Finset.univ_nonempty
  have hpos : 0 < ‖v i‖ := (norm_pos_iff.mpr hj).trans_le (hi j (Finset.mem_univ _))
  have hbound : ‖μ‖ * ‖v i‖ ≤ ‖v i‖ := by
    calc
      ‖μ‖ * ‖v i‖ = ‖∑ j, (P i j : ℂ) * v j‖ := by rw [he, norm_mul]
      _ ≤ ∑ j, ‖(P i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, P i j * ‖v j‖ := by simp [abs_of_nonneg, hp]
      _ ≤ ∑ j, P i j * ‖v i‖ := Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (hp i j)
      _ = ‖v i‖ := by rw [← Finset.sum_mul, hs, one_mul]
  nlinarith

/-- A unit-modulus stochastic eigenvalue is a root of unity. Positive transitions
from a largest eigenvector coordinate preserve its norm and multiply its value
by the eigenvalue. A repeated vertex in this finite successor orbit gives the
required positive power. -/
theorem stochastic_unit_eigenvalue_root_of_unity {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : ∀ i, ∑ j, (P i j : ℂ) * v j = μ * v i) (hμ : ‖μ‖ = 1) :
    ∃ q : ℕ, 0 < q ∧ μ^q = 1 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have : Nonempty ι := ⟨j⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖v j‖) Finset.univ_nonempty
  have hpos : 0 < ‖v i‖ := (norm_pos_iff.mpr hj).trans_le (hi j (Finset.mem_univ _))
  let S := {j : ι // ‖v j‖ = ‖v i‖}
  have hstep (a : S) : ∃ b : S, v b = μ * v a := by
    have hden : μ * v a ≠ 0 := by
      apply norm_pos_iff.mp
      simpa only [norm_mul, hμ, one_mul, a.property] using hpos
    have hz (j) : ‖v j / (μ * v a)‖ ≤ 1 := by
      rw [norm_div, norm_mul, hμ, one_mul, a.property]
      exact (div_le_one hpos).mpr (hi j (Finset.mem_univ _))
    have havg : ∑ j, (P a j : ℂ) * (v j / (μ * v a)) = 1 := by
      simp only [← mul_div_assoc, ← Finset.sum_div, he, div_self hden]
    obtain ⟨b,hb⟩ : ∃ b, 0 < P a b := by
      by_contra! h
      have hh : ∑ b, P a b = 0 := Finset.sum_eq_zero fun b _ ↦ le_antisymm (h b) (hp a b)
      linarith [hs a]
    have hbval : v b = μ * v a := by
      have := stochastic_unit_average_eq_one (P a) _ (hp a) (hs a) hz havg b hb
      exact (div_eq_one_iff_eq hden).mp this
    refine ⟨⟨b, ?_⟩, hbval⟩
    rw [hbval, norm_mul, hμ, one_mul, a.property]
  choose f hf using hstep
  let a : S := ⟨i,rfl⟩
  have hiter (k : ℕ) : v ((f^[k]) a) = μ^k * v i := by
    induction k with
    | zero => simp [a]
    | succ k ih => rw [Function.iterate_succ_apply', hf, ih, pow_succ]; ring
  obtain ⟨u,w,huw,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card S + 1) ↦ (f^[k.val]) a) (by simp)
  have hpow : μ^u.val = μ^w.val := by
    apply mul_right_cancel₀ (norm_pos_iff.mp hpos)
    rw [← hiter, ← hiter, heq]
  have hμ0 : μ ≠ 0 := by apply norm_ne_zero_iff.mp; rw [hμ]; norm_num
  have hneq : u.val ≠ w.val := fun h ↦ huw (Fin.ext h)
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · refine ⟨w.val-u.val, Nat.sub_pos_of_lt hlt, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero u.val hμ0)
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt), mul_one, hpow]
  · refine ⟨u.val-w.val, Nat.sub_pos_of_lt hgt, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero w.val hμ0)
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hgt), mul_one, hpow]

/-- On a common positive iterate, the trace of a nonempty stochastic matrix
converges to a positive integer. The characteristic roots on the unit circle
have finite order, while all other roots decay. -/
theorem stochastic_trace_common_iterate_limit {ι : Type*} [Fintype ι]
    [Nonempty ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1) :
    ∃ q c : ℕ, 0 < q ∧ 0 < c ∧
      Tendsto (fun m : ℕ ↦ Matrix.trace ((P.map Complex.ofReal) ^ (q*m)))
        atTop (𝓝 (c : ℂ)) := by
  classical
  let A : Matrix ι ι ℂ := P.map Complex.ofReal
  let l := A.charpoly.roots.toList
  let z (i : Fin l.length) := l[i.val]
  have heig (i : Fin l.length) : Module.End.HasEigenvalue A.mulVecLin (z i) := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly A.mulVecLin (z i)).mpr
    rw [Matrix.charpoly_mulVecLin]
    apply (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp
    exact Multiset.mem_toList.mp (List.getElem_mem i.isLt)
  have hspec (i : Fin l.length) : ‖z i‖ ≤ 1 ∧ (‖z i‖ = 1 → ∃ q : ℕ, 0 < q ∧ z i^q=1) := by
    obtain ⟨v,hv⟩ := (heig i).exists_hasEigenvector
    have he (j) : ∑ k, (P j k : ℂ) * v k = z i * v j := by
      have hh := congrFun hv.apply_eq_smul j
      simpa [A, Matrix.mulVec, dotProduct] using hh
    exact ⟨stochastic_eigenvalue_norm_le_one P hp hs _ v hv.2 he,
      stochastic_unit_eigenvalue_root_of_unity P hp hs _ v hv.2 he⟩
  have hord (i : Fin l.length) : ∃ q : ℕ, 0 < q ∧ (‖z i‖ = 1 → z i^q=1) := by
    by_cases hi : ‖z i‖ = 1
    · obtain ⟨q,hq,h⟩ := (hspec i).2 hi
      exact ⟨q,hq,fun _ ↦ h⟩
    · exact ⟨1,by omega,fun h ↦ (hi h).elim⟩
  choose d hdpos hd using hord
  let q := ∏ i, d i
  have hq : 0 < q := Finset.prod_pos fun i _ ↦ hdpos i
  have hdq (i) : d i ∣ q := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have hlim (i : Fin l.length) : Tendsto (fun m : ℕ ↦ z i^(q*m)) atTop
      (𝓝 (if ‖z i‖ = 1 then (1:ℂ) else 0)) := by
    split_ifs with hi
    · obtain ⟨b,hb⟩ := hdq i
      have hpow : z i^q=1 := by rw [hb, pow_mul, hd i hi, one_pow]
      simpa only [pow_mul, hpow, one_pow] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1:ℂ)) atTop (𝓝 1))
    · exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ((hspec i).1.lt_of_ne hi)).comp
        (tendsto_atTop_mono (fun m ↦ Nat.le_mul_of_pos_left m hq) tendsto_id)
  let U := Finset.univ.filter (fun i ↦ ‖z i‖ = 1)
  have hsum : (∑ i, if ‖z i‖ = 1 then (1:ℂ) else 0) = (U.card : ℂ) := by simp [U]
  have hone : Module.End.HasEigenvalue A.mulVecLin 1 := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ ↦ (1:ℂ))
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      ext i
      simp [A, Matrix.mulVec, dotProduct, ← Complex.ofReal_sum, hs]
    · intro h
      have := congrFun h (Classical.choice (inferInstance : Nonempty ι))
      simp at this
  have hone_root : (1:ℂ) ∈ l := by
    apply Multiset.mem_toList.mpr
    apply (Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr
    simpa only [Matrix.charpoly_mulVecLin] using
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A.mulVecLin 1).mp hone
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hone_root
  have hc : 0 < U.card := Finset.card_pos.mpr ⟨i, by simp [U,z,show l[i.val] = 1 from hi]⟩
  refine ⟨q,U.card,hq,hc,?_⟩
  have htrace (m : ℕ) : Matrix.trace (A^(q*m)) = ∑ i, z i^(q*m) := by
    have hh := matrix_trace_polynomial_spectral_sum A (Polynomial.X^(q*m))
    simp only [map_pow, Polynomial.aeval_X, Polynomial.eval_pow, Polynomial.eval_X] at hh
    rw [hh]
    simpa only [z,l,Multiset.sum_map_toList] using
      (Fin.sum_univ_fun_getElem l (fun x ↦ x^(q*m))).symm
  simpa only [← htrace, hsum] using tendsto_finsetSum Finset.univ (fun i _ ↦ hlim i)

open Matrix in
/-- A real linear map whose forward powers decay has positive det(I-A).
Along I-tA, 0≤t≤1, a kernel vector would remain constant while its norm is
bounded by a decaying A-orbit. Thus the determinant never vanishes; continuity
and its value 1 at t=0 keep its sign positive. -/
theorem det_one_sub_pos_of_power_decay
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hdec : ∀ v : ι → ℝ, Tendsto (fun m : ℕ ↦ A^m *ᵥ v) atTop (𝓝 0)) :
    0 < Matrix.det (1-A) := by
  have hne (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : Matrix.det (1-t • A) ≠ 0 := by
    have hker (v : ι → ℝ) (hv : (1-t • A) *ᵥ v=0) : v=0 := by
      have hrel : v=t • (A *ᵥ v) := by
        simpa only [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,sub_eq_zero] using hv
      have hpow (m : ℕ) : v=t^m • (A^m *ᵥ v) := by
        induction m with
        | zero => simp
        | succ m ih =>
          calc
            v = t^m • (A^m *ᵥ v) := ih
            _ = t^m • (A^m *ᵥ (t • (A *ᵥ v))) := by rw [← hrel]
            _ = t^(m+1) • (A^(m+1) *ᵥ v) := by
              simp only [Matrix.mulVec_smul,smul_smul,Matrix.mulVec_mulVec,pow_succ]
      have hb (m : ℕ) : ‖v‖ ≤ ‖A^m *ᵥ v‖ := by
        nth_rw 1 [hpow m]
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht.1 m)]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1 ht.2)
      have hlim := (continuous_norm.tendsto (0 : ι → ℝ)).comp (hdec v)
      have hz : ‖v‖ ≤ 0 := by
        simpa only [norm_zero] using ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
      exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
    have hinj : Function.Injective (fun v : ι → ℝ ↦ (1-t • A) *ᵥ v) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hker
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr h
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj))
  have hcont : Continuous (fun t : ℝ ↦ Matrix.det (1-t • A)) :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  by_contra! hn
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (zero_le_one : (0:ℝ) ≤ 1)
    hcont.continuousOn (show (0:ℝ) ∈ Set.Icc (Matrix.det (1-(1:ℝ) • A)) (Matrix.det (1-(0:ℝ) • A)) by
      simpa only [one_smul,zero_smul,sub_zero,Matrix.det_one,Set.mem_Icc] using And.intro hn zero_le_one)
  exact hne t ht he

open Matrix in
/-- The sign of det(I-U) for an expanding map is the sign of (-1)^d det(U).
The remaining factor is det(I-U inverse), positive by decay of inverse powers. -/
theorem det_one_sub_expanding_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℝ)
    (hUV : U*V=1)
    (hdec : ∀ v : ι → ℝ, Tendsto (fun m : ℕ ↦ V^m *ᵥ v) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ Matrix.det (1-U) = (-1:ℝ)^(Fintype.card ι)*Matrix.det U*c := by
  refine ⟨Matrix.det (1-V),det_one_sub_pos_of_power_decay V hdec,?_⟩
  have he : 1-U = -U*(1-V) := by rw [mul_sub,mul_one,neg_mul,hUV]; abel
  rw [he,Matrix.det_mul,Matrix.det_neg]

open Matrix in
/-- For a hyperbolic block decomposition the fixed-point displacement determinant
has sign (-1)^unstable_dimension times the orientation sign of the unstable map.
Both omitted factors are strictly positive by forward/backward decay. -/
theorem det_one_sub_hyperbolic_blocks_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Matrix ι ι ℝ) (U V : Matrix κ κ ℝ) (hUV : U*V=1)
    (hs : ∀ v : ι → ℝ, Tendsto (fun m : ℕ ↦ S^m *ᵥ v) atTop (𝓝 0))
    (hu : ∀ v : κ → ℝ, Tendsto (fun m : ℕ ↦ V^m *ᵥ v) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ Matrix.det (1-Matrix.fromBlocks S 0 0 U) =
      (-1:ℝ)^(Fintype.card κ)*Matrix.det U*c := by
  obtain ⟨c,hc,he⟩ := det_one_sub_expanding_factor U V hUV hu
  refine ⟨Matrix.det (1-S)*c,mul_pos (det_one_sub_pos_of_power_decay S hs) hc,?_⟩
  have hblock : 1-Matrix.fromBlocks S 0 0 U = Matrix.fromBlocks (1-S) 0 0 (1-U) := by
    ext (i|i) (j|j) <;> simp [Matrix.one_apply, Matrix.sub_apply, Matrix.fromBlocks]
  rw [hblock,Matrix.det_fromBlocks_zero₂₁,he]
  ring

/-- Two-sided exponential determinant bounds along one fixed iterate already
exclude unit-modulus eigenvalues of the original matrix. -/
theorem matrix_hyperbolic_of_iterated_determinant_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (q : ℕ) (r a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ᶠ m : ℕ in atTop, a*r^m ≤ ‖Matrix.det (1-A^(q*m))‖ ∧
      ‖Matrix.det (1-A^(q*m))‖ ≤ b*r^m) :
    ∀ μ : ℂ, Module.End.HasEigenvalue A.mulVecLin μ → ‖μ‖ ≠ 1 := by
  have hpower := matrix_hyperbolic_of_determinant_bounds (A^q) r a b hr ha hb
    (by simpa only [pow_mul] using h)
  intro μ hμ hn
  have hμpow : Module.End.HasEigenvalue (A^q).mulVecLin (μ^q) := by
    have hmap : (A^q).mulVecLin = A.mulVecLin^q := Matrix.toLin'_pow A q
    rw [hmap]
    exact hμ.pow q
  exact hpower (μ^q) hμpow (by simp [norm_pow,hn])

/-- The determinant positivity lemma on a finite-dimensional real normed carrier.
A basis conjugates its powers to matrix powers, preserving their convergence. -/
theorem linear_det_one_sub_pos_of_power_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hdec : ∀ v, Tendsto (fun m : ℕ ↦ (T^m) v) atTop (𝓝 0)) :
    0 < LinearMap.det (1 - T.toLinearMap) := by
  classical
  let b := Module.finBasis ℝ E
  let A := LinearMap.toMatrix b b T.toLinearMap
  let e := b.equivFun.toContinuousLinearEquiv
  have he (v : E) (m : ℕ) : (A^m).mulVec (e v) = e ((T^m) v) := by
    rw [show A^m = LinearMap.toMatrix b b (T.toLinearMap^m) from LinearMap.toMatrix_pow b _ m]
    change _ = b.equivFun ((T^m) v)
    change (LinearMap.toMatrix b b (T.toLinearMap^m)).mulVec (b.equivFun v) = _
    simp only [Module.Basis.equivFun_apply]
    rw [← ContinuousLinearMap.toLinearMap_pow]
    exact LinearMap.toMatrix_mulVec_repr b b (T^m).toLinearMap v
  have hA : ∀ v, Tendsto (fun m : ℕ ↦ (A^m).mulVec v) atTop (𝓝 0) := by
    intro v
    have h := e.continuous.continuousAt.tendsto.comp (hdec (e.symm v))
    simpa only [Function.comp_def, map_zero, ← he, e.apply_symm_apply] using h
  have h := det_one_sub_pos_of_power_decay A hA
  rwa [show 1-A = LinearMap.toMatrix b b (1-T.toLinearMap) by
    rw [map_sub, LinearMap.toMatrix_one], LinearMap.det_toMatrix] at h

/-- Coordinate-independent stable/unstable determinant factorization, allowing
zero-dimensional factors and requiring decay rather than a one-step norm bound. -/
theorem linear_det_hyperbolic_product_factor
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (S : E →L[ℝ] E) (U : F ≃L[ℝ] F)
    (hs : ∀ v, Tendsto (fun m : ℕ ↦ (S^m) v) atTop (𝓝 0))
    (hu : ∀ v, Tendsto (fun m : ℕ ↦ (U.symm.toContinuousLinearMap^m) v) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧
      LinearMap.det (1 - S.toLinearMap.prodMap U.toLinearMap) =
        (-1:ℝ)^(Module.finrank ℝ F)*LinearMap.det U.toLinearMap*c := by
  classical
  let b := Module.finBasis ℝ F
  let A := LinearMap.toMatrix b b U.toLinearMap
  let B := LinearMap.toMatrix b b U.symm.toLinearMap
  have hAB : A*B=1 := by
    rw [← LinearMap.toMatrix_mul]
    have hi : U.toLinearMap * U.symm.toLinearMap = 1 := by
      ext v
      exact U.apply_symm_apply v
    rw [hi, LinearMap.toMatrix_one]
  let e := b.equivFun.toContinuousLinearEquiv
  have he (v : F) (m : ℕ) : (B^m).mulVec (e v) = e ((U.symm.toContinuousLinearMap^m) v) := by
    rw [show B^m = LinearMap.toMatrix b b (U.symm.toLinearMap^m) from LinearMap.toMatrix_pow b _ m]
    change _ = b.equivFun ((U.symm.toContinuousLinearMap^m) v)
    change (LinearMap.toMatrix b b (U.symm.toLinearMap^m)).mulVec (b.equivFun v) = _
    simp only [Module.Basis.equivFun_apply]
    have hpow : (U.symm.toContinuousLinearMap^m).toLinearMap = U.symm.toLinearMap^m :=
      ContinuousLinearMap.toLinearMap_pow U.symm.toContinuousLinearMap m
    rw [← hpow]
    exact LinearMap.toMatrix_mulVec_repr b b (U.symm.toContinuousLinearMap^m).toLinearMap v
  have hB : ∀ v, Tendsto (fun m : ℕ ↦ (B^m).mulVec v) atTop (𝓝 0) := by
    intro v
    have h := e.continuous.continuousAt.tendsto.comp (hu (e.symm v))
    simpa only [Function.comp_def, map_zero, ← he, e.apply_symm_apply] using h
  obtain ⟨c,hc,hfac⟩ := det_one_sub_expanding_factor A B hAB hB
  have hU : LinearMap.det (1-U.toLinearMap) =
      (-1:ℝ)^(Module.finrank ℝ F)*LinearMap.det U.toLinearMap*c := by
    simpa only [A, ← LinearMap.toMatrix_one b, ← map_sub, LinearMap.det_toMatrix,
      Fintype.card_fin] using hfac
  refine ⟨LinearMap.det (1-S.toLinearMap)*c,
    mul_pos (linear_det_one_sub_pos_of_power_decay S hs) hc, ?_⟩
  have hp : 1-S.toLinearMap.prodMap U.toLinearMap =
      (1-S.toLinearMap).prodMap (1-U.toLinearMap) := by ext v <;> rfl
  rw [hp, LinearMap.det_prodMap, hU]
  ring

/-- The product factorization applies to actual complementary invariant
subspaces, using their sum isomorphism rather than choosing an orthogonal split. -/
theorem linear_det_invariant_splitting_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (S U : Submodule ℝ E) (hSU : IsCompl S U)
    (TS : S →L[ℝ] S) (TU : U ≃L[ℝ] U)
    (hS : ∀ v : S, (TS v : E) = T v) (hU : ∀ v : U, (TU v : E) = T v)
    (hs : ∀ v, Tendsto (fun m : ℕ ↦ (TS^m) v) atTop (𝓝 0))
    (hu : ∀ v, Tendsto (fun m : ℕ ↦ (TU.symm.toContinuousLinearMap^m) v) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ LinearMap.det (1-T.toLinearMap) =
      (-1:ℝ)^(Module.finrank ℝ U)*LinearMap.det TU.toLinearMap*c := by
  let e := S.prodEquivOfIsCompl U hSU
  have he : e.toLinearMap.comp
      ((1-TS.toLinearMap.prodMap TU.toLinearMap).comp e.symm.toLinearMap) =
        1-T.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨s,u⟩,rfl⟩ := e.surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
    change e (((s,u) : S × U) - (TS s,TU u)) = e (s,u) - T (e (s,u))
    rw [map_sub]
    change (s:E)+(u:E)-((TS s:E)+(TU u:E)) = (s:E)+(u:E)-T ((s:E)+(u:E))
    rw [hS,hU,map_add]
  obtain ⟨c,hc,hfac⟩ := linear_det_hyperbolic_product_factor TS TU hs hu
  refine ⟨c,hc,?_⟩
  rw [← he, LinearMap.det_conj]
  exact hfac

end HolomorphicAnosov













