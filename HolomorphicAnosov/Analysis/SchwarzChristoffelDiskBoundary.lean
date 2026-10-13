import HolomorphicAnosov.Analysis.MashreghiDiskDerivativeHolderBoundaryG3
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The specified upper-half-plane Schwarz–Christoffel primitive has a continuous
closed-disk extension after the explicit Cayley pullback.

Agent-written adapter for parent `analysis.marked_rectangle_g3_disk_schwarz_christoffel`,
step 4. Source prerequisites: Bak–Newman third edition (2010), Theorem 13.16 pp.183–184
for the Cayley formula; Mashreghi, Generalized Lipschitz Functions (2005), Theorem 4.3,
forward proof pp.442–443 for extension from the derivative-growth estimate. Neither
source is claimed to state the finite-separation estimate or this exact adapter.

Proof: C(z)=i(1+z)/(1-z) sends the open disk into the upper half-plane and has derivative
2i/(1-z)^2. Put eta_j=(x_j-i)/(x_j+i). These are distinct unit points. The derivative
square assumption and the four affine factorizations cancel every power of 1-z,
giving |(W o C)'(z)|^2=A/product_j |z-eta_j|, where A=4/product_j |x_j+i|.
For each mark i put c_i=product_(j!=i)(|eta_i-eta_j|/2)>0 and c=min_i c_i>0.
Choose a mark i closest to z. The triangle inequality gives
|z-eta_j| >= |eta_i-eta_j|/2 for j!=i, while |z-eta_i| >= 1-|z|.
Thus the denominator is at least c*(1-|z|), and taking square roots gives the uniform
bound sqrt(A/c)*(1-|z|)^(-1/2). Apply the proved Mashreghi theorem with alpha=1/2.
The resulting extension agrees with the literal specified W o C throughout the disk.
No boundary injectivity or rectangle image is asserted or assumed. -/
theorem schwarzChristoffel_primitive_continuous_extension
    (x : Fin 4 → ℝ) (hx : Function.Injective x) (W : ℂ → ℂ)
    (hW : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ W w ∧
      (deriv W w)^2 = -(∏ j : Fin 4, (w - (x j : ℂ)))⁻¹) :
    ∃ Fbar : ℂ → ℂ,
      EqOn Fbar (fun z ↦ W (Complex.I * (1 + z) / (1 - z))) {z | ‖z‖ < 1} ∧
      ContinuousOn Fbar {z | ‖z‖ ≤ 1} := by
  /- The derivative of the explicit Cayley map used in the disk boundary estimate.
  The formula follows by the quotient rule. -/
  have hasDerivAt_diskCayley {z : ℂ} (hz : z ≠ 1) :
      HasDerivAt (fun w : ℂ ↦ Complex.I * (1 + w) / (1 - w))
        (2 * Complex.I / (1 - z)^2) z := by
    have h := ((hasDerivAt_const z Complex.I).mul
      ((hasDerivAt_const z 1).add (hasDerivAt_id z))).div
        ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) (sub_ne_zero.mpr hz.symm)
    convert h using 1
    · rfl
    · dsimp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq]
      ring

  /- Imaginary-part identity for the Cayley map, including the totalized value at 1. -/
  have diskCayley_im (z : ℂ) :
      (Complex.I * (1 + z) / (1 - z)).im =
        (1 - ‖z‖^2) / ‖1 - z‖^2 := by
    simp only [Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

  /- The Cayley transform sends every interior disk point to the upper half-plane. -/
  have diskCayley_im_pos {z : ℂ} (hz : ‖z‖ < 1) :
      0 < (Complex.I * (1 + z) / (1 - z)).im := by
    rw [diskCayley_im]
    have hn : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    exact div_pos hn (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz1.symm)))

  /- The real prevertices become circle points under the inverse Cayley map.
  This is the elementary squared-norm computation in the bilinear normalization. -/
  have norm_inverseCayley_real (x : ℝ) :
      ‖((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)‖ = 1 := by
    rw [norm_div]
    have he : ‖(x : ℂ) - Complex.I‖ = ‖(x : ℂ) + Complex.I‖ := by
      rw [← Complex.norm_conj ((x : ℂ) + Complex.I)]
      simp [sub_eq_add_neg]
    rw [he, div_self]
    apply norm_ne_zero_iff.mpr
    intro h
    have := congrArg Complex.im h
    simp at this

  /- Each affine factor has its only zero at the inverse-Cayley circle mark. -/
  have diskCayley_factor (x : ℝ) (z : ℂ) :
      Complex.I * (1 + z) - (x : ℂ) * (1 - z) =
        ((x : ℂ) + Complex.I) *
          (z - ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)) := by
    have hx : (x : ℂ) + Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    field_simp
    ring

  /- Exact cancellation of the fourth-order Cayley denominator against the four
  Schwarz–Christoffel factors. This records the algebra used in the boundary estimate;
  it asserts no boundary extension or injectivity. -/
  have diskCayley_pullback_deriv_sq
      (x : Fin 4 → ℝ) (W : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1)
      (hW : DifferentiableAt ℂ W (Complex.I * (1 + z) / (1 - z)))
      (hsq : (deriv W (Complex.I * (1 + z) / (1 - z)))^2 =
        -(∏ j : Fin 4, (Complex.I * (1 + z) / (1 - z) - (x j : ℂ)))⁻¹) :
      (deriv (fun w : ℂ ↦ W (Complex.I * (1 + w) / (1 - w))) z)^2 =
        4 / ∏ j : Fin 4, (Complex.I * (1 + z) - (x j : ℂ) * (1 - z)) := by
    have hd : deriv (fun w : ℂ ↦ W (Complex.I * (1 + w) / (1 - w))) z =
        deriv W (Complex.I * (1 + z) / (1 - z)) * (2 * Complex.I / (1 - z)^2) := by
      simpa only [Function.comp_def] using
        (hW.hasDerivAt.comp z (hasDerivAt_diskCayley hz)).deriv
    rw [hd, mul_pow, hsq]
    have hfactor (j : Fin 4) :
        Complex.I * (1 + z) / (1 - z) - (x j : ℂ) =
        (Complex.I * (1 + z) - (x j : ℂ) * (1 - z)) / (1 - z) := by
      field_simp
    simp_rw [hfactor]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [inv_div, div_pow, mul_pow]
    norm_num [Complex.I_sq]
    field_simp [sub_ne_zero.mpr hz.symm]

  /- Finite separation gives a linear lower bound for a product of distances to
  pairwise distinct points of the unit circle. The constant is the minimum of the
  products of half the pairwise distances from each marked point. This is an
  agent-written elementary estimate for the existing parent boundary argument. -/
  have exists_circle_distance_product_lower_bound (η : Fin 4 → ℂ)
      (hη : Function.Injective η) (hunit : ∀ j, ‖η j‖ = 1) :
      ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, ‖z‖ < 1 →
        c * (1 - ‖z‖) ≤ ∏ j : Fin 4, ‖z - η j‖ := by
    classical
    let c : Fin 4 → ℝ := fun i ↦ ∏ j ∈ Finset.univ.erase i, ‖η i - η j‖ / 2
    have hc (i : Fin 4) : 0 < c i := by
      apply Finset.prod_pos
      intro j hj
      apply div_pos _ (by norm_num)
      apply norm_pos_iff.mpr
      exact sub_ne_zero.mpr (fun h ↦ (Finset.ne_of_mem_erase hj) (hη h).symm)
    obtain ⟨k, hk⟩ := Finite.exists_min c
    refine ⟨c k, hc k, fun z hz ↦ ?_⟩
    obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin 4 ↦ ‖z - η j‖)
    have hnear : 1 - ‖z‖ ≤ ‖z - η i‖ := by
      have h := norm_sub_norm_le (η i) z
      rw [hunit i, norm_sub_rev] at h
      exact h
    have hother (j : Fin 4) : ‖η i - η j‖ / 2 ≤ ‖z - η j‖ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (η i) z (η j)
      rw [norm_sub_rev (η i) z] at ht
      linarith [hi j]
    have hprod : c i ≤ ∏ j ∈ Finset.univ.erase i, ‖z - η j‖ := by
      apply Finset.prod_le_prod₀
      · intro j hj
        positivity
      · intro j hj
        exact hother j
    calc
      c k * (1 - ‖z‖) ≤ c i * (1 - ‖z‖) :=
        mul_le_mul_of_nonneg_right (hk i) (by linarith)
      _ ≤ (∏ j ∈ Finset.univ.erase i, ‖z - η j‖) * ‖z - η i‖ :=
        mul_le_mul hprod hnear (by linarith) (Finset.prod_nonneg fun j _ ↦ norm_nonneg _)
      _ = ∏ j : Fin 4, ‖z - η j‖ :=
        Finset.prod_erase_mul _ _ (Finset.mem_univ i)

  /- The real inverse-Cayley parametrization of the circle is injective. -/
  have inverseCayley_real_injective : Function.Injective
      (fun x : ℝ ↦ ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)) := by
    have hn (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    intro x y h
    have he := (div_eq_div_iff (hn x) (hn y)).mp h
    have hi := congrArg Complex.im he
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hi
    linarith

  /- The exact squared derivative formula and distinct circle marks imply the
  one-half exponent required by the published Mashreghi extension theorem. -/
  have circle_product_deriv_growth (η : Fin 4 → ℂ)
      (hη : Function.Injective η) (hunit : ∀ j, ‖η j‖ = 1)
      (A : ℝ) (hA : 0 ≤ A) (F : ℂ → ℂ)
      (hformula : ∀ z : ℂ, ‖z‖ < 1 →
        ‖deriv F z‖^2 = A / ∏ j : Fin 4, ‖z - η j‖) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ < 1 →
        ‖deriv F z‖ ≤ C * Real.rpow (1 - ‖z‖) ((1 / 2 : ℝ) - 1) := by
    obtain ⟨c, hc, hbound⟩ := exists_circle_distance_product_lower_bound η hη hunit
    refine ⟨Real.sqrt (A / c), Real.sqrt_nonneg _, fun z hz ↦ ?_⟩
    have hr : 0 < 1 - ‖z‖ := by linarith
    have hden : 0 < c * (1 - ‖z‖) := mul_pos hc hr
    have hs : ‖deriv F z‖^2 ≤ (A / c) / (1 - ‖z‖) := by
      rw [hformula z hz, div_div]
      exact div_le_div_of_nonneg_left hA hden (hbound z hz)
    have hpow : (Real.rpow (1 - ‖z‖) ((1 / 2 : ℝ) - 1))^2 = (1 - ‖z‖)⁻¹ := by
      change ((1 - ‖z‖) ^ ((1 / 2 : ℝ) - 1)) ^ (2 : ℕ) = (1 - ‖z‖)⁻¹
      rw [← Real.rpow_mul_natCast hr.le ((1 / 2 : ℝ) - 1) 2]
      norm_num [Real.rpow_neg_one]
    have hroot : (Real.sqrt (A / c))^2 = A / c := Real.sq_sqrt (div_nonneg hA hc.le)
    have hrhs : 0 ≤ Real.sqrt (A / c) * Real.rpow (1 - ‖z‖) ((1 / 2 : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _)
    have he : (Real.sqrt (A / c) * Real.rpow (1 - ‖z‖) ((1 / 2 : ℝ) - 1))^2 =
        (A / c) / (1 - ‖z‖) := by rw [mul_pow, hroot, hpow]; simp only [div_eq_mul_inv]
    nlinarith

  let F : ℂ → ℂ := fun z ↦ W (Complex.I * (1 + z) / (1 - z))
  let η : Fin 4 → ℂ := fun j ↦ ((x j : ℂ) - Complex.I) / ((x j : ℂ) + Complex.I)
  let A : ℝ := 4 / ∏ j : Fin 4, ‖(x j : ℂ) + Complex.I‖
  have hz1 (z : ℂ) (hz : ‖z‖ < 1) : z ≠ 1 := by
    intro h; simp [h] at hz
  have hF : DifferentiableOn ℂ F {z | ‖z‖ < 1} := by
    intro z hz
    exact (((hW _ (diskCayley_im_pos hz)).1).comp z
      (hasDerivAt_diskCayley (hz1 z hz)).differentiableAt).differentiableWithinAt
  have hnorm (z : ℂ) (hz : ‖z‖ < 1) :
      ‖deriv F z‖^2 = A / ∏ j : Fin 4, ‖z - η j‖ := by
    have he := diskCayley_pullback_deriv_sq x W (hz1 z hz)
      (hW _ (diskCayley_im_pos hz)).1 (hW _ (diskCayley_im_pos hz)).2
    have hn := congrArg norm he
    simp only [norm_pow, norm_div, norm_prod, Complex.norm_ofNat] at hn
    change ‖deriv F z‖^2 = _ at hn
    rw [hn]
    simp_rw [diskCayley_factor, norm_mul]
    rw [Finset.prod_mul_distrib]
    exact (div_div _ _ _).symm
  obtain ⟨C, hC, hderiv⟩ := circle_product_deriv_growth η
    (inverseCayley_real_injective.comp hx) (fun j ↦ norm_inverseCayley_real (x j))
    A (by dsimp [A]; positivity) F hnorm
  obtain ⟨Fbar, heq, hcont, hrest⟩ :=
    HolomorphicAnosov.mashreghi_disk_derivative_holder_boundary_g3
      (1 / 2) C (by norm_num) (by norm_num) hC F hF hderiv
  exact ⟨Fbar, heq, hcont⟩

end HolomorphicAnosov.Analysis.MarkedRectangle
