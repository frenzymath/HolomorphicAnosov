import HolomorphicAnosov.Analysis.ComplexDownwardLog
import HolomorphicAnosov.Analysis.ComplexInverseSqrtRealBoundary
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The downward-ray branch of the Schwarz–Christoffel integrand is holomorphic
at every nonvertex point of the closed upper half-plane. It agrees there with the
principal-log formula, and on the real axis each prevertex strictly to the right
contributes a factor -i to its phase, with a strictly positive real amplitude.

Source: Bak–Newman, Complex Analysis, third edition (2010), pp.188–190,
particularly the written inverse-square-root branch argument and the four downward
slits on pp.189–190. Our fixed prefactor -i rotates every source direction by -pi/2.

Proof: for Im(v) >= 0 and v != 0, arg(v) is in [0,pi]. Therefore
arg(-i)+arg(v) is in [-pi/2,pi/2], and the logarithm product identity gives
log(-iv)-log(-i)=log(v). The rotated argument avoids the principal cut, so its
logarithm and exponential are holomorphic at every such v. Take the four-factor
product. For positive real r the factor is exp(-log(r)/2); for negative real r,
log(r)=log(-r)+pi*i, so the factor is -i*exp(-log(-r)/2). Multiplying these four
literal factors gives the count formula. Distinctness is unnecessary for this
integrand statement; nonvertex assumptions exclude every zero factor explicitly. -/
theorem schwarzChristoffel_boundary_branch (x : Fin 4 → ℝ) :
    let G : ℂ → ℂ := fun z ↦ -Complex.I * ∏ j : Fin 4,
      Complex.exp (-(Complex.log (-Complex.I * (z - (x j : ℂ))) -
        Complex.log (-Complex.I)) / 2)
    (∀ z : ℂ, 0 ≤ z.im → (∀ j, z ≠ (x j : ℂ)) →
      DifferentiableAt ℂ G z ∧
      G z = -Complex.I * ∏ j : Fin 4, Complex.exp (-Complex.log (z - (x j : ℂ)) / 2)) ∧
    (∀ u : ℝ, (∀ j, u ≠ x j) →
      G (u : ℂ) =
        (-Complex.I)^((Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card + 1) *
          (∏ j : Fin 4, (Real.exp (-Real.log |u - x j| / 2) : ℂ))) := by
  /- On the closed upper half-plane, moving the logarithm cut to the downward ray
  preserves the principal value. This is the branch used in Bak–Newman pp.189–190. -/
  have downward_log_eq {v : ℂ} (hv : v ≠ 0) (him : 0 ≤ v.im) :
      Complex.log (-Complex.I * v) - Complex.log (-Complex.I) = Complex.log v := by
    have harg : (-Complex.I).arg + v.arg ∈ Ioc (-Real.pi) Real.pi := by
      rw [Complex.arg_neg_I]
      have ha := Complex.arg_nonneg_iff.mpr him
      have hb := Complex.arg_le_pi v
      constructor <;> linarith [Real.pi_pos]
    rw [Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) hv harg]
    ring

  /- The rotated argument lies off the logarithm cut at every nonzero point of the
  closed upper half-plane. -/
  have downward_mem_slitPlane {v : ℂ} (hv : v ≠ 0) (him : 0 ≤ v.im) :
      -Complex.I * v ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, zero_sub, neg_mul, one_mul,
      neg_neg, zero_add]
    by_cases h : v.im = 0
    · right
      have hreal : v.re ≠ 0 := by
        intro hr
        exact hv (Complex.ext hr h)
      exact neg_ne_zero.mpr hreal
    · left
      exact lt_of_le_of_ne him (Ne.symm h)

  /- The positive real value of the inverse square-root branch specified on
  Bak–Newman p.189. -/
  have inverse_sqrt_branch_of_pos {r : ℝ} (hr : 0 < r) :
      Complex.exp (-Complex.log (r : ℂ) / 2) =
        (Real.exp (-Real.log r / 2) : ℂ) := by
    rw [← Complex.ofReal_log hr.le]
    norm_cast

  /- On the negative real axis the same branch has phase -i, as in the
  semicircular branch calculation on Bak–Newman pp.188–189. -/
  have inverse_sqrt_branch_of_neg {r : ℝ} (hr : r < 0) :
      Complex.exp (-Complex.log (r : ℂ) / 2) =
        -Complex.I * (Real.exp (-Real.log (-r) / 2) : ℂ) := by
    have hlog : Complex.log (r : ℂ) = (Real.log (-r) : ℂ) + Real.pi * Complex.I := by
      have h := Complex.log_ofReal_mul (neg_pos.mpr hr) (show (-1 : ℂ) ≠ 0 by norm_num)
      simpa [Complex.log_neg_one] using h
    rw [hlog]
    have he : -((Real.log (-r) : ℂ) + Real.pi * Complex.I) / 2 =
        ((-Real.log (-r) / 2 : ℝ) : ℂ) + (-(Real.pi : ℂ) / 2) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
    rw [← Complex.ofReal_exp]
    ring

  /- The source's real boundary factor formula, with positive amplitude expressed
  as an exponential of the real logarithm. -/
  have inverse_sqrt_branch_real {r : ℝ} (hr : r ≠ 0) :
      Complex.exp (-Complex.log (r : ℂ) / 2) =
        (if r < 0 then -Complex.I else 1) *
          (Real.exp (-Real.log |r| / 2) : ℂ) := by
    by_cases h : r < 0
    · rw [ite_eq_left h, abs_of_neg h, inverse_sqrt_branch_of_neg h]
    · have hp : 0 < r := lt_of_le_of_ne (le_of_not_gt h) hr.symm
      rw [ite_eq_right h, abs_of_pos hp, inverse_sqrt_branch_of_pos hp, one_mul]

  /- Bak–Newman pp.189–190: crossing each of the four ordered real prevertices
  increases the integrand's phase by pi/2. The exact formula counts prevertices
  strictly to the right, so no arbitrary ordering or relabeling is hidden. -/
  have schwarzChristoffel_real_boundary_phase (x : Fin 4 → ℝ) (u : ℝ)
      (hu : ∀ j, u ≠ x j) :
      -Complex.I * (∏ j : Fin 4, Complex.exp (-Complex.log ((u : ℂ) - (x j : ℂ)) / 2)) =
        (-Complex.I)^((Finset.univ.filter (fun j : Fin 4 ↦ u < x j)).card + 1) *
          (∏ j : Fin 4, (Real.exp (-Real.log |u - x j| / 2) : ℂ)) := by
    classical
    have hf (j : Fin 4) : Complex.exp (-Complex.log ((u : ℂ) - (x j : ℂ)) / 2) =
        (if u < x j then -Complex.I else 1) *
          (Real.exp (-Real.log |u - x j| / 2) : ℂ) := by
      simpa only [Complex.ofReal_sub, sub_neg] using
        (inverse_sqrt_branch_real (sub_ne_zero.mpr (hu j)))
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite, Finset.prod_const]
    rw [pow_succ]
    ring

  /- Bak–Newman pp.189–190: the product of inverse square-root branches is holomorphic
  across every nonvertex point of the real axis, by using downward-ray cuts. The
  extension agrees with the literal principal-log integrand throughout the upper
  half-plane and at the nonsingular real points. -/
  have schwarzChristoffel_boundary_integrand
      (x : Fin 4 → ℝ) :
      let G : ℂ → ℂ := fun z ↦ -Complex.I * ∏ j : Fin 4,
        Complex.exp (-(Complex.log (-Complex.I * (z - (x j : ℂ))) -
          Complex.log (-Complex.I)) / 2)
      (∀ z : ℂ, 0 ≤ z.im → (∀ j, z ≠ (x j : ℂ)) → DifferentiableAt ℂ G z) ∧
      (∀ z : ℂ, 0 ≤ z.im → (∀ j, z ≠ (x j : ℂ)) →
        G z = -Complex.I * ∏ j : Fin 4, Complex.exp (-Complex.log (z - (x j : ℂ)) / 2)) := by
    dsimp only
    constructor
    · intro z hz hne
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.fun_finsetProd
      intro j hj
      have hslit : -Complex.I * (z - (x j : ℂ)) ∈ Complex.slitPlane := by
        apply downward_mem_slitPlane (sub_ne_zero.mpr (hne j))
        simpa using hz
      exact ((((differentiableAt_const (-Complex.I)).mul
        (differentiableAt_id.sub_const (x j : ℂ))).clog hslit).sub_const
          (Complex.log (-Complex.I))).neg.div_const 2 |>.cexp
    · intro z hz hne
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [downward_log_eq (sub_ne_zero.mpr (hne j)) (by simpa using hz)]
  dsimp only
  refine ⟨?_, ?_⟩
  · intro z hz hne
    exact ⟨(schwarzChristoffel_boundary_integrand x).1 z hz hne,
      (schwarzChristoffel_boundary_integrand x).2 z hz hne⟩
  · intro u hu
    have hne (j : Fin 4) : (u : ℂ) ≠ (x j : ℂ) := by exact_mod_cast hu j
    exact ((schwarzChristoffel_boundary_integrand x).2 (u : ℂ) (by simp) hne).trans
      (schwarzChristoffel_real_boundary_phase x u hu)

end HolomorphicAnosov.Analysis.MarkedRectangle
