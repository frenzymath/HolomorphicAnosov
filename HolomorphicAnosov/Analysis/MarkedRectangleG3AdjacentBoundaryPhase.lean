import HolomorphicAnosov.Analysis.MarkedRectangleG3CanonicalPrevertices
import HolomorphicAnosov.Analysis.SchwarzChristoffelBoundaryBranch
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The two horizontal sides in the canonical Schwarz--Christoffel boundary.
Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp.189--190. -/

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The left finite interval has positive real tangent: exactly three prevertices
lie to its right, so the boundary branch has phase `(-i)^4=1`.
Source: Bak--Newman, pp.189--190, with the fixed prefactor `-i`. -/
theorem canonical_boundary_integrand_left_phase {k u : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hu0 : -1 / k < u) (hu1 : u < -1) :
    ∃ r : ℝ, 0 < r ∧
      -Complex.I * (∏ j : Fin 4,
        Complex.exp (-Complex.log ((u : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) =
          (r : ℂ) := by
  classical
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have hu2 : u < 1 := by linarith
  have hu3 : u < 1 / k := hu2.trans hki
  have hne (j : Fin 4) : u ≠ canonicalPrevertex k j := by
    fin_cases j
    · simpa [canonicalPrevertex] using ne_of_gt hu0
    · simpa [canonicalPrevertex] using ne_of_lt hu1
    · simpa [canonicalPrevertex] using ne_of_lt hu2
    · simpa [canonicalPrevertex] using ne_of_lt hu3
  have hneC (j : Fin 4) : (u : ℂ) ≠ (canonicalPrevertex k j : ℂ) := by
    exact_mod_cast hne j
  have hcard : (Finset.univ.filter (fun j : Fin 4 ↦ u < canonicalPrevertex k j)).card = 3 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_four]
    simp only [one_div] at hu3
    simp [canonicalPrevertex, not_lt.mpr hu0.le, hu1, hu2, hu3]
  have hp := (schwarzChristoffel_boundary_branch (canonicalPrevertex k)).2 u hne
  rw [((schwarzChristoffel_boundary_branch (canonicalPrevertex k)).1
    (u : ℂ) (by simp) hneC).2, hcard] at hp
  let r : ℝ := ∏ j : Fin 4, Real.exp (-Real.log |u - canonicalPrevertex k j| / 2)
  refine ⟨r, Finset.prod_pos (fun _ _ ↦ Real.exp_pos _), ?_⟩
  rw [hp]
  have hcast : (∏ j : Fin 4, (Real.exp (-Real.log |u - canonicalPrevertex k j| / 2) : ℂ)) =
      (r : ℂ) := by simp [r]
  rw [hcast]
  norm_num [pow_succ, mul_assoc, Complex.I_mul_I]

/-- The right finite interval has negative real tangent: exactly one prevertex
lies to its right, so the boundary branch has phase `(-i)^2=-1`.
Source: Bak--Newman, pp.189--190, with the fixed prefactor `-i`. -/
theorem canonical_boundary_integrand_right_phase {k u : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hu0 : 1 < u) (hu1 : u < 1 / k) :
    ∃ r : ℝ, 0 < r ∧
      -Complex.I * (∏ j : Fin 4,
        Complex.exp (-Complex.log ((u : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) =
          -(r : ℂ) := by
  classical
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have h0 : -1 / k < u := by rw [neg_div]; linarith
  have h1 : -1 < u := by linarith
  have hne (j : Fin 4) : u ≠ canonicalPrevertex k j := by
    fin_cases j
    · simpa [canonicalPrevertex] using ne_of_gt h0
    · simpa [canonicalPrevertex] using ne_of_gt h1
    · simpa [canonicalPrevertex] using ne_of_gt hu0
    · simpa [canonicalPrevertex] using ne_of_lt hu1
  have hneC (j : Fin 4) : (u : ℂ) ≠ (canonicalPrevertex k j : ℂ) := by
    exact_mod_cast hne j
  have hcard : (Finset.univ.filter (fun j : Fin 4 ↦ u < canonicalPrevertex k j)).card = 1 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_four]
    simp only [one_div] at hu1
    simp [canonicalPrevertex, not_lt.mpr h0.le, not_lt.mpr h1.le,
      not_lt.mpr hu0.le, hu1]
  have hp := (schwarzChristoffel_boundary_branch (canonicalPrevertex k)).2 u hne
  rw [((schwarzChristoffel_boundary_branch (canonicalPrevertex k)).1
    (u : ℂ) (by simp) hneC).2, hcard] at hp
  let r : ℝ := ∏ j : Fin 4, Real.exp (-Real.log |u - canonicalPrevertex k j| / 2)
  refine ⟨r, Finset.prod_pos (fun _ _ ↦ Real.exp_pos _), ?_⟩
  rw [hp]
  have hcast : (∏ j : Fin 4, (Real.exp (-Real.log |u - canonicalPrevertex k j| / 2) : ℂ)) =
      (r : ℂ) := by simp [r]
  rw [hcast]
  norm_num [pow_succ, mul_assoc, Complex.I_mul_I]

/-- The real boundary integrand is continuous on any interval avoiding all four
prevertices. This is the downward-cut branch from Bak--Newman pp.189--190,
restricted to the real line; the branch theorem identifies it with the
principal-log integrand at every point of this interval. -/
theorem schwarzChristoffel_integrand_continuousOn_interval (x : Fin 4 → ℝ)
    {a b : ℝ} (havoid : ∀ j, x j ∉ Icc a b) :
    ContinuousOn (fun t : ℝ ↦ -Complex.I * ∏ j : Fin 4,
      Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) (Icc a b) := by
  let D : ℂ → ℂ := fun z ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-(Complex.log (-Complex.I * (z - (x j : ℂ))) -
      Complex.log (-Complex.I)) / 2)
  have hD (t : ℝ) (ht : t ∈ Icc a b) :
      DifferentiableAt ℂ D (t : ℂ) ∧ D (t : ℂ) = -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2) := by
    apply (schwarzChristoffel_boundary_branch x).1 (t : ℂ) (by simp)
    intro j he
    exact havoid j ((Complex.ofReal_injective he) ▸ ht)
  have hcD : ContinuousOn (fun t : ℝ ↦ D (t : ℂ)) (Icc a b) := by
    intro t ht
    exact ((hD t ht).1.continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  exact hcD.congr (fun t ht ↦ (hD t ht).2.symm)

/-- A continuous horizontal integrand of fixed strict sign produces a horizontal
primitive increment of that same strict sign. Source: the primitive increment
formula in Bak--Newman p.189. Commute real and imaginary parts with the integral;
the imaginary integral vanishes and the signed real integral is positive. -/
theorem signed_horizontal_increment_strict {a b σ : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (F : ℝ → ℂ) (hc : ContinuousOn f (Icc a b))
    (hphase : ∀ t ∈ Icc a b, (f t).im = 0 ∧ 0 < σ * (f t).re)
    (hinc : F b - F a = ∫ t in a..b, f t) :
    (F b).im = (F a).im ∧ σ * (F a).re < σ * (F b).re := by
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    hc.intervalIntegrable_of_Icc hab.le
  have him : (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  have hre : (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have hzero : (∫ t in a..b, (f t).im) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht ↦
        (hphase t (by simpa only [uIcc_of_le hab.le] using ht)).1)
      _ = 0 := by simp
  have hpos : 0 < ∫ t in a..b, σ * (f t).re :=
    intervalIntegral.integral_pos hab
      (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hc))
      (fun t ht ↦ (hphase t ⟨ht.1.le, ht.2⟩).2.le)
      ⟨a, ⟨le_rfl, hab.le⟩, (hphase a ⟨le_rfl, hab.le⟩).2⟩
  rw [intervalIntegral.integral_const_mul] at hpos
  have hR := congrArg Complex.re hinc
  have hI := congrArg Complex.im hinc
  rw [Complex.sub_re, hre] at hR
  rw [Complex.sub_im, him, hzero] at hI
  refine ⟨sub_eq_zero.mp hI, ?_⟩
  rw [← hR, mul_sub] at hpos
  exact sub_pos.mp hpos

/-- Between the left two prevertices the boundary primitive has strictly
increasing real coordinate and constant imaginary coordinate. Source:
Bak--Newman pp.189--190; integrate the positive real boundary phase on the
compact interval, which avoids all four prevertices. -/
theorem canonical_left_increment_strict {k a b : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hab : a < b) (ha : -1 / k < a) (hb : b < -1)
    (Wbar : ℂ → ℂ)
    (hinc : Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
      -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) :
    (Wbar (b : ℂ)).im = (Wbar (a : ℂ)).im ∧
      (Wbar (a : ℂ)).re < (Wbar (b : ℂ)).re := by
  let f : ℝ → ℂ := fun t ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have havoid (j : Fin 4) : canonicalPrevertex k j ∉ Icc a b := by
    intro hj
    fin_cases j <;> simp only [canonicalPrevertex] at hj <;>
      simp only [one_div, neg_div] at * <;> linarith [hj.1, hj.2]
  have hc : ContinuousOn f (Icc a b) :=
    schwarzChristoffel_integrand_continuousOn_interval (canonicalPrevertex k) havoid
  have hp : ∀ t ∈ Icc a b, (f t).im = 0 ∧ 0 < (1 : ℝ) * (f t).re := by
    intro t ht
    obtain ⟨r, hr, he⟩ := canonical_boundary_integrand_left_phase hk0 hk1
      (ha.trans_le ht.1) (ht.2.trans_lt hb)
    change f t = (r : ℂ) at he
    simp [he, hr]
  simpa only [one_mul] using signed_horizontal_increment_strict hab f
    (fun t : ℝ ↦ Wbar (t : ℂ)) hc hp hinc

/-- Between the right two prevertices the boundary primitive has strictly
decreasing real coordinate and constant imaginary coordinate. Source:
Bak--Newman pp.189--190; integrate the negative real boundary phase on the
compact interval, which avoids all four prevertices. -/
theorem canonical_right_increment_strict {k a b : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hab : a < b) (ha : 1 < a) (hb : b < 1 / k)
    (Wbar : ℂ → ℂ)
    (hinc : Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
      -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) :
    (Wbar (b : ℂ)).im = (Wbar (a : ℂ)).im ∧
      (Wbar (b : ℂ)).re < (Wbar (a : ℂ)).re := by
  let f : ℝ → ℂ := fun t ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have havoid (j : Fin 4) : canonicalPrevertex k j ∉ Icc a b := by
    intro hj
    fin_cases j <;> simp only [canonicalPrevertex] at hj <;>
      simp only [one_div, neg_div] at * <;> linarith [hj.1, hj.2]
  have hc : ContinuousOn f (Icc a b) :=
    schwarzChristoffel_integrand_continuousOn_interval (canonicalPrevertex k) havoid
  have hp : ∀ t ∈ Icc a b, (f t).im = 0 ∧ 0 < (-1 : ℝ) * (f t).re := by
    intro t ht
    obtain ⟨r, hr, he⟩ := canonical_boundary_integrand_right_phase hk0 hk1
      (ha.trans_le ht.1) (ht.2.trans_lt hb)
    change f t = -(r : ℂ) at he
    simp [he, hr]
  simpa only [neg_one_mul, neg_lt_neg_iff] using signed_horizontal_increment_strict hab f
    (fun t : ℝ ↦ Wbar (t : ℂ)) hc hp hinc

end HolomorphicAnosov.Analysis.MarkedRectangle

