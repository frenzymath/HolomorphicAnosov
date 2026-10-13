import HolomorphicAnosov.Analysis.MarkedRectangleG3CanonicalPrevertices
import HolomorphicAnosov.Analysis.SchwarzChristoffelBoundaryBranch
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-! Central-side phase in the canonical Schwarz–Christoffel normalization.
Bak–Newman, *Complex Analysis*, third edition (2010), pp.189–190:
the number of negative real factors determines the tangent direction. -/

noncomputable section
open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle
/-- For canonical prevertices with `0 < k < 1`, the boundary integrand on
`(-1,1)` points strictly upward. Source: Bak–Newman, pp.189–190.

There are exactly two prevertices to the right of `u`. The real-boundary
branch formula therefore has phase `(-i)^3 = i`; its amplitude is a product
of four positive real exponentials. This calculation applies to every allowed
parameter and makes no assertion about endpoint differentiability. -/
theorem canonical_boundary_integrand_central_phase {k u : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hu0 : -1 < u) (hu1 : u < 1) :
    ∃ r : ℝ, 0 < r ∧
      -Complex.I * (∏ j : Fin 4,
        Complex.exp (-Complex.log ((u : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) =
          (r : ℂ) * Complex.I := by
  classical
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have h0 : -1 / k < u := by rw [neg_div]; linarith
  have h3 : u < 1 / k := hu1.trans hki
  have hne (j : Fin 4) : u ≠ canonicalPrevertex k j := by
    fin_cases j
    · simpa [canonicalPrevertex] using ne_of_gt h0
    · simpa [canonicalPrevertex] using ne_of_gt hu0
    · simpa [canonicalPrevertex] using ne_of_lt hu1
    · simpa [canonicalPrevertex] using ne_of_lt h3
  have hneC (j : Fin 4) : (u : ℂ) ≠ (canonicalPrevertex k j : ℂ) := by
    exact_mod_cast hne j
  have hcard : (Finset.univ.filter (fun j : Fin 4 ↦ u < canonicalPrevertex k j)).card = 2 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_four]
    simp only [one_div] at h3
    simp [canonicalPrevertex, not_lt.mpr h0.le, not_lt.mpr hu0.le, hu1, h3]
  have hp := (schwarzChristoffel_boundary_branch (canonicalPrevertex k)).2 u hne
  rw [((schwarzChristoffel_boundary_branch (canonicalPrevertex k)).1
    (u : ℂ) (by simp) hneC).2, hcard] at hp
  let r : ℝ := ∏ j : Fin 4, Real.exp (-Real.log |u - canonicalPrevertex k j| / 2)
  have hr : 0 < r := Finset.prod_pos (fun _ _ ↦ Real.exp_pos _)
  refine ⟨r, hr, ?_⟩
  rw [hp]
  have hcast : (∏ j : Fin 4, (Real.exp (-Real.log |u - canonicalPrevertex k j| / 2) : ℂ)) =
      (r : ℂ) := by simp [r]
  rw [hcast]
  norm_num [pow_succ, mul_assoc, Complex.I_mul_I]
  ring
/-- A primitive increment on a compact central subinterval is strictly upward.
Source: Bak–Newman, pp.189–190. The boundary branch is continuous away from
prevertices. Its real part vanishes and its imaginary part is everywhere positive
on the interval by the central phase formula. Commuting real and imaginary
parts with the interval integral gives the claim, using strict positivity of
the integral of a continuous positive function on a nondegenerate interval. -/
theorem canonical_central_increment_strict {k a b : ℝ}
    (hk0 : 0 < k) (hk1 : k < 1) (hab : a < b) (ha : -1 < a) (hb : b < 1)
    (Wbar : ℂ → ℂ)
    (hinc : Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b,
      -Complex.I * ∏ j : Fin 4,
        Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)) :
    (Wbar (b : ℂ)).re = (Wbar (a : ℂ)).re ∧
      (Wbar (a : ℂ)).im < (Wbar (b : ℂ)).im := by
  let f : ℝ → ℂ := fun t ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-Complex.log ((t : ℂ) - (canonicalPrevertex k j : ℂ)) / 2)
  have hki : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have hbounds (t : ℝ) (ht : t ∈ Icc a b) : -1 < t ∧ t < 1 :=
    ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hne (t : ℝ) (ht : t ∈ Icc a b) (j : Fin 4) :
      (t : ℂ) ≠ (canonicalPrevertex k j : ℂ) := by
    intro he
    have heR : t = canonicalPrevertex k j := Complex.ofReal_injective he
    have ht' := hbounds t ht
    fin_cases j <;> norm_num [canonicalPrevertex] at heR <;>
      simp only [one_div, neg_div] at * <;> linarith
  let D : ℂ → ℂ := fun z ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-(Complex.log (-Complex.I * (z - (canonicalPrevertex k j : ℂ))) -
      Complex.log (-Complex.I)) / 2)
  have hD (t : ℝ) (ht : t ∈ Icc a b) :
      DifferentiableAt ℂ D (t : ℂ) ∧ D (t : ℂ) = f t :=
    (schwarzChristoffel_boundary_branch (canonicalPrevertex k)).1
      (t : ℂ) (by simp) (hne t ht)
  have hcD : ContinuousOn (fun t : ℝ ↦ D (t : ℂ)) (Icc a b) := by
    intro t ht
    exact ((hD t ht).1.continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hc : ContinuousOn f (Icc a b) := hcD.congr (fun t ht ↦ (hD t ht).2.symm)
  have hphase (t : ℝ) (ht : t ∈ Icc a b) : (f t).re = 0 ∧ 0 < (f t).im := by
    obtain ⟨r, hr, he⟩ := canonical_boundary_integrand_central_phase hk0 hk1
      (hbounds t ht).1 (hbounds t ht).2
    change f t = (r : ℂ) * Complex.I at he
    simp [he, hr]
  have hint : IntervalIntegrable f MeasureTheory.volume a b :=
    hc.intervalIntegrable_of_Icc hab.le
  have him : (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  have hre : (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have hzero : (∫ t in a..b, (f t).re) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht ↦
        (hphase t (by simpa only [uIcc_of_le hab.le] using ht)).1)
      _ = 0 := by simp
  have hpos : 0 < ∫ t in a..b, (f t).im :=
    intervalIntegral.integral_pos hab (Complex.continuous_im.comp_continuousOn hc)
      (fun t ht ↦ (hphase t ⟨ht.1.le, ht.2⟩).2.le)
      ⟨a, ⟨le_rfl, hab.le⟩, (hphase a ⟨le_rfl, hab.le⟩).2⟩
  change Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b, f t at hinc
  have hR := congrArg Complex.re hinc
  have hI := congrArg Complex.im hinc
  rw [Complex.sub_re, hre, hzero] at hR
  rw [Complex.sub_im, him] at hI
  exact ⟨sub_eq_zero.mp hR, sub_pos.mp (hI.symm ▸ hpos)⟩

end HolomorphicAnosov.Analysis.MarkedRectangle

