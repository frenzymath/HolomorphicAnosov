import HolomorphicAnosov.Analysis.Complex.OmittedValuesCenterDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# An absolute spherical-derivative estimate for two omitted values

Source: Lyubich, Conformal Geometry and Dynamics of Quadratic Polynomials,
§4.3 Exercise 4.6 and Theorem 4.8, p.112; Conway, Functions of One Complex
Variable II, Chapter XVI §4 Theorem 4.2, pp.124–125.
Ahlfors, *Complex Analysis*, Chapter 5 §5.5 Theorem 17, pp.226–227, supplies
the necessary spherical-derivative criterion. The proof uses independent Conway
sequential normality, a Cauchy
center estimate, and affine rescaling to an inscribed disk.
-/

namespace HolomorphicAnosov

open Metric Set

/-- An absolute spherical-derivative bound for a holomorphic function omitting zero and one.

The spherical length element is `|dw| / (1 + |w|²)`, without a factor of two.
The constant precedes the disk and function, so it is independent of the center,
radius, values and evaluation point. Values outside the open disk are unrestricted.
No Euclidean image bound, injectivity or boundary regularity is assumed.

Source and proof: Lyubich §4.3 Exercise 4.6 and Theorem 4.8, p.112, with the
sequential normality theorem of Conway II, Chapter XVI §4 Theorem 4.2, pp.124–125.
Ahlfors Chapter 5 §5.5 Theorem 17, pp.226–227, gives the finite-chart/reciprocal
necessity argument for the center bound. After choosing that bound, the direct
application to an inscribed disk and the final real inequality below are elementary
steps of this proof. Ahlfors Chapter 4 §3.4 pp.135–136 describes affine disk
normalization; it does not state the particular factor-two estimate used here.
If spherical center derivatives on the unit disk were unbounded, choose functions
with derivatives exceeding n. Conway gives a subsequence with finite compact-uniform
holomorphic limit or uniform divergence to infinity. Cauchy's estimate on the half
disk bounds derivatives in the finite case; applied to reciprocals, it also bounds
spherical derivatives in the infinite case. Thus one positive center bound C exists.
For z in B(a,R), precompose h with w↦z+(R−dist(z,a))w. The chain rule gives a
spherical derivative bound C/(R−dist(z,a)), at most 2CR/(R²−dist(z,a)²). The absolute
constant 2C proves the statement. Every denominator is positive inside the disk.
DAG node: `analysis.lyubich_omitted_values_spherical_derivative_bound`.
-/
theorem omittedValues_sphericalDerivative_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℂ) (R : ℝ) (h : ℂ → ℂ),
        0 < R →
        DifferentiableOn ℂ h (Metric.ball a R) →
        (∀ z ∈ Metric.ball a R, h z ≠ 0 ∧ h z ≠ 1) →
        ∀ z ∈ Metric.ball a R,
          ‖deriv h z‖ / (1 + ‖h z‖ ^ 2) ≤ C * R / (R ^ 2 - dist z a ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := omittedValues_center_sphericalDerivative_bound
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro a R h hR hh ho z hz
  let r := R - dist z a
  have hr : 0 < r := sub_pos.mpr hz
  let A : ℂ → ℂ := fun w ↦ z + (r : ℂ) * w
  have hA : MapsTo A (ball 0 1) (ball a R) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    have ha : dist (A w) z = r * ‖w‖ := by
      simp [A, dist_eq_norm, Complex.norm_real, abs_of_pos hr]
    change dist (A w) a < R
    calc
      dist (A w) a ≤ dist (A w) z + dist z a := dist_triangle _ _ _
      _ < r + dist z a := by rw [ha]; nlinarith
      _ = R := by dsimp [r]; ring
  have hAd : Differentiable ℂ A := by
    fun_prop
  have hc := hbound (h ∘ A) (hh.comp hAd.differentiableOn hA)
    (fun w hw ↦ ho _ (hA hw))
  have hAz : A 0 = z := by simp [A]
  have hder : deriv (h ∘ A) 0 = deriv h z * (r : ℂ) := by
    have hda : HasDerivAt A (r : ℂ) 0 := by
      simpa [A] using (((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z)
    have hdh : HasDerivAt h (deriv h z) (A 0) := by
      rw [hAz]
      exact (hh.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    exact (hdh.comp 0 hda).deriv
  rw [Function.comp_apply, hAz, hder, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr] at hc
  have hden : 0 < 1 + ‖h z‖ ^ 2 := by positivity
  have hc' : ‖deriv h z‖ / (1 + ‖h z‖ ^ 2) ≤ C / r := by
    apply (le_div_iff₀ hr).mpr
    simpa only [div_mul_eq_mul_div] using hc
  have hd : 0 ≤ dist z a := dist_nonneg
  have hdR : dist z a < R := hz
  have hquad : 0 < R ^ 2 - dist z a ^ 2 := by nlinarith
  refine hc'.trans ((div_le_div_iff₀ hr hquad).mpr ?_)
  dsimp [r]
  nlinarith [mul_nonneg hC.le (sq_nonneg (R - dist z a))]



end HolomorphicAnosov
