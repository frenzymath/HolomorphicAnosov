import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Set

namespace HolomorphicAnosov

/-- The vertex of a nondegenerate right angle does not lie on its opposite
base segment. Source: agent-written coordinate expansion of Cairns (1951),
§3, the perpendicular first-contact construction and Case II, pp.862–863.
If the vertex were a convex combination of the other endpoints, taking the
dot product with the first leg would force its coefficient to vanish. The
other coefficient would then be one, identifying its endpoint with the
vertex, a contradiction. -/
theorem halfSector_perpendicular_base_notMem
    (M D P : ℂ) (hDM : D ≠ M) (hPM : P ≠ M)
    (hperp : (P-M).re * (D-M).re + (P-M).im * (D-M).im = 0) :
    M ∉ segment ℝ D P := by
  rintro ⟨a, b, ha, hb, hab, heq⟩
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at him
  have hre' : a * (D-M).re + b * (P-M).re = 0 := by
    simp only [Complex.sub_re]
    linear_combination hre - M.re * hab
  have him' : a * (D-M).im + b * (P-M).im = 0 := by
    simp only [Complex.sub_im]
    linear_combination him - M.im * hab
  have hnorm : 0 < (D-M).re^2 + (D-M).im^2 := by
    have hn : (D-M).re ≠ 0 ∨ (D-M).im ≠ 0 := by
      by_contra h
      push Not at h
      apply hDM
      exact sub_eq_zero.mp (Complex.ext h.1 h.2)
    rcases hn with hn | hn <;> nlinarith [sq_pos_of_ne_zero hn]
  have ha0 : a * ((D-M).re^2 + (D-M).im^2) = 0 := by
    linear_combination (D-M).re * hre' + (D-M).im * him' - b * hperp
  have haeq : a = 0 := (mul_eq_zero.mp ha0).resolve_right (ne_of_gt hnorm)
  have hbeq : b = 1 := by linarith
  exact hPM (by simpa [haeq, hbeq] using heq)

end HolomorphicAnosov

