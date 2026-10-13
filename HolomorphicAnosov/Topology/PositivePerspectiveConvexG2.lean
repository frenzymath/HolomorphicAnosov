import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Positivity

open Set
namespace HolomorphicAnosov

/-- Positive perspective is an involution on the upper half-plane. -/
noncomputable def positivePerspectiveG2 (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / p.2, 1 / p.2)

lemma positivePerspectiveG2_involutive {p : ℝ × ℝ} (hp : p.2 ≠ 0) :
    positivePerspectiveG2 (positivePerspectiveG2 p) = p := by
  ext <;> simp [positivePerspectiveG2, hp]

lemma positivePerspectiveG2_continuousOn :
    ContinuousOn positivePerspectiveG2 {p : ℝ × ℝ | 0 < p.2} := by
  exact (continuous_fst.continuousOn.div continuous_snd.continuousOn
    (fun p hp ↦ ne_of_gt hp)).prodMk
      (continuous_const.continuousOn.div continuous_snd.continuousOn (fun p hp ↦ ne_of_gt hp))

/-- Positive perspective preserves convexity.

Source: Boyd and Vandenberghe, Convex Optimization (2004), §2.3.3, pp.39–42.
For points (x,y),(x',y') with positive second coordinates, a convex combination
of their perspective images is the perspective of a convex combination of the
original points. For image weights a,b the original weights are
(a/y)/(a/y+b/y') and (b/y')/(a/y+b/y'). The denominator is positive because
at least one of a,b is positive. These weights are nonnegative, sum to one,
and direct division gives the desired image identity. -/
theorem positivePerspectiveG2_convex_image {K : Set (ℝ × ℝ)}
    (hK : Convex ℝ K) (hpos : ∀ p ∈ K, 0 < p.2) :
    Convex ℝ (positivePerspectiveG2 '' K) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  have hp0 := hpos p hp
  have hq0 := hpos q hq
  let d := a / p.2 + b / q.2
  have hd : 0 < d := by
    rcases eq_or_lt_of_le ha with h | h
    · have ha0 : a = 0 := h.symm
      have hb1 : b = 1 := by linarith
      simp [d, ha0, hb1, hq0]
    · exact add_pos_of_pos_of_nonneg (div_pos h hp0) (div_nonneg hb hq0.le)
  have hsum : a / p.2 / d + b / q.2 / d = 1 := by
    rw [← add_div]
    exact div_self hd.ne'
  refine ⟨(a / p.2 / d) • p + (b / q.2 / d) • q,
    hK hp hq (by positivity) (by positivity) hsum, ?_⟩
  have hy : (a / p.2 / d) * p.2 + (b / q.2 / d) * q.2 = 1 / d := by
    field_simp
    nlinarith [hab]
  apply Prod.ext
  · change ((a / p.2 / d) * p.1 + (b / q.2 / d) * q.1) /
      ((a / p.2 / d) * p.2 + (b / q.2 / d) * q.2) =
      a * (p.1 / p.2) + b * (q.1 / q.2)
    rw [hy]
    field_simp
  · change 1 / ((a / p.2 / d) * p.2 + (b / q.2 / d) * q.2) =
      a * (1 / p.2) + b * (1 / q.2)
    rw [hy]
    simp [d, div_eq_mul_inv]

end HolomorphicAnosov
