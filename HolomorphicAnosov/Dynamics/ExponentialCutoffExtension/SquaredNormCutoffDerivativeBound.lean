import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Directional derivative bound for a squared-norm cutoff

Source: Merry, *Sixty Lectures on Dynamical Systems*, Lecture 32, proof of
Theorem 32.2, equations (32.6)–(32.7), and HPS, *Invariant Manifolds*, p.62.
-/

namespace HolomorphicAnosov.ExponentialCutoff

/-- A scalar cutoff applied to the squared norm has a global inverse-radius derivative bound.

Source: Merry, Lecture 32, Theorem 32.2, (32.6)–(32.7), and HPS p.62.
Proof: the chain rule gives the scalar derivative times
`(⟪v,w⟫+⟪w,v⟫)/δ²`. Inside the radius, Cauchy–Schwarz bounds the numerator
by `2δ‖w‖`, and the scalar derivative bound gives the result. At or outside the
radius the scalar derivative is zero by hypothesis. Zero vectors and the zero
space are included. For the project's smooth bump, the derivative-zero hypothesis
at the boundary follows from continuity of its derivative.
-/
theorem squared_norm_cutoff_derivative_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, |deriv χ t| ≤ K)
    (hχzero : ∀ t : ℝ, 1 ≤ t → deriv χ t = 0)
    (v w : V) :
    |deriv (fun t : ℝ ↦ χ (‖v + t • w‖ ^ 2 / δ ^ 2)) 0| ≤
      (2 * K / δ) * ‖w‖ := by
  have hline : HasDerivAt (fun t : ℝ ↦ v + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hquad : HasDerivAt (fun t : ℝ ↦ ‖v + t • w‖ ^ 2 / δ ^ 2)
      ((inner ℝ v w + inner ℝ w v) / δ ^ 2) 0 := by
    simpa only [zero_smul, add_zero, real_inner_self_eq_norm_sq] using
      (hline.inner ℝ hline).div_const (δ ^ 2)
  have hformula := ((hχ _).hasDerivAt.comp 0 hquad).deriv
  simp only [Function.comp_def, zero_smul, add_zero] at hformula
  rw [hformula]
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  have hvv : ‖v‖ ^ 2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
  have hcs : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := by
    exact abs_real_inner_le_norm v w
  have hcs' : |inner ℝ w v| ≤ ‖v‖ * ‖w‖ := by
    exact (abs_real_inner_le_norm w v).trans_eq (mul_comm _ _)
  by_cases hinside : ‖v‖ < δ
  · have hnum : |inner ℝ v w + inner ℝ w v| ≤ 2 * δ * ‖w‖ := by
      calc
        _ ≤ |inner ℝ v w| + |inner ℝ w v| := abs_add_le _ _
        _ ≤ 2 * ‖v‖ * ‖w‖ := by linarith
        _ ≤ _ := by nlinarith
    rw [abs_mul, abs_div, abs_of_pos (sq_pos_of_pos hδ)]
    calc
      _ ≤ K * ((2 * δ * ‖w‖) / δ ^ 2) :=
        mul_le_mul (hbound _) (div_le_div_of_nonneg_right hnum (sq_nonneg δ))
          (div_nonneg (abs_nonneg _) (sq_nonneg δ)) hK
      _ = _ := by field_simp
  · have ht : 1 ≤ inner ℝ v v / δ ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
      rw [← hvv]
      nlinarith [le_of_not_gt hinside]
    rw [← real_inner_self_eq_norm_sq v, hχzero _ ht, zero_mul, abs_zero]
    positivity


end HolomorphicAnosov.ExponentialCutoff
