import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory
namespace HolomorphicAnosov

/-- Affine change of variables from the Euclidean unit ball to a positive-radius ball.
Source: Campanato (1964), Lemma [2.I], equation (2.12), printed p.143.
Proof: Haar measure scales by the inverse N-th power under scalar multiplication;
translation preserves Haar measure. The two maps carry the indicated balls onto one another.
The Bochner-integral identity also holds for nonintegrable functions, whose integrals are zero. -/
theorem euclidean_ball_affine_integral {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) (r : ℝ) (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) :
    (∫ x in Metric.ball 0 1, f (a + r • x)) =
      (r ^ N)⁻¹ * ∫ x in Metric.ball a r, f x := by
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun x ↦ f (a + x)) _ hr]
  rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hp : (fun x ↦ a + x) ⁻¹' Metric.ball a r = Metric.ball 0 r := by
    ext x
    simp [Metric.mem_ball, dist_eq_norm]
  have ht := (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (Homeomorph.addLeft a).measurableEmbedding f (Metric.ball a r)
  rw [hp] at ht
  rw [ht]
  simp

end HolomorphicAnosov
