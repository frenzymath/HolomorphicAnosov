import Mathlib.Analysis.Complex.Schwarz

open Set Metric

namespace HolomorphicAnosov

/-- The analytic contradiction in Lyubich Lemma 4.13 (printed p.113).
The derivative chain rule forces the inverse derivative to have modulus one. Schwarz on the
larger disk bounds that modulus by its reciprocal radius, which is strictly less than one.
This result assumes the inverse; it does not supply the planar image-filling argument. -/
theorem normalized_inverse_larger_disk_contradiction
    (f g : ℂ → ℂ) (R : ℝ) (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hf0 : f 0 = 0) (hderiv : ‖deriv f 0‖ = 1)
    (hleft : EqOn (g ∘ f) id (ball 0 1))
    (hmap : MapsTo g (ball 0 R) (ball 0 1)) : False := by
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hg0 : g 0 = 0 := by
    simpa only [Function.comp_apply, hf0, id_eq] using hleft (mem_ball_self zero_lt_one)
  have hcomp : deriv (g ∘ f) 0 = 1 := by
    simpa using hleft.deriv isOpen_ball (mem_ball_self zero_lt_one)
  have hgd : DifferentiableAt ℂ g (f 0) := by
    rw [hf0]
    exact hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0))
  have hprod : deriv g 0 * deriv f 0 = 1 := by
    rw [deriv_comp 0 hgd
      (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)))] at hcomp
    simpa only [hf0] using hcomp
  have hgnorm : ‖deriv g 0‖ = 1 := by
    have h := congrArg norm hprod
    simpa only [norm_mul, hderiv, mul_one, norm_one] using h
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball hg
    (show MapsTo g (ball 0 R) (closedBall (g 0) 1) from by
      rw [hg0]
      exact hmap.mono_right ball_subset_closedBall) hR0
  rw [hgnorm] at hbound
  have hlt : 1 / R < 1 := (div_lt_one hR0).mpr hR
  exact (not_lt_of_ge hbound) hlt

end HolomorphicAnosov
