import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount

namespace HolomorphicAnosov
open Set
open scoped Topology _root_.Topology

/-- The zero-persistence argument in Conway VII.4.3, p.163, as expanded by the
boundary winding proof of Hurwitz's theorem (McMullen, Advanced Complex Analysis,
Lemma 4.2, pp.58–59). A zero at the center contributes positive winding. A strictly
smaller boundary perturbation gives a straight homotopy avoiding zero, so winding
is unchanged. The zero-count theorem forces a zero of the perturbed function. -/
theorem conway_zero_persists_of_boundary_close
    (a : ℂ) (r : ℝ) (hr : 0 < r) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall a r))
    (hfa : f a = 0)
    (hclose : ∀ z ∈ Metric.sphere a r, ‖g z - f z‖ < ‖f z‖) :
    ∃ z ∈ Metric.ball a r, g z = 0 := by
  classical
  have hfne : ∀ z ∈ Metric.sphere a r, f z ≠ 0 := by
    intro z hz he
    have := hclose z hz
    rw [he, norm_zero] at this
    exact (not_lt_of_ge (norm_nonneg _)) this
  have hgne : ∀ z ∈ Metric.sphere a r, g z ≠ 0 := by
    intro z hz he
    have := hclose z hz
    simp [he] at this
  have hzcount := winding_holomorphic_zero_count.2.2.2.2
  obtain ⟨s, hs, hord, hwind, _⟩ := hzcount a 0 r f hr hf hfne
  obtain ⟨t, ht, htord, htwind, hexists⟩ := hzcount a 0 r g hr hg hgne
  apply hexists
  let γf := diskBoundaryLoop a r f hr hf.continuousOn
  let γg := diskBoundaryLoop a r g hr hg.continuousOn
  have hcircle (z : Circle) : a + r * (z : ℂ) ∈ Metric.sphere a r := by
    rw [Metric.mem_sphere]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr]
  have hbf : ∀ z : Circle, γf z ≠ 0 := fun z ↦ hfne _ (hcircle z)
  have hbg : ∀ z : Circle, γg z ≠ 0 := fun z ↦ hgne _ (hcircle z)
  have hhom : LoopHomotopyAvoids γf γg 0 := by
    let H : C(↑unitInterval × Circle, ℂ) :=
      ⟨fun p ↦ γf p.2 + (p.1.val : ℂ) * (γg p.2 - γf p.2), by fun_prop⟩
    refine ⟨H, ?_, ?_, ?_⟩
    · intro z
      simp [H]
    · intro z
      simp [H]
    · intro u z he
      have hid : γf z = -(u.val : ℂ) * (γg z - γf z) := by
        change γf z + (u.val : ℂ) * (γg z - γf z) = 0 at he
        linear_combination he
      have heq := congrArg norm hid
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg u.property.1] at heq
      have hle : ‖γf z‖ ≤ ‖γg z - γf z‖ := by
        rw [heq]
        exact mul_le_of_le_one_left (norm_nonneg _) u.property.2
      exact (not_lt_of_ge hle) (hclose _ (hcircle z))
  have hsame := loopWinding_homotopy γf γg 0 hbf hbg hhom
  change loopWinding γg 0 hbg ≠ 0
  rw [← hsame]
  have ha : a ∈ s := (hs a).mpr ⟨Metric.mem_ball_self hr, hfa⟩
  have hsumpos : 0 < s.sum (fun z ↦ (analyticOrderNatAt (fun z ↦ f z - 0) z : ℤ)) := by
    apply Finset.sum_pos
    · intro z hz
      exact Int.natCast_pos.mpr (hord z hz).2
    · exact ⟨a, ha⟩
  exact ne_of_gt (hwind.symm ▸ hsumpos)

end HolomorphicAnosov
