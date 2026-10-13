import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set

/-- A continuous angular lift of an injective circle map with positive unit
increment is strictly increasing on the closed parameter interval.
Source: Lyubich §1.11 pp.53–54 and the circle-homeomorphism discussion in
§19.8.4. Equal lift values force equal circle parameters. Distinct parameters
in [0,1] with the same circle point must be the two endpoints, but the positive
increment excludes equality there. A continuous injective real interval map
is monotone in one direction; the endpoint increment chooses increasing. -/
theorem circle_lift_strictMono
    (e : Circle → Circle) (he : Function.Injective e)
    (θ : C(Icc (0 : ℝ) 1, ℝ))
    (hθ : ∀ t, Circle.exp (θ t) = e (Circle.exp (2 * Real.pi * (t : ℝ))))
    (hinc : θ ⟨1, by simp⟩ - θ ⟨0, by simp⟩ = 2 * Real.pi) :
    StrictMono θ := by
  apply θ.continuous.strictMono_of_inj_boundedOrder
  · change θ ⟨0, by simp⟩ ≤ θ ⟨1, by simp⟩
    linarith [Real.pi_pos]
  intro s t hst
  have hphase : Circle.exp (2 * Real.pi * (s : ℝ)) = Circle.exp (2 * Real.pi * (t : ℝ)) := by
    apply he
    rw [← hθ s, ← hθ t, hst]
  by_contra hne
  wlog hlt : s < t generalizing s t
  · apply this hst.symm hphase.symm (Ne.symm hne)
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
  have hltval : (s : ℝ) < t := hlt
  have hdiff : (t : ℝ) - s < 1 := by
    by_contra hh
    have hs : s = ⟨0, by simp⟩ := by
      apply Subtype.ext
      have hs0 := s.property.1
      have ht1 := t.property.2
      dsimp at *
      linarith
    have ht : t = ⟨1, by simp⟩ := by
      apply Subtype.ext
      have hs0 := s.property.1
      have ht1 := t.property.2
      dsimp at *
      linarith
    rw [hs, ht] at hst
    linarith [Real.pi_pos]
  have hsinj := Circle.exp_injOn_Icc
    (a := 2 * Real.pi * (s : ℝ)) (b := 2 * Real.pi * (t : ℝ))
    (by nlinarith [Real.pi_pos])
  have heq := hsinj (by constructor <;> nlinarith [Real.pi_pos, hltval])
    (by constructor <;> nlinarith [Real.pi_pos, hltval]) hphase
  have hv : (s : ℝ) = t := (mul_left_cancel₀ (by positivity) heq)
  exact hne (Subtype.ext hv)

/-- Normalizing a nonzero complex exponential retains precisely its angle. -/
theorem exp_im_eq_normalized (z : ℂ) :
    Complex.exp ((z.im : ℂ) * Complex.I) =
      Complex.exp z / (‖Complex.exp z‖ : ℂ) := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    exact (Complex.re_add_im z).symm
  nth_rw 2 [hz]
  rw [Complex.exp_add, Complex.norm_exp, Complex.ofReal_exp]
  exact (mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)).symm

/-- The imaginary part of a logarithm lift with positive full-turn increment
strictly increases whenever the normalized loop is injective on the circle.
Source: Lyubich §1.11 pp.53–54, circle lift monotonicity. The preceding
normalization identity converts the logarithm lift to an angular lift, and
the imaginary part of its increment is exactly two pi. -/
theorem normalized_loop_log_strictMono
    (γ : Circle → ℂ) (a : ℂ)
    (havoid : ∀ z, γ z ≠ a)
    (hinj : Function.Injective (fun z ↦ (γ z - a) / (‖γ z - a‖ : ℂ)))
    (L : C(Icc (0 : ℝ) 1, ℂ))
    (hL : ∀ t, Complex.exp (L t) = γ (Circle.exp (2 * Real.pi * (t : ℝ))) - a)
    (hinc : L ⟨1, by simp⟩ - L ⟨0, by simp⟩ = (2 * Real.pi : ℂ) * Complex.I) :
    StrictMono (fun t ↦ (L t).im) := by
  let e : Circle → Circle := fun z ↦
    ⟨(γ z - a) / (‖γ z - a‖ : ℂ), by
      change (γ z - a) / (‖γ z - a‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right]
      simp [Complex.norm_real,
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr (havoid z))]⟩
  apply circle_lift_strictMono e
    (fun x y h ↦ hinj (congrArg (fun z : Circle ↦ (z : ℂ)) h))
    ⟨fun t ↦ (L t).im, Complex.continuous_im.comp L.continuous⟩
  · intro t
    apply Subtype.ext
    change Complex.exp ((L t).im * Complex.I) =
      (γ (Circle.exp (2 * Real.pi * (t : ℝ))) - a) /
        (‖γ (Circle.exp (2 * Real.pi * (t : ℝ))) - a‖ : ℂ)
    rw [exp_im_eq_normalized, hL]
  · have hi := congrArg Complex.im hinc
    simpa using hi

/-- Every point distinct from the cut has a unique parameter in the open turn.
The argument in (-pi,pi] is shifted by one full turn when it is nonpositive. -/
theorem circle_exists_open_turn (u q : Circle) (h : q ≠ u) :
    ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ u * Circle.exp (2 * Real.pi * t) = q := by
  let w := u⁻¹ * q
  have hw : w ≠ 1 := by
    intro he
    have := congrArg (fun z : Circle ↦ u*z) he
    simp [w] at this
    exact h this
  have ha : Complex.arg w ≠ 0 := by simpa using hw
  obtain ⟨r, hr, he⟩ : ∃ r : ℝ, r ∈ Ioo (0 : ℝ) (2 * Real.pi) ∧ Circle.exp r = w := by
    rcases lt_or_gt_of_ne ha with hn | hp
    · refine ⟨Complex.arg w + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
      · linarith [Complex.neg_pi_lt_arg (w : ℂ), Real.pi_pos]
      · linarith
      · simp
    · refine ⟨Complex.arg w, ⟨hp, ?_⟩, Circle.exp_arg w⟩
      linarith [Complex.arg_le_pi (w : ℂ), Real.pi_pos]
  refine ⟨r / (2 * Real.pi),
    ⟨div_pos hr.1 (by positivity), (div_lt_one (by positivity)).mpr hr.2⟩, ?_⟩
  rw [mul_div_cancel₀ _ (by positivity), he]
  simp [w]

end HolomorphicAnosov.Analysis.MarkedRectangle
