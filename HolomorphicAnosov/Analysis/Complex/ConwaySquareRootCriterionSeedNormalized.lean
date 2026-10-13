import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootCriterionSeed
namespace HolomorphicAnosov
open Function Filter Metric Set
open scoped Topology _root_.Topology
theorem conway_square_root_criterion_seed_normalized {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hUproper : U ≠ Set.univ)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z)
    (a : ℂ) (ha : a ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ Set.InjOn F U ∧
      Set.MapsTo F U (Metric.ball (0 : ℂ) 1) ∧ F a = 0 ∧ deriv F a ≠ 0 := by
  obtain ⟨f, hf, hfi, hfm, hfd⟩ := conway_square_root_criterion_seed hUopen hUconnected hUproper hsqrt
  let F : ℂ → ℂ := fun z ↦ (f z - f a) / 2
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hf.sub (differentiableOn_const (c := f a))) |>.div_const 2
  · intro z hz w hw he
    apply hfi hz hw
    have he' := congrArg (fun q : ℂ ↦ (2 : ℂ) * q) he
    simpa [F, div_eq_mul_inv] using he'
  · intro z hz
    rw [mem_ball_zero_iff]
    have hsub : ‖f z - f a‖ < 2 := by
      calc
        ‖f z - f a‖ ≤ ‖f z‖ + ‖f a‖ := norm_sub_le _ _
        _ < 1 + 1 := add_lt_add (mem_ball_zero_iff.mp (hfm hz)) (mem_ball_zero_iff.mp (hfm ha))
        _ = 2 := by norm_num
    change ‖(f z - f a) / 2‖ < 1
    rw [norm_div]
    norm_num
    linarith
  · simp [F]
  · have hF := ((hf a ha).differentiableAt (hUopen.mem_nhds ha) |>.hasDerivAt.sub
      (hasDerivAt_const a (f a))).div_const 2
    dsimp [F] at hF ⊢
    rw [hF.deriv]
    exact div_ne_zero (by simpa using hfd a ha) (by norm_num)

end HolomorphicAnosov
