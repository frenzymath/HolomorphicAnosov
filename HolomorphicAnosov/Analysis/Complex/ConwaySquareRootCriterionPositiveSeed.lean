import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootCriterionSeedNormalized

/-!
# Nonemptiness of Conway's normalized univalent family

Source: Conway, *Functions of One Complex Variable*, second edition, VII Lemma 4.3,
printed pp. 161–163. DAG node: `analysis.conway_square_root_criterion_positive_seed`.
-/

namespace HolomorphicAnosov

/-- The square-root criterion supplies an injective holomorphic disk map with zero value
and positive real derivative at a prescribed point.

Source and proof: Conway VII Lemma 4.3, pp. 161–163, the nonemptiness of its normalized
family. Start with the zero-normalized disk injection `f` and write `d = f'(a) ≠ 0`.
Multiplication by `c = |d| / d` preserves norms because `|c| = 1`, and preserves
injectivity because `c ≠ 0`. For `F = c f`, differentiation gives `F'(a) = |d|`,
which has zero imaginary part and strictly positive real part. Also `F(a) = 0`.
-/
theorem conway_square_root_criterion_positive_seed
    {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hUproper : U ≠ Set.univ)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z)
    (a : ℂ) (ha : a ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ Set.InjOn F U ∧
      Set.MapsTo F U (Metric.ball (0 : ℂ) 1) ∧
      F a = 0 ∧ (deriv F a).im = 0 ∧ 0 < (deriv F a).re := by
  obtain ⟨f, hf, hfi, hfm, hfa, hfd⟩ :=
    conway_square_root_criterion_seed_normalized hUopen hUconnected hUproper hsqrt a ha
  let c : ℂ := (‖deriv f a‖ : ℂ) / deriv f a
  have hc : ‖c‖ = 1 := by
    simp [c, hfd]
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  have hder : deriv (fun z ↦ c * f z) a = (‖deriv f a‖ : ℂ) := by
    rw [((hf.differentiableAt (hUopen.mem_nhds ha)).hasDerivAt.const_mul c).deriv]
    exact div_mul_cancel₀ _ hfd
  refine ⟨fun z ↦ c * f z, hf.const_mul c, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz w hw he
    exact hfi hz hw (mul_left_cancel₀ hc0 he)
  · intro z hz
    simpa only [mem_ball_zero_iff, norm_mul, hc, one_mul] using hfm hz
  · simp [hfa]
  · simp [hder]
  · simpa [hder] using norm_pos_iff.mpr hfd


end HolomorphicAnosov
