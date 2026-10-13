import HolomorphicAnosov.Analysis.WellsForwardSequenceOperator
import HolomorphicAnosov.Analysis.WellsVerticalC0Injection
import HolomorphicAnosov.Analysis.WellsComplementarySmoothFixedPoints

open scoped ZeroAtInfty ContDiff

namespace HolomorphicAnosov.Analysis

/-- The whole-base smooth family of forward sequences in Wells (1976),
pp.290–291. Construct the forward operator and the zeroth horizontal injection.
Their complementary supports give the exact maximum estimates for Picard on each
closed ball of base norm. Smooth inversion then selects the unique fixed sequence
over every point of the original base ball, with norm bounded by the base norm
and unit Lipschitz dependence. Evaluating its fixed equation gives the component
equations below. Uniqueness is on the full original sequence ball. -/
theorem wells_forward_smooth_sequences
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    (U : E₁ →L[ℝ] E₁) (V : E₂ →L[ℝ] E₂) (q s ε : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hε : 0 ≤ ε) (r : ℕ∞) (hr : 1 ≤ r)
    (hsmall : max (‖U‖ * (q + ε)) (q⁻¹ * (‖V‖ + ε)) < 1)
    (C : C₀(ℕ, E₁ × E₂) → C₀(ℕ, E₁ × E₂)) (hC0 : C 0 = 0)
    (hC : ContDiffOn ℝ (r : ℕ∞ω) C (Metric.ball 0 s))
    (hCLip : ∀ w ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
      ∀ z ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
      ‖C w - C z‖ ≤ ε * ‖w - z‖) :
    ∃ f : E₂ → C₀(ℕ, E₁ × E₂),
      ContDiffOn ℝ (r : ℕ∞ω) f (Metric.ball 0 s) ∧ f 0 = 0 ∧
      (∀ p ∈ Metric.ball (0 : E₂) s,
        ‖f p‖ ≤ ‖p‖ ∧
        f p 0 = (q • U (f p 1).1 - U (C (f p) 0).1, p) ∧
        ∀ n, f p (n + 1) =
          (q • U (f p (n + 2)).1 - U (C (f p) (n + 1)).1,
            q⁻¹ • (V (f p n).2 + (C (f p) n).2))) ∧
      (∀ p ∈ Metric.ball (0 : E₂) s, ∀ t ∈ Metric.ball (0 : E₂) s,
        ‖f p - f t‖ ≤ ‖p - t‖) ∧
      (∀ p ∈ Metric.ball (0 : E₂) s,
        ∀ z ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s,
        z 0 = (q • U (z 1).1 - U (C z 0).1, p) →
        (∀ n, z (n + 1) =
          (q • U (z (n + 2)).1 - U (C z (n + 1)).1,
            q⁻¹ • (V (z n).2 + (C z n).2))) → z = f p) := by
  let Q := max (‖U‖ * (q + ε)) (q⁻¹ * (‖V‖ + ε))
  have hQ : 0 ≤ Q := le_max_of_le_left (mul_nonneg (norm_nonneg _) (add_nonneg hq.le hε))
  obtain ⟨Γ, hΓ0, hΓsmooth, hΓzero, hΓnext, hΓLip⟩ :=
    wells_forward_sequence_operator U V q s ε hq r C hC0 hC hCLip
  obtain ⟨I, hI0, hInext, hInorm, hImax⟩ :=
    wells_vertical_c0_injection (E₁ := E₁) (E₂ := E₂)
  have hΓsnd (w : C₀(ℕ, E₁ × E₂)) : (Γ w 0).2 = 0 := by rw [hΓzero]
  have hmax (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s)
      (w : C₀(ℕ, E₁ × E₂)) (hw : ‖w‖ ≤ ‖p‖) :
      ‖I p + Γ w‖ ≤ max ‖p‖ (Q * ‖w‖) := by
    rw [hImax p (Γ w) (hΓsnd w)]
    apply max_le_max le_rfl
    have hwmem : w ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s := by
      simpa using hw.trans_lt (show ‖p‖ < s by simpa using hp)
    simpa [hΓ0] using hΓLip w hwmem 0 (by simpa using hs)
  have hmaxdiff (p t : E₂) (w : C₀(ℕ, E₁ × E₂))
      (hw : w ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s)
      (z : C₀(ℕ, E₁ × E₂)) (hz : z ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s) :
      ‖(I p + Γ w) - (I t + Γ z)‖ ≤ max ‖p - t‖ (Q * ‖w - z‖) := by
    have heq : (I p + Γ w) - (I t + Γ z) = I (p - t) + (Γ w - Γ z) := by
      rw [map_sub]; abel
    rw [heq, hImax (p - t) (Γ w - Γ z) (by simp [hΓsnd])]
    exact max_le_max le_rfl (hΓLip w hw z hz)
  obtain ⟨f, hfsmooth, hf0, hfixed, hfLip, hunique⟩ :=
    HolomorphicAnosov.wells_complementary_smooth_fixed_points I hInorm Γ s Q hs hQ
      hsmall r hr hΓsmooth hΓLip hmax hmaxdiff
  refine ⟨f, hfsmooth, hf0, ?_, hfLip, ?_⟩
  · intro p hp
    have heq := sub_eq_iff_eq_add.mp (hfixed p hp).2
    refine ⟨(hfixed p hp).1, ?_, ?_⟩
    · have h := congrArg (fun w : C₀(ℕ, E₁ × E₂) ↦ w 0) heq
      simpa [hI0, hΓzero] using h
    · intro n
      have h := congrArg (fun w : C₀(ℕ, E₁ × E₂) ↦ w (n + 1)) heq
      simpa [hInext, hΓnext] using h
  · intro p hp z hz hz0 hzn
    apply hunique p hp z hz
    apply sub_eq_iff_eq_add.mpr
    ext1 n
    cases n with
    | zero => simpa [hI0, hΓzero] using hz0
    | succ n => simpa [hInext, hΓnext] using hzn n

end HolomorphicAnosov.Analysis

