import HolomorphicAnosov.Analysis.MovingOperatorNormLocalBound

noncomputable section
open Set Filter
open scoped _root_.Topology
namespace HolomorphicAnosov
universe u v w z
/-- Uniform near-isometry in moving finite-dimensional frames.
At an isometric parameter both strict bounds hold on the compact model unit
sphere. Joint continuity and compactness give one parameter neighborhood for all
sphere vectors. Normalize each nonzero frame coordinate and cancel its positive
normalization factor; the zero vector gives both bounds immediately. -/
theorem moving_isometry_eventually_norm_bounds_g18
    {B : Type u} [TopologicalSpace B]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : B → Type w} {F : B → Type z}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    (frame : ∀ x, V ≃ₗ[ℝ] E x) (A : ∀ x, E x →L[ℝ] F x)
    (hsource : Continuous (fun p : B × V ↦ ‖frame p.1 p.2‖))
    (himage : Continuous (fun p : B × V ↦ ‖A p.1 (frame p.1 p.2)‖))
    (x₀ : B) (hisom : ∀ v, ‖A x₀ v‖ = ‖v‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ v : E x,
      (1 - ε) * ‖v‖ ≤ ‖A x v‖ ∧ ‖A x v‖ ≤ (1 + ε) * ‖v‖ := by
  have huniform : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : V) 1,
      (1 - ε) * ‖frame x v‖ < ‖A x (frame x v)‖ ∧
        ‖A x (frame x v)‖ < (1 + ε) * ‖frame x v‖ := by
    apply (isCompact_sphere (0 : V) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hvnorm : ‖v‖ = 1 := by simpa using hv
    have hvne : v ≠ 0 := by intro h; simp [h] at hvnorm
    have hpos : 0 < ‖frame x₀ v‖ := norm_pos_iff.mpr (by
      intro h; apply hvne; exact (frame x₀).injective (by simpa using h))
    have hl : (1 - ε) * ‖frame x₀ v‖ < ‖A x₀ (frame x₀ v)‖ := by
      rw [hisom]; nlinarith
    have hu : ‖A x₀ (frame x₀ v)‖ < (1 + ε) * ‖frame x₀ v‖ := by
      rw [hisom]; nlinarith
    exact ((continuous_const.mul hsource).continuousAt.eventually_lt
      himage.continuousAt hl).and (himage.continuousAt.eventually_lt
        (continuous_const.mul hsource).continuousAt hu)
  filter_upwards [huniform] with x hx v
  obtain ⟨w, rfl⟩ := (frame x).surjective v
  by_cases hw : w = 0
  · simp [hw]
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  let u : V := ‖w‖⁻¹ • w
  have hu : u ∈ Metric.sphere (0 : V) 1 := by simp [u, norm_smul, hnorm]
  have hc : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  obtain ⟨hl, hu'⟩ := hx u hu
  have hl' : ‖w‖⁻¹ * ((1 - ε) * ‖frame x w‖) ≤ ‖w‖⁻¹ * ‖A x (frame x w)‖ := by
    simpa [u, norm_smul, mul_assoc, mul_comm, mul_left_comm] using hl.le
  have hu'' : ‖w‖⁻¹ * ‖A x (frame x w)‖ ≤ ‖w‖⁻¹ * ((1 + ε) * ‖frame x w‖) := by
    simpa [u, norm_smul, mul_assoc, mul_comm, mul_left_comm] using hu'.le
  exact ⟨(mul_le_mul_iff_right₀ hc).mp (by simpa [mul_comm] using hl'),
    (mul_le_mul_iff_right₀ hc).mp (by simpa [mul_comm] using hu'')⟩
end HolomorphicAnosov
