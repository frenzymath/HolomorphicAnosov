import HolomorphicAnosov.Analysis.MovingOperatorNormLocalBound

noncomputable section
open Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
universe u v w z

/-- The strict bound form of `moving_operator_norm_eventually_le`. -/
theorem moving_operator_norm_eventually_lt
    {B : Type u} [TopologicalSpace B]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : B → Type w} {F : B → Type z}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    (frame : ∀ x, V ≃ₗ[ℝ] E x) (A : ∀ x, E x →L[ℝ] F x)
    (hsource : Continuous (fun p : B × V ↦ ‖frame p.1 p.2‖))
    (himage : Continuous (fun p : B × V ↦ ‖A p.1 (frame p.1 p.2)‖))
    (x₀ : B) {c : ℝ} (hc : ‖A x₀‖ < c) :
    ∀ᶠ x in 𝓝 x₀, ‖A x‖ < c := by
  obtain ⟨q, hqc, hq⟩ := moving_operator_norm_eventually_le frame A hsource himage x₀ hc
  exact hq.mono fun _ hx ↦ hx.trans_lt hqc


end HolomorphicAnosov
