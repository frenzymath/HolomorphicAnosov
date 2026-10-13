import HolomorphicAnosov.Analysis.Regularity.JourneInverseDerivativeLowerBound

/-!
This file proves a local anti-Lipschitz estimate for inverse branches.
-/ 

noncomputable section

namespace HolomorphicAnosov

open Set
open scoped Topology _root_.Topology

theorem eventually_antiLipschitz_of_openPartialHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (e : OpenPartialHomeomorph E F) {x : E} (hx : x ∈ e.source)
    {ρ K : ℝ} (hρ : 0 < ρ)
    (_hball : Metric.ball (e x) ρ ⊆ e.target)
    (hinv : ∀ u ∈ Metric.ball (e x) ρ, ∀ v ∈ Metric.ball (e x) ρ,
      ‖e.symm u - e.symm v‖ ≤ K * ‖u - v‖) :
    ∀ᶠ z in 𝓝 x, ‖z - x‖ ≤ K * ‖e z - e x‖ := by
  have hxe : e x ∈ Metric.ball (e x) ρ := by
    rw [Metric.mem_ball]
    simpa using hρ
  have hball_nhds : Metric.ball (e x) ρ ∈ 𝓝 (e x) :=
    Metric.isOpen_ball.mem_nhds hxe
  have he_preimage : e ⁻¹' Metric.ball (e x) ρ ∈ 𝓝 x :=
    (e.continuousAt hx).preimage_mem_nhds hball_nhds
  have hsource_nhds : e.source ∈ 𝓝 x := e.open_source.mem_nhds hx
  filter_upwards [hsource_nhds, he_preimage] with z hzsource hzball
  have h := hinv (e z) hzball (e x) hxe
  simpa only [e.left_inv hzsource, e.left_inv hx] using h


theorem hasFDerivAt_norm_lower_of_openPartialHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) {x : E} (hx : x ∈ e.source)
    {ρ K : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (e x) ρ ⊆ e.target)
    (hinv : ∀ u ∈ Metric.ball (e x) ρ, ∀ v ∈ Metric.ball (e x) ρ,
      ‖e.symm u - e.symm v‖ ≤ K * ‖u - v‖)
    {f : E → F} {f' : E →L[ℝ] F}
    (hf : f = (e : E → F)) (hderiv : HasFDerivAt f f' x) :
    ∀ v, ‖v‖ ≤ K * ‖f' v‖ := by
  apply hasFDerivAt_norm_lower_of_eventually_antiLipschitz hderiv
  simpa [hf] using
    (eventually_antiLipschitz_of_openPartialHomeomorph e hx hρ hball hinv)

theorem inverse_opNorm_le_of_norm_lower
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E ≃L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hlower : ∀ v, ‖v‖ ≤ K * ‖A v‖) :
    ‖A.symm.toContinuousLinearMap‖ ≤ K := by
  apply A.symm.toContinuousLinearMap.opNorm_le_bound hK
  intro w
  have h := hlower (A.symm w)
  rw [A.apply_symm_apply] at h
  exact h

end HolomorphicAnosov


