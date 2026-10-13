import HolomorphicAnosov.Linear.HyperbolicDecayAux13

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- On the spectral block outside the unit circle, inverse powers converge to zero in operator norm. -/
theorem generalizedSpectralPart_inverse_operator_decay
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : W ≃L[ℂ] W)
    (hT : ∀ μ, Module.End.HasEigenvalue T.toLinearEquiv.toLinearMap μ → ‖μ‖ ≠ 1) :
    let _P := generalizedSpectralPart T.toLinearEquiv.toLinearMap (fun μ ↦ ¬ ‖μ‖ < 1)
    let h := generalizedSpectralPart_mapsTo T.toLinearEquiv.toLinearMap
      T.symm.toLinearEquiv.toLinearMap (fun μ ↦ ¬ ‖μ‖ < 1) (equiv_commutes_inverse T)
    Tendsto (fun n : ℕ ↦ (T.symm.toContinuousLinearMap.restrict h) ^ n) atTop (𝓝 0) := by
  dsimp only
  let P := generalizedSpectralPart T.toLinearEquiv.toLinearMap (fun μ ↦ ¬ ‖μ‖ < 1)
  have hf : ∀ v ∈ P, T v ∈ P :=
    generalizedSpectralPart_mapsTo _ _ _ (Commute.refl _)
  have hb : ∀ v ∈ P, T.symm v ∈ P :=
    generalizedSpectralPart_mapsTo _ _ _ (equiv_commutes_inverse T)
  let B := invariantSubspaceEquiv T P hf hb
  have hBm : B.toContinuousLinearMap = T.toContinuousLinearMap.restrict hf :=
    invariantSubspaceEquiv_map T P hf hb
  have hBinv : B.symm.toContinuousLinearMap = T.symm.toContinuousLinearMap.restrict hb :=
    invariantSubspaceEquiv_symm_map T P hf hb
  rw [← hBinv]
  apply operator_powers_decay_of_eigenvalues
  intro μ hμ
  obtain ⟨hμne, hμinv⟩ := eigenvalue_inverse_reciprocal B hμ
  have hμinv' : Module.End.HasEigenvalue
      (T.toLinearEquiv.toLinearMap.restrict hf) μ⁻¹ := by
    change Module.End.HasEigenvalue B.toContinuousLinearMap.toLinearMap μ⁻¹ at hμinv
    rw [hBm, ContinuousLinearMap.toLinearMap_restrict] at hμinv
    exact hμinv
  have houtside := generalizedSpectralPart_restrict_eigenvalue
    T.toLinearEquiv.toLinearMap (fun z ↦ ¬ ‖z‖ < 1) hf hμinv'
  have hneq := hT μ⁻¹ (restrict_eigenvalue_lifts _ P hf hμinv')
  have hgt : 1 < ‖μ⁻¹‖ := lt_of_le_of_ne (le_of_not_gt houtside) (Ne.symm hneq)
  rw [norm_inv] at hgt
  exact (one_lt_inv₀ (norm_pos_iff.mpr hμne)).mp hgt



end HolomorphicAnosov
