import HolomorphicAnosov.Linear.HyperbolicDecayAux19

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- The forward- and inverse-decay subspaces of a finite-dimensional complex hyperbolic automorphism
are complementary. (Alves, Thm 5.5) -/
theorem complex_full_decay_isCompl
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : W ≃L[ℂ] W)
    (hT : ∀ μ, Module.End.HasEigenvalue T.toLinearEquiv.toLinearMap μ → ‖μ‖ ≠ 1) :
    IsCompl (fullForwardDecay T) (fullForwardDecay T.symm) := by
  let t := T.toLinearEquiv.toLinearMap
  let S := generalizedSpectralPart t (fun μ ↦ ‖μ‖ < 1)
  let U := generalizedSpectralPart t (fun μ ↦ ¬ ‖μ‖ < 1)
  have hc : IsCompl S U := generalized_spectral_cut_isCompl t
  have hsf : ∀ v ∈ S, T v ∈ S := generalizedSpectralPart_mapsTo t t _ (Commute.refl _)
  have hsb : ∀ v ∈ S, T.symm v ∈ S :=
    generalizedSpectralPart_mapsTo t _ _ (equiv_commutes_inverse T)
  have huf : ∀ v ∈ U, T v ∈ U := generalizedSpectralPart_mapsTo t t _ (Commute.refl _)
  have hub : ∀ v ∈ U, T.symm v ∈ U :=
    generalizedSpectralPart_mapsTo t _ _ (equiv_commutes_inverse T)
  let ES := invariantSubspaceEquiv T S hsf hsb
  let EU := invariantSubspaceEquiv T U huf hub
  have hsop : Tendsto (fun n : ℕ ↦ ES.toContinuousLinearMap ^ n) atTop (𝓝 0) := by
    rw [show ES.toContinuousLinearMap = T.toContinuousLinearMap.restrict hsf from
      invariantSubspaceEquiv_map T S hsf hsb]
    apply operator_powers_decay_of_eigenvalues
    intro μ hμ
    exact generalizedSpectralPart_restrict_eigenvalue t (fun z ↦ ‖z‖ < 1) hsf hμ
  have huop : Tendsto (fun n : ℕ ↦ EU.symm.toContinuousLinearMap ^ n) atTop (𝓝 0) := by
    rw [show EU.symm.toContinuousLinearMap = T.symm.toContinuousLinearMap.restrict hub from
      invariantSubspaceEquiv_symm_map T U huf hub]
    exact generalizedSpectralPart_inverse_operator_decay T hT
  have hsorbit (v : S) : Tendsto (fun n : ℕ ↦ (T ^ n) (v : W)) atTop (𝓝 0) := by
    have h := continuous_subtype_val.tendsto (0 : S) |>.comp
      (equiv_pointwise_decay_of_operator_decay ES hsop v)
    simpa only [Function.comp_def, Submodule.coe_zero, ES, invariantSubspaceEquiv_pow_coe] using h
  have huorbit (v : U) : Tendsto (fun n : ℕ ↦ (T.symm ^ n) (v : W)) atTop (𝓝 0) := by
    have h := continuous_subtype_val.tendsto (0 : U) |>.comp
      (equiv_pointwise_decay_of_operator_decay EU.symm huop v)
    have he : EU.symm = invariantSubspaceEquiv T.symm U hub huf := by
      ext z
      rfl
    simpa only [Function.comp_def, Submodule.coe_zero, he,
      invariantSubspaceEquiv_pow_coe] using h
  have hSeq : fullForwardDecay T = S := by
    apply le_antisymm
    · intro v hv
      obtain ⟨⟨s, u⟩, hsu, -⟩ := Submodule.existsUnique_add_of_isCompl_prod hc v
      have hu : Tendsto (fun n : ℕ ↦ (T ^ n) (u : W)) atTop (𝓝 0) := by
        have h := hv.sub (hsorbit s)
        convert h using 1
        · funext n
          rw [← hsu, map_add, add_sub_cancel_left]
        · simp
      have hue : Tendsto (fun n : ℕ ↦ (EU ^ n) u) atTop (𝓝 0) := by
        apply tendsto_subtype_rng.mpr
        simpa only [EU, invariantSubspaceEquiv_pow_coe, Submodule.coe_zero] using hu
      have huz := eq_zero_of_forward_decay_of_inverse_operator_decay EU huop u hue
      rw [← hsu, huz]
      simp
    · intro v hv
      exact hsorbit ⟨v, hv⟩
  have hUeq : fullForwardDecay T.symm = U := by
    apply le_antisymm
    · intro v hv
      obtain ⟨⟨s, u⟩, hsu, -⟩ := Submodule.existsUnique_add_of_isCompl_prod hc v
      have hs : Tendsto (fun n : ℕ ↦ (T.symm ^ n) (s : W)) atTop (𝓝 0) := by
        have h := hv.sub (huorbit u)
        convert h using 1
        · funext n
          rw [← hsu, map_add, add_sub_cancel_right]
        · simp
      have hse : Tendsto (fun n : ℕ ↦ (ES.symm ^ n) s) atTop (𝓝 0) := by
        apply tendsto_subtype_rng.mpr
        have he : ES.symm = invariantSubspaceEquiv T.symm S hsb hsf := by
          ext z
          rfl
        simpa only [he, invariantSubspaceEquiv_pow_coe, Submodule.coe_zero] using hs
      have hsz := eq_zero_of_forward_decay_of_inverse_operator_decay ES.symm
        (by simpa only [ContinuousLinearEquiv.symm_symm] using hsop) s hse
      rw [← hsu, hsz]
      simp
    · intro v hv
      exact huorbit ⟨v, hv⟩
  rw [hSeq, hUeq]
  exact hc

end HolomorphicAnosov
