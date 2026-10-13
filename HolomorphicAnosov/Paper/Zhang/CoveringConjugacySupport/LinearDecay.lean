import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyDecayTransfer
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.SpectralCoordinates
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.CoordinateDecay

open scoped Topology
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- The full C9 conclusion for an arbitrary finite-dimensional real carrier. -/
theorem covering_conjugacy_linear_decay_g15
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V ≃L[ℝ] V)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    ∃ Vs Vu : Submodule ℝ V,
      (Vs : Set V) = {v | Tendsto (fun n : ℕ ↦ A^[n] v) atTop (𝓝 0)} ∧
      (Vu : Set V) = {v | Tendsto (fun n : ℕ ↦ A.symm^[n] v) atTop (𝓝 0)} ∧
      IsCompl Vs Vu := by
  classical
  obtain ⟨e, he⟩ := covering_conjugacy_spectral_coordinates_g15 A hA
  let B : (Fin (Module.finrank ℝ V) → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    (e.symm.trans A).trans e
  obtain ⟨Es, Eu, hs, hu, hcompl⟩ :=
    covering_conjugacy_coordinate_decay_g15 (Module.finrank ℝ V) B.toLinearEquiv he
  refine ⟨Es.map e.symm.toLinearEquiv.toLinearMap,
    Eu.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_,
      Submodule.isCompl_map e.symm.toLinearEquiv hcompl⟩
  · ext v
    have hm : v ∈ Es.map e.symm.toLinearEquiv.toLinearMap ↔ e v ∈ Es := by
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro hv
        exact ⟨e v, hv, e.symm_apply_apply v⟩
    change v ∈ Es.map e.symm.toLinearEquiv.toLinearMap ↔ _
    rw [hm]
    change e v ∈ (Es : Set _) ↔ _
    rw [hs]
    exact (covering_conjugacy_transfer_decay_g15 e A B (by intro w; simp [B]) v).symm
  · ext v
    have hm : v ∈ Eu.map e.symm.toLinearEquiv.toLinearMap ↔ e v ∈ Eu := by
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro hv
        exact ⟨e v, hv, e.symm_apply_apply v⟩
    change v ∈ Eu.map e.symm.toLinearEquiv.toLinearMap ↔ _
    rw [hm]
    change e v ∈ (Eu : Set _) ↔ _
    rw [hu]
    exact (covering_conjugacy_transfer_decay_g15 e A.symm B.symm
      (by intro w; simp [B]) v).symm


end HolomorphicAnosov
