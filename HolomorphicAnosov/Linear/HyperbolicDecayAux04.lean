import HolomorphicAnosov.Linear.HyperbolicDecayAux03

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- A commuting linear map preserves the selected generalized spectral subspace. -/
theorem generalizedSpectralPart_mapsTo
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T B : Module.End ℂ W) (P : ℂ → Prop) (h : Commute T B) :
    ∀ v ∈ generalizedSpectralPart T P, B v ∈ generalizedSpectralPart T P := by
  change generalizedSpectralPart T P ≤ (generalizedSpectralPart T P).comap B
  rw [← Submodule.map_le_iff_le_comap]
  simp only [generalizedSpectralPart, Submodule.map_iSup, iSup_le_iff]
  intro μ hμ v hv
  rcases hv with ⟨x, hx, rfl⟩
  exact Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem hμ (T.mapsTo_maxGenEigenspace_of_comm h μ hx))



end HolomorphicAnosov
