import HolomorphicAnosov.Linear.HyperbolicDecayAux01

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- The generalized eigenspaces for eigenvalues inside and outside the unit circle are complementary. (Alves, Theorem 3.1) -/
theorem generalized_spectral_cut_isCompl
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) :
    IsCompl (⨆ μ : ℂ, ⨆ (_ : ‖μ‖ < 1), T.maxGenEigenspace μ)
      (⨆ μ : ℂ, ⨆ (_ : ¬ ‖μ‖ < 1), T.maxGenEigenspace μ) := by
  refine ⟨?_, ?_⟩
  · exact T.independent_maxGenEigenspace.disjoint_biSup_biSup
      (Set.disjoint_left.mpr fun μ h hn ↦ hn h)
  · rw [codisjoint_iff]
    apply top_unique
    rw [← T.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun μ ↦ ?_
    by_cases hμ : ‖μ‖ < 1
    · exact le_sup_of_le_left (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl))



end HolomorphicAnosov
