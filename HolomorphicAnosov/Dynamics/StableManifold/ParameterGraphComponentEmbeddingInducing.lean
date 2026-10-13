import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroSectionContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroPairingContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAllZeroSectionsContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! HPS pp. 8 and 61--62, zero-section topology bridge for the split carrier. -/
theorem parameter_graph_component_embedding_inducing
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun p : A ↦
      (⟨p, (0, 0)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  have hz := parameter_graph_all_zero_sections_continuity e
  have _ := parameter_graph_zero_pairing_continuity e
  exact hz.2.2

end HolomorphicAnosov
