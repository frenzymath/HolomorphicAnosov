import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroSectionContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! HPS pp. 8 and 61--62: the three zero sections of the two component carriers and their
split product carrier are continuous in the native dependent topologies. This exact collection
is the zero-section input for assembling component embeddings into the split carrier. -/
theorem parameter_graph_all_zero_sections_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun p : A ↦ (⟨p, 0⟩ : Sigma E₁)) ∧
    Continuous (fun p : A ↦ (⟨p, 0⟩ : Sigma E₂)) ∧
    Continuous (fun p : A ↦
      (⟨p, (0, 0)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  have hzero := parameter_graph_zero_section_continuity (e := e)
  refine ⟨hzero.1, hzero.2, ?_⟩
  apply e.split_inducing.continuous_iff.mpr
  have hpair : Continuous (fun p : A ↦
      ((⟨p, 0⟩ : Sigma E₁), (⟨p, 0⟩ : Sigma E₂))) := hzero.1.prodMk hzero.2
  convert hpair using 1; funext p; rfl

end HolomorphicAnosov
