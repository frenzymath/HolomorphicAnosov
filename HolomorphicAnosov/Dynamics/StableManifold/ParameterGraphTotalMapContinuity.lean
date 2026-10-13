import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphComponentEmbeddingContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! This file proves continuity of the component total maps induced by a continuous split product map (HPS, Theorem 5.5, pp.61–62). -/
theorem parameter_graph_total_map_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (hT : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, (T₁ z.1 z.2.1, T₂ z.1 z.2.2)⟩ :
        Sigma (fun p ↦ E₁ p × E₂ p)))) :
    Continuous (fun z : Sigma E₁ ↦
      (⟨h z.1, T₁ z.1 z.2⟩ : Sigma E₁)) ∧
    Continuous (fun z : Sigma E₂ ↦
      (⟨h z.1, T₂ z.1 z.2⟩ : Sigma E₂)) := by
  have hemb := parameter_graph_component_embedding_continuity (e := e)
  have hs : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      ((⟨z.1, z.2.1⟩ : Sigma E₁), (⟨z.1, z.2.2⟩ : Sigma E₂))) :=
    e.split_inducing.continuous
  have hp1 : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨z.1, z.2.1⟩ : Sigma E₁)) := continuous_fst.comp hs
  have hp2 : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨z.1, z.2.2⟩ : Sigma E₂)) := continuous_snd.comp hs
  have h1 : Continuous (fun z : Sigma E₁ ↦
      (⟨h z.1, T₁ z.1 z.2⟩ : Sigma E₁)) := by
    have hc := hp1.comp (hT.comp hemb.1)
    convert hc using 1; funext z; rfl
  have h2 : Continuous (fun z : Sigma E₂ ↦
      (⟨h z.1, T₂ z.1 z.2⟩ : Sigma E₂)) := by
    have hc := hp2.comp (hT.comp hemb.2)
    convert hc using 1; funext z; rfl
  exact ⟨h1, h2⟩

end HolomorphicAnosov
