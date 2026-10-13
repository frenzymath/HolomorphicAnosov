import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphComponentEmbeddingInducing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroPairingContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-!
HPS pp. 61--62, zero-section restriction bridge.  The split inducing law and the genuine
component fibre inducing laws are used to show continuity of the canonical embeddings
`(p,v) ↦ (p,(v,0))` and `(p,w) ↦ (p,(0,w))` from component total spaces into the split total
space.  Restricting the continuous product total map along these embeddings is the exact API
step needed to obtain the two component total maps.  This is isolated as a named Stage 2
proposition because the current atlas structure exposes the inducing fields but no assembled
embedding theorem.
-/
theorem parameter_graph_component_embedding_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun z : Sigma E₁ ↦
      (⟨z.1, (z.2, 0)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) ∧
    Continuous (fun z : Sigma E₂ ↦
      (⟨z.1, (0, z.2)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  have hpair := parameter_graph_zero_pairing_continuity (e := e)
  refine ⟨hpair, ?_⟩
  have hproj : Continuous (fun z : Sigma E₂ ↦ z.1) := by
    apply continuous_iff_continuousAt.2
    intro z
    let c := e.second.chart z.1
    have hzsource : z ∈ c.toOpenPartialHomeomorph.source :=
      c.mem_source.mpr (e.second.mem_baseSet z.1)
    have hc := c.toOpenPartialHomeomorph.continuousAt hzsource
    have hf := ContinuousAt.comp (f := c.toOpenPartialHomeomorph)
      (g := Prod.fst) continuous_fst.continuousAt hc
    apply hf.congr_of_eventuallyEq
    filter_upwards [c.toOpenPartialHomeomorph.open_source.mem_nhds hzsource] with z hz
    simpa only [Function.comp_apply] using (c.proj_toFun z hz).symm
  have hzero : Continuous (fun z : Sigma E₂ ↦ (⟨z.1, 0⟩ : Sigma E₁)) :=
    (parameter_graph_zero_section_continuity (e := e)).1.comp hproj
  have hpair' : Continuous (fun z : Sigma E₂ ↦
      ((⟨z.1, 0⟩ : Sigma E₁), z)) := hzero.prodMk continuous_id
  apply e.split_inducing.continuous_iff.mpr
  convert hpair' using 1; funext z; rfl

end HolomorphicAnosov
