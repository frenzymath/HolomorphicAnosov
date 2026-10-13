import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroSectionContinuity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! This file proves continuity of pairing a component point with the zero vector in the other component (HPS, pp.8, 61–62). -/
theorem parameter_graph_zero_pairing_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun z : Sigma E₁ ↦
      (⟨z.1, (z.2, 0)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  have hproj : Continuous (fun z : Sigma E₁ ↦ z.1) := by
    apply continuous_iff_continuousAt.2
    intro z
    let c := e.first.chart z.1
    have hzsource : z ∈ c.toOpenPartialHomeomorph.source :=
      c.mem_source.mpr (e.first.mem_baseSet z.1)
    have hc := c.toOpenPartialHomeomorph.continuousAt hzsource
    have hf := ContinuousAt.comp (f := c.toOpenPartialHomeomorph)
      (g := Prod.fst) continuous_fst.continuousAt hc
    apply hf.congr_of_eventuallyEq
    filter_upwards [c.toOpenPartialHomeomorph.open_source.mem_nhds hzsource] with z hz
    simpa only [Function.comp_apply] using (c.proj_toFun z hz).symm
  have hzero : Continuous (fun z : Sigma E₁ ↦ (⟨z.1, 0⟩ : Sigma E₂)) :=
    (parameter_graph_zero_section_continuity (e := e)).2.comp hproj
  have hpair : Continuous (fun z : Sigma E₁ ↦
      (z, (⟨z.1, 0⟩ : Sigma E₂))) := continuous_id.prodMk hzero
  apply e.split_inducing.continuous_iff.mpr
  convert hpair using 1; funext z; rfl

end HolomorphicAnosov
