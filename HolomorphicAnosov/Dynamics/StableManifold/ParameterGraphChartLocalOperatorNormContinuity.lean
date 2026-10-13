import HolomorphicAnosov.Analysis.FrameOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTotalMapContinuity

open Set Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- HPS, Invariant Manifolds, pp.8, 35, 61–62: local continuity of the original fibre
operator norms. Extract continuous component total maps and compose with a source
chart frame. The atlas norm functions give joint continuity of source and image norms.
Apply compact sphere norm-ratio continuity to the second block. For the inverse first
block, use the source frame transported by the first block; inverse evaluation then
reduces to the original source frame. Restriction to the open chart neighborhood gives
continuity at its centre. This works in varying rank and includes rank zero. -/
theorem parameter_graph_chart_local_operator_norm_continuity
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
    ∀ p : A,
      ContinuousAt (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖) p ∧
      ContinuousAt (fun q ↦ ‖T₂ q‖) p := by
  intro p
  have hmaps := parameter_graph_total_map_continuity e h T₁ T₂ hT
  constructor
  · let U := (e.first.chart p).baseSet
    let j (q : U) := (e.first.coordinates p q.val q.property).symm
    have hf := atlas_frame_continuous e.first p
    have hden : Continuous (fun z : U × FiniteFiberModel (e.first.rank p) ↦
        ‖j z.1 z.2‖) := e.first.continuous_norm.comp hf
    have hnum : Continuous (fun z : U × FiniteFiberModel (e.first.rank p) ↦
        ‖T₁ z.1.val (j z.1 z.2)‖) := e.first.continuous_norm.comp (hmaps.1.comp hf)
    let j' (q : U) := (j q).trans (T₁ q.val)
    have hnum' : Continuous (fun z : U × FiniteFiberModel (e.first.rank p) ↦
        ‖(T₁ z.1.val).symm (j' z.1 z.2)‖) := by
      simpa only [j', ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply] using hden
    have hinv := continuous_norm_of_frame j'
      (fun q : U ↦ (T₁ q.val).symm.toContinuousLinearMap) hnum hnum'
    have hon : ContinuousOn (fun q ↦ ‖(T₁ q).symm.toContinuousLinearMap‖) U :=
      continuousOn_iff_continuous_domRestrict.mpr hinv
    exact hon.continuousAt ((e.first.chart p).open_baseSet.mem_nhds
      (e.first.mem_baseSet p))
  · let U := (e.second.chart p).baseSet
    let j (q : U) := (e.second.coordinates p q.val q.property).symm
    have hf := atlas_frame_continuous e.second p
    have hden : Continuous (fun z : U × FiniteFiberModel (e.second.rank p) ↦
        ‖j z.1 z.2‖) := e.second.continuous_norm.comp hf
    have hnum : Continuous (fun z : U × FiniteFiberModel (e.second.rank p) ↦
        ‖T₂ z.1.val (j z.1 z.2)‖) := e.second.continuous_norm.comp (hmaps.2.comp hf)
    have hnorm := continuous_norm_of_frame j (fun q : U ↦ T₂ q.val) hden hnum
    have hon : ContinuousOn (fun q ↦ ‖T₂ q‖) U :=
      continuousOn_iff_continuous_domRestrict.mpr hnorm
    exact hon.continuousAt ((e.second.chart p).open_baseSet.mem_nhds
      (e.second.mem_baseSet p))

end
end HolomorphicAnosov
