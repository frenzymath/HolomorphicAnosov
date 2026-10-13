import HolomorphicAnosov.Geometry.Riemannian.C1ChartSegmentReplacement

/-! C¹ paths contained in a sufficiently small neighborhood admit smooth replacements with the same
endpoints and a prescribed multiplicative length bound. -/

open Set MeasureTheory Bundle Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology _root_.Topology

namespace HolomorphicAnosov
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- For every `r > 1`, each point has a neighborhood in which every C¹ path admits a smooth path
with the same endpoints and length at most `r²` times its length. (Petersen, Thm 5.3.8, pp.148–150;
Cor. 5.3.10, p.150) -/
theorem locally_c1_path_smooth_replacement
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (x : M) (r : ℝ≥0) (hr : 1 < r) :
    ∃ U ∈ 𝓝 x, ∀ {a b : ℝ} {c : ℝ → M}, a < b →
      ContMDiffOn 𝓘(ℝ) I 1 c (Icc a b) → MapsTo c (Icc a b) U →
      ∃ σ : ℝ → M, ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
        σ 0 = c a ∧ σ 1 = c b ∧
        pathELength I σ 0 1 ≤ (r : ℝ≥0∞) * r * pathELength I c a b := by
  let e := extChartAt I x
  let T := trivializationAt E (TangentSpace I : M → Type _) x
  let W := {y : M | y ∈ (chartAt H x).source ∧
    ‖(T.symmL ℝ x).comp (T.continuousLinearMapAt ℝ y)‖ < r ∧
    ‖(T.symmL ℝ y).comp (T.continuousLinearMapAt ℝ x)‖ < r}
  have hW : W ∈ 𝓝 x := by
    filter_upwards [chart_source_mem_nhds H x,
      eventually_norm_symmL_trivializationAt_self_comp_lt E (TangentSpace I : M → Type _) x
        (show (1 : ℝ) < r from hr),
      eventually_norm_symmL_trivializationAt_comp_self_lt E (TangentSpace I : M → Type _) x
        (show (1 : ℝ) < r from hr)] with y hy h₁ h₂
    exact ⟨hy, h₁, h₂⟩
  have heW : e.symm ⁻¹' W ∈ 𝓝[range I] (e x) := by
    apply nhdsWithin_le_nhds
    have h := (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds (by simpa using hW)
    simpa only [e, extChartAt_to_inv] using h
  obtain ⟨δ, hδ, hs⟩ : ∃ δ > 0, Metric.ball (e x) δ ∩ range I ⊆
      e.target ∩ e.symm ⁻¹' W :=
    Metric.mem_nhdsWithin_iff.mp (inter_mem (extChartAt_target_mem_nhdsWithin x) heW)
  let s := Metric.ball (e x) δ ∩ range I
  let U := e ⁻¹' s ∩ e.source
  have hU : U ∈ 𝓝 x := by
    apply inter_mem _ (by simpa [e] using chart_source_mem_nhds H x)
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    dsimp only [s]
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hδ)
  refine ⟨U, hU, ?_⟩
  intro a b c hab hc hcU
  apply c1_chart_segment_replacement x r hab hc
    ((convex_ball (e x) δ).inter I.convex_range) (fun z hz ↦ (hs hz).1)
    (fun t ht ↦ (hcU ht).1) (fun t ht ↦ (hcU ht).2) (T.symmL ℝ x)
  · intro z hz v
    have hyW : e.symm z ∈ W := (hs hz).2
    have hbase : x ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have heq : T.symmL ℝ (e.symm z) =
        mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z := by
      rw [TangentBundle.symmL_trivializationAt hyW.1]
      rw [e.right_inv (hs hz).1]
    rw [← heq]
    calc
      ‖T.symmL ℝ (e.symm z) v‖ =
          ‖((T.symmL ℝ (e.symm z)).comp (T.continuousLinearMapAt ℝ x))
            (T.symmL ℝ x v)‖ := by
        rw [ContinuousLinearMap.comp_apply, T.continuousLinearMapAt_symmL hbase]
      _ ≤ ‖(T.symmL ℝ (e.symm z)).comp (T.continuousLinearMapAt ℝ x)‖ *
          ‖T.symmL ℝ x v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ r * ‖T.symmL ℝ x v‖ := mul_le_mul_of_nonneg_right hyW.2.2.le (norm_nonneg _)
  · intro t ht v
    have hyW : c t ∈ W := by
      have h := (hs (hcU ht).1).2
      change e.symm (e (c t)) ∈ W at h
      rwa [e.left_inv (hcU ht).2] at h
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hyW.1]
    calc
      _ = ‖((T.symmL ℝ x).comp (T.continuousLinearMapAt ℝ (c t))) v‖ := rfl
      _ ≤ ‖(T.symmL ℝ x).comp (T.continuousLinearMapAt ℝ (c t))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ r * ‖v‖ := mul_le_mul_of_nonneg_right hyW.2.1.le (norm_nonneg _)

end HolomorphicAnosov

