import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
open scoped ContDiff Manifold Topology _root_.Topology
open Set TopologicalSpace
noncomputable section
namespace HolomorphicAnosov
/-- A diffeomorphism from an open coordinate domain onto an open manifold subset gives a chart in
the maximal atlas with the specified coordinate target and inverse formula. (Lee, Lemma 1.10,
pp. 13–15, and Ch. 2, p. 36) -/
theorem open_diffeomorph_maximal_chart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (B : Opens E) (U : Opens M) (b : B) (h : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) B U ∞) :
    ∃ c : OpenPartialHomeomorph M E,
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ M ∧ c.target = B ∧
      ∀ v : B, c.symm v = (h v : M) := by
  let eB := B.openPartialHomeomorphSubtypeCoe ⟨b⟩
  let eU := U.openPartialHomeomorphSubtypeCoe ⟨h b⟩
  let eH := h.symm.toHomeomorph.toOpenPartialHomeomorph
  let c := eU.symm.trans (eH.trans eB)
  have hB : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ eB.symm eB.target := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff B eB.symm eB.target y).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun z hz ↦ eB.right_inv hz) hy
  have hU : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ eU.symm eU.target := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U eU.symm eU.target y).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun z hz ↦ eU.right_inv hz) hy
  have hc : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c c.source := by
    exact (contMDiff_subtype_val.comp h.symm.contMDiff).comp_contMDiffOn
      (hU.mono inter_subset_left)
  have hci : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c.symm c.target := by
    exact (contMDiff_subtype_val.comp h.contMDiff).comp_contMDiffOn
      (hB.mono (by simp [c, eH, eB, eU]))
  refine ⟨c, c.mem_maximalAtlas_of_contMDiffOn hc hci, ?_, ?_⟩
  · simp [c, eH, eB, eU]
  · intro v
    change (h (eB.symm v) : M) = (h v : M)
    congr 2
    apply Subtype.ext
    exact eB.right_inv (by simp [eB])

end HolomorphicAnosov
