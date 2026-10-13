import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Between

open Set
namespace HolomorphicAnosov

/-- Two nondegenerate collinear segments that meet only at their joint merge to
one segment, and the joint is strictly between the outer endpoints.

Agent-written collinear-vertex reduction for `topo.cairns_simple_polygon_schoenflies`,
step3, in the setting of Cairns, An Elementary Proof of the Jordan-Schoenflies Theorem
(1951), Theorem2.1 pp.860–861. The source does not spell out this general vector-space
lemma; its proof is recorded honestly as agent-origin. Collinear betweenness
trichotomy gives three cases. Either b lies between a and c, or a or c lies in both
old segments. The latter cases contradict their intersection condition and the
nondegenerate hypotheses. Thus b lies in the open outer segment. Convexity gives
inclusion of the old segments in the outer one; splitting that outer segment at b
gives the reverse inclusion. No topology or planar dimension is needed, and the
hypotheses themselves exclude coincident outer endpoints.
DAG node: `topo.collinear_segments_meeting_only_at_joint_g19`. -/
theorem collinear_segments_meeting_only_at_joint
    {V : Type*} [AddCommGroup V] [Module ℝ V] (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hcol : Collinear ℝ ({a, b, c} : Set V))
    (hinter : segment ℝ a b ∩ segment ℝ b c ⊆ {b}) :
    b ∈ openSegment ℝ a c ∧ segment ℝ a b ∪ segment ℝ b c = segment ℝ a c := by
  have hbetween : Wbtw ℝ a b c := by
    rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h
    · exact (hbc (hinter ⟨h.symm.mem_segment, right_mem_segment ℝ b c⟩).symm).elim
    · exact (hab (hinter ⟨left_mem_segment ℝ a b, h.symm.mem_segment⟩)).elim
  have hb := hbetween.mem_segment
  refine ⟨mem_openSegment_of_ne_left_right hab hbc.symm hb, subset_antisymm ?_ ?_⟩
  · exact union_subset
      ((convex_segment a c).segment_subset (left_mem_segment ℝ a c) hb)
      ((convex_segment a c).segment_subset hb (right_mem_segment ℝ a c))
  · intro z hz
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · have hline : b ∈ range (AffineMap.lineMap a c : ℝ → V) := by
        rw [segment_eq_image_lineMap] at hb
        exact image_subset_range _ _ hb
      rcases openSegment_subset_union a c hline hz with rfl | hz | hz
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ a b hz)
      · exact Or.inr (openSegment_subset_segment ℝ b c hz)

end HolomorphicAnosov
