import Mathlib.Geometry.Polygon.Basic
import Mathlib.Basic.Real.Basic

/-!
# Exact polygon edge intersections from the simplicity bound

Source context: Cairns, An Elementary Proof of the Jordan-Schoenflies Theorem
(1951), Theorem 2.1, pp.860–861. The endpoint-set conversion below is an
agent-written elementary detail of the finite polygon amalgamation interface.
-/

open Set

namespace Polygon

/-- If the intersection of two closed polygon edges contains only their common
indexed vertices, it is exactly the intersection of their endpoint sets.
Source context: Cairns (1951), Theorem 2.1, pp.860–861.

For the forward inclusion, a common indexed vertex is an endpoint of both
edges. Conversely each point common to the two endpoint sets lies in both
closed segments. This uses neither injectivity of the vertex list nor
distinctness of the edges, and includes degenerate segments. -/
theorem edgeSet_inter_eq_of_subset_common_vertices
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (p : Polygon V n) (i j : Fin n)
    (h : p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
      p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j})) :
    p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
      ({p i, p (finRotate n i)} : Set V) ∩ {p j, p (finRotate n j)} := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨k, ⟨hki, hkj⟩, rfl⟩ := h hx
    simp only [mem_insert_iff, mem_singleton_iff] at hki hkj ⊢
    constructor
    · exact hki.elim (fun hki ↦ Or.inl (congrArg p hki))
        (fun hki ↦ Or.inr (congrArg p hki))
    · exact hkj.elim (fun hkj ↦ Or.inl (congrArg p hkj))
        (fun hkj ↦ Or.inr (congrArg p hkj))
  · rintro x ⟨hi, hj⟩
    have hend (k : Fin n) : ({p k, p (finRotate n k)} : Set V) ⊆ p.edgeSet ℝ k :=
      pair_subset (left_mem_affineSegment ℝ _ _) (right_mem_affineSegment ℝ _ _)
    exact ⟨hend i hi, hend j hj⟩

end Polygon

