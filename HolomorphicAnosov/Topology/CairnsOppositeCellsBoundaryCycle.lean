import HolomorphicAnosov.Topology.PolygonSeamNormalization
import HolomorphicAnosov.Topology.PolygonCycleGluing

/-!
# Boundary cycle of two polygons sharing a segment

Source: Cairns (1951), preliminary §2(B), printed p.860. The source states the
boundary-arc gluing principle; the finite polygon construction is proved here.
DAG node: `topo.cairns_opposite_cells_boundary_cycle_g17`.

Subdivide each polygon at the two seam endpoints and remove redundant vertices in
the open seam. The normalization theorem preserves both boundaries and simplicity
and makes the seam the closing edge. Orient the first remaining arc from a to b
and the second from b to a. Concatenate their vertex lists, omitting the final
vertex in each list to retain each joining endpoint once. The gluing theorem gives
injectivity, common-endpoint edge intersections, and boundary equal to the union
of the original boundaries minus the open seam. The new cycle has at least four
vertices. Reindex its size as n+3; injectivity gives nondegenerate edges.

The proof uses only the exact boundary intersection, so no opposite-side or
complementary-region hypothesis is needed for this finite cycle construction.
-/

namespace HolomorphicAnosov
open Set

/-- Two finite simple polygon boundaries meeting exactly in a nondegenerate segment
give a finite simple polygon after deleting the open common segment. -/
theorem cairns_opposite_cells_boundary_cycle
    {n₁ n₂ : ℕ} (q₁ : Polygon ℂ (n₁ + 3)) (q₂ : Polygon ℂ (n₂ + 3))
    (hq₁_vertices : Function.Injective q₁.vertices)
    (_hq₁_edges : q₁.HasNondegenerateEdges)
    (hq₁_simple : ∀ i j : Fin (n₁ + 3), i ≠ j →
      q₁.edgeSet ℝ i ∩ q₁.edgeSet ℝ j =
        ({q₁ i, q₁ (finRotate (n₁ + 3) i)} : Set ℂ) ∩
        {q₁ j, q₁ (finRotate (n₁ + 3) j)})
    (hq₂_vertices : Function.Injective q₂.vertices)
    (_hq₂_edges : q₂.HasNondegenerateEdges)
    (hq₂_simple : ∀ i j : Fin (n₂ + 3), i ≠ j →
      q₂.edgeSet ℝ i ∩ q₂.edgeSet ℝ j =
        ({q₂ i, q₂ (finRotate (n₂ + 3) i)} : Set ℂ) ∩
        {q₂ j, q₂ (finRotate (n₂ + 3) j)})
    (a b : ℂ) (hab : a ≠ b)
    (hq_inter : q₁.boundary ℝ ∩ q₂.boundary ℝ = segment ℝ a b)
    :
    ∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
          ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
          {q j, q (finRotate (n + 3) j)}) ∧
      q.boundary ℝ = (q₁.boundary ℝ ∪ q₂.boundary ℝ) \ openSegment ℝ a b := by
  have hs₁ : PolygonCycleData q₁ := ⟨hq₁_vertices, fun i j hij ↦ (hq₁_simple i j hij).subset⟩
  have hs₂ : PolygonCycleData q₂ := ⟨hq₂_vertices, fun i j hij ↦ (hq₂_simple i j hij).subset⟩
  have hsub₁ : segment ℝ a b ⊆ q₁.boundary ℝ := by
    rw [← hq_inter]
    exact inter_subset_left
  have hsub₂ : segment ℝ b a ⊆ q₂.boundary ℝ := by
    rw [segment_symm ℝ b a, ← hq_inter]
    exact inter_subset_right
  obtain ⟨m₁, p₁, hp₁, hb₁, ha₁, hc₁⟩ := hs₁.standard_seam a b hab hsub₁
  obtain ⟨m₂, p₂, hp₂, hb₂, hb₀, hc₂⟩ := hs₂.standard_seam b a hab.symm hsub₂
  obtain ⟨p, hp, hpb⟩ := PolygonCycleData.glue_standard p₁ p₂ hp₁ hp₂ a b hab
    ha₁ hc₁ hb₀ hc₂ (by rw [hb₁, hb₂]; exact hq_inter)
  have hn : (m₁ + 2) + (m₂ + 2) = (m₁ + m₂ + 1) + 3 := by omega
  generalize heN : (m₁ + 2) + (m₂ + 2) = N at p hp hpb
  have heN' : N = (m₁ + m₂ + 1) + 3 := heN.symm.trans hn
  clear heN
  subst N
  refine ⟨m₁ + m₂ + 1, p, hp.injective, hp.nondegenerate, ?_, ?_⟩
  · intro i j hij
    apply subset_antisymm (hp.simple i j hij)
    intro z hz
    have hend (k) : ({p k, p (finRotate (m₁ + m₂ + 1 + 3) k)} : Set ℂ) ⊆
        p.edgeSet ℝ k := pair_subset (left_mem_affineSegment ℝ _ _) (right_mem_affineSegment ℝ _ _)
    exact ⟨hend i hz.1, hend j hz.2⟩
  · simpa only [hb₁, hb₂] using hpb


end HolomorphicAnosov
