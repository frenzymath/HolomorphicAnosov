import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace HolomorphicAnosov

/-!
# Endpoint intersections of simple polygon edges

The former statement omitted simplicity and was false: the complex quadrilateral
with consecutive vertices `0, 1 + I, I, 1` has injective vertices and nondegenerate
edges, but edges 0 and 2 meet at `(1 + I) / 2` without a common endpoint.
The corrected statement explicitly assumes the pairwise edge-intersection law.
-/

/-- For a simple polygon with injective vertices, every point common to distinct
edges is the image of a common endpoint index.

Source: the simple-polygon intersection convention used in Cairns (1951),
preliminary §2, pp.860–861. Rewrite the edge intersection by simplicity. A point
in both endpoint pairs has preimages in both index pairs; vertex injectivity
identifies those preimages, giving a member of the intersection of index pairs. -/
theorem Polygon.endpoint_inter_subset_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Polygon E n) (hinj : Function.Injective p.vertices)
    (_hnd : p.HasNondegenerateEdges)
    (hsimple : ∀ i j : Fin n, i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j =
        ({p i, p (finRotate n i)} : Set E) ∩ {p j, p (finRotate n j)})
    (i j : Fin n) (hij : i ≠ j) :
    p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
      p.vertices '' ({i, finRotate n i} ∩ {j, finRotate n j}) := by
  rw [hsimple i j hij, Set.image_inter hinj]
  simp only [Set.image_pair]
  exact Set.Subset.rfl

end HolomorphicAnosov

