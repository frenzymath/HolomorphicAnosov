import HolomorphicAnosov.Topology.BarycentricIteratedMesh
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The affine-origin hull used for Hatcher, Algebraic Topology, Proposition 2.21(1),
pp.119–121, agrees with the ordinary convex hull in Euclidean coordinates. -/

open Set

namespace HolomorphicAnosov.BarycentricGeometry

/-- Translating the convex hull of vertex differences back by the chosen origin
recovers the convex hull of the original vertices. This is the coordinate form
of the affine hull convention used in Hatcher, Proposition 2.21(1), pp.119–121. -/
theorem barycentricMesh_hull_eq_convexHull_range {n : ℕ}
    (w : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) :
    BarycentricMesh.hull w = convexHull ℝ (Set.range w) := by
  unfold BarycentricMesh.hull
  change (AffineEquiv.vaddConst ℝ (w 0)).toAffineMap ''
      convexHull ℝ (Set.range (fun i ↦ w i -ᵥ w 0)) = convexHull ℝ (Set.range w)
  rw [(AffineEquiv.vaddConst ℝ (w 0)).toAffineMap.image_convexHull]
  rw [← Set.range_comp]
  congr 1
  ext i
  simp [Function.comp]

end HolomorphicAnosov.BarycentricGeometry
