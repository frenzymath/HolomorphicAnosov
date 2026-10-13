import HolomorphicAnosov.Topology.EuclideanPositiveSimplex
import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Faces of the prescribed local simplex avoid the origin

Source: Hatcher, *Algebraic Topology*, pp.233–234 and p.269. DAG node:
`topo.euclidean_positive_simplex_face_avoids_zero_g15`.
-/

noncomputable section
namespace HolomorphicAnosov

/-- Every codimension-one face of the prescribed `(n+1)`-simplex avoids zero.

If a face image were zero, all barycentric weights would equal the first
weight. The omitted vertex has weight zero, forcing every weight to vanish,
contradicting the standard simplex total-one condition. This is the concrete
face condition used to send the boundary into the punctured subspace. -/
theorem euclideanPositiveSimplex_face_avoids_zero (n : ℕ)
    (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    euclideanPositiveSimplex (n + 1)
      (Convexity.StdSimplex.map i.succAbove t) ≠ 0 := by
  intro hz
  let u := Convexity.StdSimplex.map i.succAbove t
  have hconstant (j : Fin (n + 2)) : u.weights j = u.weights 0 := by
    refine Fin.cases rfl (fun k ↦ ?_) j
    have hk := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x k) hz
    exact sub_eq_zero.mp hk
  have hi : u.weights i = 0 := by
    dsimp only [u]
    rw [Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  apply Convexity.StdSimplex.weights_ne_zero u
  ext j
  exact (hconstant j).trans ((hconstant i).symm.trans hi)

end HolomorphicAnosov

