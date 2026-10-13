import HolomorphicAnosov.Topology.EuclideanPositiveSimplex
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexCoordinateRecovery
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced

/-!
# The prescribed affine simplex is an embedded closed disk

Source: Hatcher, *Algebraic Topology*, pp.233–234 and ordered simplex convention
p.269. DAG node: `topo.euclidean_positive_simplex_embedding_g15`.
-/

noncomputable section
namespace HolomorphicAnosov

/-- The ordered affine map is a closed embedding.

The coordinate recovery formula makes it injective: equality of the image
coordinates gives equality of the first barycentric coordinate, then equality
of all successor coordinates. The standard simplex is compact and Euclidean
space is Hausdorff, so the continuous injective map is closed and therefore a
closed embedding. This is the concrete topological disk input in Hatcher's
local simplex comparison. -/
theorem euclideanPositiveSimplex_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (euclideanPositiveSimplex n) := by
  let σ := euclideanPositiveSimplex n
  have hinj : Function.Injective σ := by
    intro s t hst
    have hsum : (∑ j : Fin n, σ s j) = ∑ j : Fin n, σ t j := by
      rw [hst]
    have h0 : s.weights 0 = t.weights 0 := by
      rw [euclideanPositiveSimplex_coordinate_recovery n s,
        euclideanPositiveSimplex_coordinate_recovery n t, hsum]
    apply Convexity.StdSimplex.weights_inj.mp
    apply Finsupp.ext
    intro j
    refine Fin.cases h0 (fun j ↦ ?_) j
    have hj : (σ s).ofLp j = (σ t).ofLp j :=
      congrFun (congrArg (fun z => z.ofLp) hst) j
    have hsj : s.weights j.succ = t.weights j.succ := by
      dsimp [σ, euclideanPositiveSimplex] at hj
      linarith
    exact hsj
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    σ.continuous hinj σ.continuous.isClosedMap

end HolomorphicAnosov

