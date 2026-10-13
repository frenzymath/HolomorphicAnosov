import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Data.Fin.VecNotation

noncomputable section
open Convexity
universe u
namespace HolomorphicAnosov.Topology

/-- The ordered affine edge between two vertices of a standard simplex,
parametrized by the original unit interval. Source: Hatcher, Algebraic
Topology, ordered simplices pp.103–104 and Theorem 2A.1 proof p.167. Use the
standard interval-simplex homeomorphism, followed by the simplex map sending
the two endpoint vertices to the prescribed vertices. Repeated vertices give
the constant edge. -/
def stdSimplexEdgePath {ι : Type u} (a b : ι) :
    Path (StdSimplex.single a : StdSimplex ℝ ι) (StdSimplex.single b) where
  toFun t := (StdSimplex.homeomorphI.symm t).map ![a, b]
  continuous_toFun := (StdSimplex.continuous_map ℝ ![a, b]).comp
    StdSimplex.homeomorphI.symm.continuous
  source' := by simp
  target' := by simp

end HolomorphicAnosov.Topology
