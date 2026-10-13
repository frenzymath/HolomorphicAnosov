import HolomorphicAnosov.Geometry.IdealTriangleReflectionData
import HolomorphicAnosov.Geometry.IdealTriangleBoundary
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.LocallyFinite

noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- A one-step geometric side reflection is included in the finite reflection orbit. (Epstein–Petronio, Def. 2.1) -/
theorem reflectionStep_reachable (V W : Finset ℂ)
    (h : reflectionStep V W) : reachable V W := by
  exact Relation.ReflTransGen.single h

end HolomorphicAnosov.IdealDiskTriangle
