import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction
import HolomorphicAnosov.Topology.LoopSingularClassRefl

namespace HolomorphicAnosov.Topology
universe u
/-- The degree-one Hurewicz quotient function sends the group identity to zero.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.166. The identity is represented
by the constant based loop. The quotient lift evaluates to its singular class,
which vanishes because the constant triangle bounds the constant loop. -/
theorem degreeOneHurewiczFunction_one {X : Type u} [TopologicalSpace X] (x : X) :
    degreeOneHurewiczFunction x 1 = 0 := by
  exact loopSingularClass_refl x
end HolomorphicAnosov.Topology
