import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Topology.Covering.Quotient

/-!
The projection onto the quotient by a full complex lattice is an additive quotient covering map.
(Zhang, Thm 1.2, pp. 11–13)
-/

namespace HolomorphicAnosov

/-- The lattice quotient projection is an additive quotient covering map. (Zhang, Thm 1.2, pp.
11–13) -/
theorem torus_quotient_covering {d : ℕ} (L : FullComplexLattice d) :
    IsAddQuotientCoveringMap
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) L.lattice.toAddSubgroup := by
  have : DiscreteTopology L.lattice := L.discrete
  exact AddSubgroup.isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

end HolomorphicAnosov
