import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Group.Quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.FullLattice

/-!
The complex torus is the additive quotient of the complex model by a full lattice.
-/

namespace HolomorphicAnosov

abbrev ComplexTorus {d : ℕ} (L : FullComplexLattice d) :=
  ComplexModel d ⧸ L.lattice.toAddSubgroup

end HolomorphicAnosov
