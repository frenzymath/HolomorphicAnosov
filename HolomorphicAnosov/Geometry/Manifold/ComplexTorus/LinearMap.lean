import Mathlib.Topology.Algebra.Group.Quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient

/-!
A lattice-preserving complex linear equivalence induces an additive automorphism of the complex
torus quotient.
-/

namespace HolomorphicAnosov

def quotientLinearEquiv {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) : ComplexTorus L ≃+ ComplexTorus L :=
  QuotientAddGroup.congr L.lattice.toAddSubgroup L.lattice.toAddSubgroup
    A.linear.toAddEquiv A.map_lattice

end HolomorphicAnosov
