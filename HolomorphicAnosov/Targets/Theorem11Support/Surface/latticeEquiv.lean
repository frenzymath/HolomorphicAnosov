import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import Mathlib.Algebra.Module.Equiv.Basic

/-!
Restriction of a lattice-preserving complex-linear equivalence gives an integer-linear lattice automorphism.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW10

universe u

/-- The integer-linear automorphism obtained by restricting `B.linear` to `L.lattice`. -/
def latticeEquiv (L : FullComplexLattice 2) (B : LatticeLinearEquiv L) :
    L.lattice ≃ₗ[ℤ] L.lattice :=
  ((B.linear.toAddEquiv.addSubgroupMap L.lattice.toAddSubgroup).trans
    (AddEquiv.addSubgroupCongr B.map_lattice)).toIntLinearEquiv

end HolomorphicAnosov.Theorem11SupportW10

