import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Group.Subgroup.Map
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.FullLattice

/-!
A lattice-preserving complex linear equivalence maps the lattice subgroup onto itself.
-/

namespace HolomorphicAnosov

structure LatticeLinearEquiv {d : ℕ} (L : FullComplexLattice d) where
  linear : ComplexModel d ≃ₗ[ℂ] ComplexModel d
  map_lattice : L.lattice.toAddSubgroup.map linear.toAddEquiv.toAddMonoidHom =
    L.lattice.toAddSubgroup

end HolomorphicAnosov
