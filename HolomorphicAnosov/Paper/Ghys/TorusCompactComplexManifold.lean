import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.TorusCompact

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_compact_complex_manifold {d : ℕ} (L : FullComplexLattice d) :
    IsCompactComplexManifold d (ComplexTorus L) := by
  let : DiscreteTopology L.lattice := L.discrete
  let : IsClosed (L.lattice.toAddSubgroup : Set (ComplexModel d)) :=
    AddSubgroup.isClosed_of_discreteTopology
  let : CompactSpace (ComplexTorus L) := torus_compact L
  let : IsManifold (complexModel d) ∞ (ComplexTorus L) := complexTorus_isManifold L
  let : ConnectedSpace (ComplexTorus L) :=
    (torus_quotient_covering L).surjective.connectedSpace QuotientAddGroup.continuous_mk
  exact IsCompactComplexManifold.mk

end HolomorphicAnosov
