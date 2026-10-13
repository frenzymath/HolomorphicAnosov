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

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_compact {d : ℕ} (L : FullComplexLattice d) :
    CompactSpace (ComplexTorus L) := by
  let : DiscreteTopology L.lattice := L.discrete
  let : IsZLattice ℝ L.lattice := L.full
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice
    (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      simp only [QuotientAddGroup.mk_add]
      have hw' : (QuotientAddGroup.mk w : ComplexTorus L) = 0 :=
        by
          change (QuotientAddGroup.mk w : ComplexTorus L) = QuotientAddGroup.mk 0
          exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hw)
      rw [hw', add_zero])
  simpa only [(torus_quotient_covering L).surjective.range_eq] using hc

end HolomorphicAnosov
