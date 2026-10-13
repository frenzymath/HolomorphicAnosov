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
import HolomorphicAnosov.Paper.Ghys.QuotientAffineEquiv

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_chart_inverse {d : ℕ} (L : FullComplexLattice d)
    (e : OpenPartialHomeomorph (ComplexTorus L) (ComplexModel d))
    (he : e ∈ atlas (ComplexModel d) (ComplexTorus L)) :
    (e.symm : ComplexModel d → ComplexTorus L) = QuotientAddGroup.mk := by
  change ∃ x : ComplexTorus L,
    ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
      ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
      (OpenPartialHomeomorph.refl (ComplexModel d)) = e at he
  obtain ⟨x, rfl⟩ := he
  simp

end HolomorphicAnosov
