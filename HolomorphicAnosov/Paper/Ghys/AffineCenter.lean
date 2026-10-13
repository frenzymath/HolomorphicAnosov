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

theorem affine_center {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (h1 : ¬ Module.End.HasEigenvalue A.linear.toLinearMap 1) :
    ∃ c : ComplexModel d, b = c - A.linear c := by
  have hinj : Function.Injective ((LinearMap.id : ComplexModel d →ₗ[ℂ] ComplexModel d) - A.linear.toLinearMap) := by
    rw [← LinearMap.ker_eq_bot]
    apply eq_bot_iff.mpr
    intro v hv
    by_contra hv0
    apply h1
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by
        have he := LinearMap.mem_ker.mp hv
        change v - A.linear v = 0 at he
        simpa using (sub_eq_zero.mp he).symm), hv0⟩
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) b
  exact ⟨c, hc.symm⟩

end HolomorphicAnosov
