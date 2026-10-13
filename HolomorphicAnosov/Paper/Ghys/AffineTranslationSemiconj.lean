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

theorem affine_translation_semiconj {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) (b c : ComplexModel d) (hc : b = c - A.linear c) :
    Function.Semiconj (fun x : ComplexTorus L ↦ x - QuotientAddGroup.mk c)
      (quotientAffineEquiv A b) (quotientLinearEquiv A) := by
  intro x
  change quotientLinearEquiv A x + QuotientAddGroup.mk b - QuotientAddGroup.mk c =
    quotientLinearEquiv A (x - QuotientAddGroup.mk c)
  rw [(quotientLinearEquiv A).map_sub]
  have hAc : quotientLinearEquiv A (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (A.linear c) := by
    rfl
  rw [hAc, hc]
  simp only [QuotientAddGroup.mk_sub]
  abel

end HolomorphicAnosov
