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
import HolomorphicAnosov.Paper.Ghys.QuotientTranslationSmooth

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

noncomputable def quotientTranslation {d : ℕ} (L : FullComplexLattice d)
    (c : ComplexModel d) : Biholomorph d d (ComplexTorus L) (ComplexTorus L) where
  toEquiv := Equiv.addRight (- (QuotientAddGroup.mk c : ComplexTorus L))
  contMDiff_toFun := by
    simpa [sub_eq_add_neg] using quotient_translation_smooth L c
  contMDiff_invFun := by
    simpa [Equiv.addRight, sub_eq_add_neg] using quotient_translation_smooth L (-c)

end HolomorphicAnosov
