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
import HolomorphicAnosov.Paper.Ghys.QuotientProjectionDerivative
import HolomorphicAnosov.Paper.Ghys.QuotientProjectionSmooth

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem torus_flat_frame_continuous {d : ℕ} (L : FullComplexLattice d) :
    Continuous (fun p : ComplexTorus L × ComplexModel d ↦
      (⟨p.1, p.2⟩ : TangentBundle (realModel d) (ComplexTorus L))) := by
  let : IsManifold (complexModel d) ∞ (ComplexTorus L) := complexTorus_isManifold L
  let : IsManifold (realModel d) ∞ (ComplexTorus L) := complex_isManifold_real d _
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  have hq : ContMDiff (realModel d) (realModel d) ∞ q :=
    contMDiff_complex_to_real (quotient_projection_smooth L)
  have ht : Continuous (fun p : ComplexModel d × ComplexModel d ↦
      (⟨q p.1, mfderiv (realModel d) (realModel d) q p.1 p.2⟩ :
        TangentBundle (realModel d) (ComplexTorus L))) := by
    exact (hq.continuous_tangentMap (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
      (tangentBundleModelSpaceHomeomorph (realModel d)).symm.continuous
  apply ((QuotientAddGroup.isOpenQuotientMap_mk.prodMap
    (IsOpenQuotientMap.id (X := ComplexModel d))).isQuotientMap.continuous_iff).mpr
  convert ht using 1
  funext p
  simp only [Function.comp_def, q, quotient_projection_derivative]
  rfl

end HolomorphicAnosov
