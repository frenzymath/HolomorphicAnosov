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
import HolomorphicAnosov.Paper.Ghys.QuotientChartDerivative

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem quotient_projection_derivative {d : ℕ} (L : FullComplexLattice d)
    (z : ComplexModel d) :
    mfderiv (realModel d) (realModel d)
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) z =
      ContinuousLinearMap.id ℝ (ComplexModel d) := by
  apply HasMFDerivAt.mfderiv
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have h := quotient_chart_derivative L
    (chartAt (ComplexModel d) (QuotientAddGroup.mk z : ComplexTorus L))
    (chart_mem_atlas _ _) z (mem_chart_source _ _)
  have hid : ((tangentSpaceCastModel (realModel d)
      (QuotientAddGroup.mk z : ComplexTorus L)).toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ (ComplexModel d)).comp
        (tangentSpaceCastModel (realModel d) z).symm.toContinuousLinearMap)) =
      ContinuousLinearMap.id ℝ (ComplexModel d) := by ext v; rfl
  rw [hid]
  simpa [writtenInExtChartAt, extChartAt, realModel, Function.comp_def]
    using h.hasFDerivWithinAt (s := Set.univ)

end HolomorphicAnosov
