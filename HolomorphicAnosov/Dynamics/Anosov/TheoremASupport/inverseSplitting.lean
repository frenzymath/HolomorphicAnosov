import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverse_derivative_left

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

attribute [local instance] complex_isManifold_real

def inverseSplitting (g : Diffeomorph I I X X ∞)
    (s : InvariantRealTangentSplitting g) : InvariantRealTangentSplitting g.symm where
  stable := s.unstable
  unstable := s.stable
  isCompl x := (s.isCompl x).symm
  stable_map := by
    intro x
    let P := s.unstable.toDistribution
    have hP := s.unstable_map
    have h := hP (g.symm x)
    rw [g.apply_symm_apply] at h
    rw [← h, ← Submodule.map_comp]
    have hi : (mfderiv I I g.symm x).comp (mfderiv I I g (g.symm x)) =
        ContinuousLinearMap.id ℝ (TangentSpace I (g.symm x)) := by
      have hi := inverse_derivative_left g (g.symm x)
      simp only [TangentSpace] at hi
      rw [g.apply_symm_apply] at hi
      exact hi
    rw [← ContinuousLinearMap.toLinearMap_comp, hi]
    exact Submodule.map_id _
  unstable_map := by
    intro x
    let P := s.stable.toDistribution
    have hP := s.stable_map
    have h := hP (g.symm x)
    rw [g.apply_symm_apply] at h
    rw [← h, ← Submodule.map_comp]
    have hi : (mfderiv I I g.symm x).comp (mfderiv I I g (g.symm x)) =
        ContinuousLinearMap.id ℝ (TangentSpace I (g.symm x)) := by
      have hi := inverse_derivative_left g (g.symm x)
      simp only [TangentSpace] at hi
      rw [g.apply_symm_apply] at hi
      exact hi
    rw [← ContinuousLinearMap.toLinearMap_comp, hi]
    exact Submodule.map_id _


end
end HolomorphicAnosov.TheoremAProof
