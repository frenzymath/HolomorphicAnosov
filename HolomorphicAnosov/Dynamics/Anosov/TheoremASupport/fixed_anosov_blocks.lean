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
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.mfderiv_iterate_fixed
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.fixed_restriction_norm
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.fixed_restriction_inverse_norm

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

attribute [local instance] complex_isManifold_real

theorem fixed_anosov_blocks {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (a : AnosovDatum f) (x : X) (hx : f x = x) :
    let : Bundle.RiemannianBundle (fun y : X ↦ TangentSpace (realModel d) y) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ (T : TangentSpace (realModel d) x ≃L[ℝ] TangentSpace (realModel d) x)
      (TS : ↥(a.splitting.stable.toDistribution x) ≃L[ℝ]
        ↥(a.splitting.stable.toDistribution x))
      (TU : ↥(a.splitting.unstable.toDistribution x) ≃L[ℝ]
        ↥(a.splitting.unstable.toDistribution x)),
      IsCompl (a.splitting.stable.toDistribution x) (a.splitting.unstable.toDistribution x) ∧
      (a.splitting.stable.toDistribution x).map T.toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x ∧
      (a.splitting.unstable.toDistribution x).map T.toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x ∧
      (∀ v, (TS v : TangentSpace (realModel d) x) = T v) ∧
      (∀ v, (TU v : TangentSpace (realModel d) x) = T v) ∧
      ‖TS.toContinuousLinearMap‖ < 1 ∧ ‖TU.symm.toContinuousLinearMap‖ < 1 ∧
      T.toContinuousLinearMap =
        (show TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) x from
          mfderiv (realModel d) (realModel d) f.toReal x) ^ a.k := by
  let : Bundle.RiemannianBundle (fun y : X ↦ TangentSpace (realModel d) y) :=
    ⟨a.metric.toRiemannianMetric⟩
  have hk : ((f.toReal : X → X)^[a.k]) x = x := Function.iterate_fixed hx a.k
  let T : TangentSpace (realModel d) x ≃L[ℝ] TangentSpace (realModel d) x :=
    (realIterate (realModel d) f.toReal a.k).mfderivToContinuousLinearEquiv (by simp) x
  have hS : (a.splitting.stable.toDistribution x).map T.toLinearEquiv.toLinearMap =
      a.splitting.stable.toDistribution x := by
    have h := real_distribution_iterate_invariant f.toReal _ a.splitting.stable_map a.k x
    erw [hk] at h
    exact h
  have hU : (a.splitting.unstable.toDistribution x).map T.toLinearEquiv.toLinearMap =
      a.splitting.unstable.toDistribution x := by
    have h := real_distribution_iterate_invariant f.toReal _ a.splitting.unstable_map a.k x
    erw [hk] at h
    exact h
  let TS := T.ofSubmodules _ _ hS
  let TU := T.ofSubmodules _ _ hU
  refine ⟨T, TS, TU, a.splitting.isCompl x, hS, hU, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; rfl
  · intro v; rfl
  · have h := a.stable_contracting x
    rw [← fixed_restriction_norm f.toReal _ a.splitting.stable_map a.k x hk hS] at h
    exact h
  · have h := a.unstable_contracting x
    rw [← fixed_restriction_inverse_norm f.toReal _ a.splitting.unstable_map a.k x hk hU] at h
    exact h
  · exact mfderiv_iterate_fixed f.toReal x hx a.k



end
end HolomorphicAnosov.TheoremAProof
