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
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseSplitting
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverse_restricted_norm

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

attribute [local instance] complex_isManifold_real

/-- Invert Zhang's actual Anosov datum, retaining its metric and common iterate and exchanging
its given invariant continuous subbundles. The chain rule and exact inverse restriction identity
prove the two contraction fields; no new metric, subbundle or admitted proof is selected. -/
def inverseAnosovDatum {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (a : AnosovDatum f) : AnosovDatum f.symm where
  metric := a.metric
  splitting := inverseSplitting f.toReal a.splitting
  k := a.k
  one_le_k := a.one_le_k
  stable_contracting := by
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    intro x
    obtain ⟨y, rfl⟩ := (f.toReal.surjective.iterate a.k) x
    change ‖(restrictedIterateDerivative f.toReal.symm a.splitting.unstable.toDistribution
      (inverseSplitting f.toReal a.splitting).stable_map
      a.k (((f.toReal : X → X)^[a.k]) y)).toContinuousLinearMap‖ < 1
    rw [inverse_restricted_norm f.toReal _ a.splitting.unstable_map]
    exact a.unstable_contracting y
  unstable_contracting := by
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    intro x
    have hn := inverse_restricted_norm f.toReal.symm a.splitting.stable.toDistribution
      (inverseSplitting f.toReal a.splitting).unstable_map a.splitting.stable_map a.k x
    change ‖(restrictedIterateDerivative f.toReal.symm a.splitting.stable.toDistribution
      (inverseSplitting f.toReal a.splitting).unstable_map
      a.k x).symm.toContinuousLinearMap‖ < 1
    rw [← hn]
    exact a.stable_contracting (((f.toReal.symm : X → X)^[a.k]) x)


end
end HolomorphicAnosov.TheoremAProof
