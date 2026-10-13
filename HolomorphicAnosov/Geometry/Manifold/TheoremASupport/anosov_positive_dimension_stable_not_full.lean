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
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.smoothMetric_full_contraction_subsingleton
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.native_stable_full_strict
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.positive_complex_dimension_not_subsingleton_support

namespace HolomorphicAnosov.TheoremAProof.Dimension
open Set Filter Manifold Bundle HolomorphicAnosov
open scoped Bundle ContDiff Manifold _root_.Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [ProperSpace E]
open MeasureTheory
open scoped ENNReal
attribute [local instance] complex_isManifold_real
universe u
set_option maxHeartbeats 800000

/-- The original metric and common iterate exclude a full stable fibre in positive dimension. -/
theorem anosov_positive_dimension_stable_not_full
    {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X] (hd : 0 < d)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (htop : ∀ x, a.splitting.stable.toDistribution x = ⊤) : False := by
  have hstrict :
      let : Bundle.RiemannianBundle
          (fun x : X ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      ∀ x, ‖mfderiv (realModel d) (realModel d)
        ((f.toReal : X → X)^[a.k]) x‖ < 1 :=
    fun x ↦ native_stable_full_strict f a x (htop x)
  have hsub : Subsingleton X :=
    smoothMetric_full_contraction_subsingleton a.metric
      ((f.toReal : X → X)^[a.k])
      ((f.toReal.contMDiff.iterate a.k).of_le (by simp))
      (f.toReal.surjective.iterate a.k) hstrict
  exact positive_complex_dimension_not_subsingleton_support hd hsub


end
end HolomorphicAnosov.TheoremAProof.Dimension
