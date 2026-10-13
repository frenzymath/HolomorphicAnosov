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
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.upperSemicontinuous_mfderiv_norm

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

theorem uniform_speed_bound_of_pointwise
    [CompactSpace M] [Nonempty M]
    (F : M → M) (hF : ContMDiff I I 1 F)
    (hstrict : ∀ x, ‖mfderiv I I F x‖ < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ x (v : TangentSpace I x), ‖mfderiv I I F x v‖ ≤ q * ‖v‖ := by
  obtain ⟨x, _, hx⟩ := ((upperSemicontinuous_mfderiv_norm F hF).upperSemicontinuousOn Set.univ).exists_isMaxOn Set.univ_nonempty isCompact_univ
  refine ⟨(‖mfderiv I I F x‖ + 1) / 2, ?_, ?_, ?_⟩
  · have := norm_nonneg (mfderiv I I F x); linarith
  · have := hstrict x; linarith
  · intro y v
    have hy : ‖mfderiv I I F y‖ ≤ ‖mfderiv I I F x‖ := hx (mem_univ y)
    have hq : ‖mfderiv I I F y‖ ≤ (‖mfderiv I I F x‖ + 1) / 2 := by
      have := hstrict x; linarith
    exact (mfderiv I I F y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hq (norm_nonneg v))


end
end HolomorphicAnosov.TheoremAProof.Dimension
