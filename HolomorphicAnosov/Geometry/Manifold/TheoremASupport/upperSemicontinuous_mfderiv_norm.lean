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
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.eventually_speed_bound

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

theorem upperSemicontinuous_mfderiv_norm
    (F : M → M) (hF : ContMDiff I I 1 F) :
    UpperSemicontinuous (fun x : M ↦ ‖mfderiv I I F x‖) := by
  intro x
  change UpperSemicontinuousAt (fun y : M ↦ ‖mfderiv I I F y‖) x
  rw [upperSemicontinuousAt_iff]
  intro q hq
  obtain ⟨q', h1, h2⟩ := exists_between hq
  filter_upwards [eventually_speed_bound F hF x q' h1] with y hy
  exact ((mfderiv I I F y).opNorm_le_bound ((norm_nonneg (mfderiv I I F x)).trans h1.le) hy).trans_lt h2


end
end HolomorphicAnosov.TheoremAProof.Dimension
