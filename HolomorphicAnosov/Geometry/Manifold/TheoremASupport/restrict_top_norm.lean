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

theorem restrict_top_norm {E F : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
 (e : E ≃L[ℝ] F) (P : Submodule ℝ E) (Q : Submodule ℝ F)
 (h : P.map e.toLinearMap = Q) (hP : P = ⊤) :
 ‖(e.ofSubmodules P Q h).toContinuousLinearMap‖ = ‖e.toContinuousLinearMap‖ := by
 apply le_antisymm
 · apply ContinuousLinearMap.opNorm_le_bound (e.ofSubmodules P Q h).toContinuousLinearMap (norm_nonneg e.toContinuousLinearMap)
   intro v
   simpa only [ContinuousLinearEquiv.coe_coe, ← Submodule.norm_coe,
     ContinuousLinearEquiv.ofSubmodules_apply] using
       e.toContinuousLinearMap.le_opNorm (v : E)
 · apply ContinuousLinearMap.opNorm_le_bound e.toContinuousLinearMap (norm_nonneg (e.ofSubmodules P Q h).toContinuousLinearMap)
   intro v
   have hv : v ∈ P := by rw [hP]; exact Submodule.mem_top
   simpa only [ContinuousLinearEquiv.coe_coe, ← Submodule.norm_coe,
     ContinuousLinearEquiv.ofSubmodules_apply] using
       (e.ofSubmodules P Q h).toContinuousLinearMap.le_opNorm ⟨v,hv⟩


end
end HolomorphicAnosov.TheoremAProof.Dimension
