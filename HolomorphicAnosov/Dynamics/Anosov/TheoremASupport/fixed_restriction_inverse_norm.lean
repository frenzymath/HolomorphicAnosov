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

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

attribute [local instance] complex_isManifold_real

theorem fixed_restriction_inverse_norm (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ y, (P y).map (mfderiv I I g y).toLinearMap = P (g y))
    [Bundle.RiemannianBundle (fun y : X ↦ TangentSpace I y)]
    (n : ℕ) (x : X) (hn : ((g : X → X)^[n]) x = x)
    (hfixed : (P x).map
      ((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.toLinearMap
      = P x) :
    let T : TangentSpace I x ≃L[ℝ] TangentSpace I x :=
      (realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x
    ‖(T.ofSubmodules (P x) (P x) hfixed).symm.toContinuousLinearMap‖ =
    ‖(restrictedIterateDerivative g P hP n x).symm.toContinuousLinearMap‖ := by
  simp only [ContinuousLinearMap.norm_def]
  apply congrArg sInf
  ext c
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  simp only [Subtype.forall]
  apply forall_congr'
  intro v
  have hp : P (((g : X → X)^[n]) x) = P x := by erw [hn]
  simp only [hp]
  apply forall_congr'
  intro hv
  unfold restrictedIterateDerivative
  apply iff_of_eq
  apply congrArg (fun r : ℝ ↦ ‖((realIterate I g n).mfderivToContinuousLinearEquiv
    (by simp) x).symm v‖ ≤ c * r)
  have hnorm : @Norm.norm (TangentSpace I x) inferInstance =
      @Norm.norm (TangentSpace I (((g : X → X)^[n]) x)) inferInstance := by
    erw [hn]
  exact congrFun hnorm v


end
end HolomorphicAnosov.TheoremAProof
