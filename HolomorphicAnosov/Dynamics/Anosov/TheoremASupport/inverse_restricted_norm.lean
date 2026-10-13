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
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverse_derivative_apply

namespace HolomorphicAnosov.TheoremAProof
open scoped ContDiff Bundle
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

attribute [local instance] complex_isManifold_real

omit [IsManifold I ∞ X] in
lemma inverse_restricted_norm (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (hPinv : ∀ x, (P x).map (mfderiv I I g.symm x).toLinearMap = P (g.symm x))
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)] (n : ℕ) (x : X) :
    ‖(restrictedIterateDerivative g.symm P hPinv
      n (((g : X → X)^[n]) x)).toContinuousLinearMap‖ =
    ‖(restrictedIterateDerivative g P hP n x).symm.toContinuousLinearMap‖ := by
  simp only [ContinuousLinearMap.norm_def]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro v
  apply iff_of_eq
  apply congrArg (fun r : ℝ ↦ r ≤ c * ‖v‖)
  unfold restrictedIterateDerivative
  change ‖((realIterate I g.symm n).mfderivToContinuousLinearEquiv (by simp)
    (((g : X → X)^[n]) x)) (v : TangentSpace I (((g : X → X)^[n]) x))‖ =
    ‖((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).symm
      (v : TangentSpace I (((g : X → X)^[n]) x))‖
  change ‖mfderiv I I (realIterate I g.symm n) (((g : X → X)^[n]) x) ↑v‖ =
    ‖((realIterate I g n).mfderivToContinuousLinearEquiv (by simp) x).symm
      (show TangentSpace I ((realIterate I g n) x) from (show E from v.val))‖
  have hv := inverse_derivative_apply (realIterate I g n) x
    (show TangentSpace I ((realIterate I g n) x) from (show E from v.val))
  erw [hv]
  have hx : realIterate I g.symm n (((g : X → X)^[n]) x) = x :=
    g.left_inv.iterate n x
  erw [hx]



end
end HolomorphicAnosov.TheoremAProof
