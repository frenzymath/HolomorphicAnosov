import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.Flow.JointDerivative

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Regularity of the two actual derivative components yields regularity of
the joint continuous-linear derivative. -/
theorem jointDerivative_contDiffOn (D : Set (E × ℝ)) (n : ℕ)
    (Y : E × ℝ → E →L[ℝ] E) (V : E × ℝ → E)
    (hY : ContDiffOn ℝ n Y D) (hV : ContDiffOn ℝ n V D) :
    ContDiffOn ℝ n (jointDerivative Y V) D := by
  exact (hY.clm_comp contDiffOn_const).add
    ((contDiffOn_const.smulRight hV).clm_comp contDiffOn_const)

end SmoothFlowBootstrap
