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
import HolomorphicAnosov.Analysis.Flow.JointDerivativeContDiffOn

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Teschl's finite-order successor step on the SAME open domain. The first
variation is an actual HasFDerivAt witness supplied by the proved C1 defect
argument; its components' higher regularity comes from the augmented-flow
induction. This lemma does not assume higher differentiability of α. -/
theorem finite_order_successor (D : Set (E × ℝ)) (hD : IsOpen D) (n : ℕ)
    (α : E × ℝ → E) (Y : E × ℝ → E →L[ℝ] E) (V : E × ℝ → E)
    (hfirst : ∀ p ∈ D, HasFDerivAt α (jointDerivative Y V p) p)
    (hY : ContDiffOn ℝ n Y D) (hV : ContDiffOn ℝ n V D) :
    ContDiffOn ℝ (n + 1) α D := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen hD).mpr
  refine ⟨fun p hp ↦ (hfirst p hp).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact (jointDerivative_contDiffOn D n Y V hY hV).congr
      (fun p hp ↦ (hfirst p hp).fderiv)

end SmoothFlowBootstrap
