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
import HolomorphicAnosov.Analysis.Flow.SmoothAtAllFiniteOrders

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite-order germs at every point yield C∞ on the SAME open original
solution domain. Each n may have its own local neighborhood; no countable
intersection or new positive common radius is asserted or required. -/
theorem smooth_on_of_all_finite_germs
    (D : Set (E × ℝ)) (α : E × ℝ → E)
    (hα : ∀ p ∈ D, ∀ n : ℕ, ContDiffAt ℝ n α p) : ContDiffOn ℝ ∞ α D := by
  intro p hp
  exact (smooth_at_of_all_finite_orders α p (hα p hp)).contDiffWithinAt

end SmoothFlowBootstrap
