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
import HolomorphicAnosov.Analysis.Flow.FiniteOrderSuccessor
import HolomorphicAnosov.Analysis.Flow.VariationalRegularOfAugmented

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Combine the actual augmented trajectory's regularity with the original
solution's lower-order regularity. The unchanged original α is upgraded on
D. The identity heq is the conclusion of augmented_trajectory_eq when the
actual source and receiving domains and coefficient guards have been bound;
it is not inferred from an unguarded solution-set equality. -/
theorem successor_on_same_solution_of_augmented
    (D : Set (E × ℝ)) (hD : IsOpen D) (Ω : Set E) (n : ℕ) (F : E → E)
    (α : E × ℝ → E) (Y : E × ℝ → E →L[ℝ] E)
    (Γ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (hF : ContDiffOn ℝ n F Ω) (hα : ContDiffOn ℝ n α D)
    (hrange : ∀ p ∈ D, α p ∈ Ω)
    (hfirst : ∀ p ∈ D, HasFDerivAt α (jointDerivative Y (fun q ↦ F (α q)) p) p)
    (hΓ : ContDiffOn ℝ n Γ
      ((fun p : E × ℝ ↦ ((p.1, ContinuousLinearMap.id ℝ E), p.2)) '' D))
    (heq : ∀ p ∈ D, Γ ((p.1, ContinuousLinearMap.id ℝ E), p.2) = (α p, Y p)) :
    ContDiffOn ℝ (n + 1) α D := by
  exact finite_order_successor D hD n α Y (fun p ↦ F (α p)) hfirst
    (variational_regular_of_augmented D n Γ α Y hΓ heq)
    (hF.comp hα hrange)

end SmoothFlowBootstrap
