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

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.SmoothLocalFlowProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- First variational operators are bijective at every actual trajectory
time. Compare their two vector trajectories from the common endpoint and
evaluate at time zero. This uses neither surjectivity of a nonlinear time
slice nor existence of its inverse, and includes the zero-dimensional case. -/
theorem variational_operator_bijective
    {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (A Y : ℝ → E →L[ℝ] E) (K : NNReal)
    (hA : ∀ t ∈ Ioo a b, ‖A t‖ ≤ K)
    (hY : ∀ t ∈ Ioo a b, HasDerivAt Y ((A t).comp (Y t)) t)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ E)
    {t : ℝ} (ht : t ∈ Ioo a b) : Function.Bijective (Y t) := by
  have hinj : Function.Injective (Y t) := by
    intro v w heq
    have hd (v : E) (s : ℝ) (hs : s ∈ Ioo a b) :
        HasDerivAt (fun q ↦ Y q v) (A s (Y s v)) s := by
      simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
        (hY s hs).clm_apply (hasDerivAt_const s v)
    have h := ODE_solution_unique_of_mem_Ioo
      (v := fun s (v : E) ↦ A s v) (s := fun _ ↦ (univ : Set E)) (K := K)
      (fun s hs ↦ ((A s).lipschitzWith.weaken (hA s hs)).lipschitzOnWith)
      ht (fun s hs ↦ ⟨hd v s hs, mem_univ _⟩)
      (fun s hs ↦ ⟨hd w s hs, mem_univ _⟩) heq
    simpa [hY0] using h h0
  exact ⟨hinj, (Y t).toLinearMap.surjective_of_injective hinj⟩

end HolomorphicAnosov.SmoothLocalFlowProof
