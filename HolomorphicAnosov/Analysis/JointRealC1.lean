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
import HolomorphicAnosov.Analysis.JointRealPartialDerivative

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.JointRealC1Scratch
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual jointly continuous spatial and time derivatives imply C¹ for the SAME
function on the SAME open rectangle. The product-partial kernel supplies its
Fréchet derivative at every point. The combined derivative is jointly continuous
because `toSpanSingletonLIE` and continuous-linear-map coproduct preserve
continuity. Mathlib's C¹ derivative criterion then applies to this actual open
domain. Empty rectangles and rank zero need no separate hypotheses. This is an
agent-written interface step following Mathlib, not a full flow-existence proof. -/
theorem joint_contDiffOn_one_of_partials
    (α : E → ℝ → F) (Y : E → ℝ → E →L[ℝ] F) (V : E → ℝ → F)
    (U : Set E) (I : Set ℝ) (hU : IsOpen U) (hI : IsOpen I)
    (hspace : ∀ x ∈ U, ∀ t ∈ I, HasFDerivAt (fun q ↦ α q t) (Y x t) x)
    (htime : ∀ x ∈ U, ∀ t ∈ I, HasDerivAt (α x) (V x t) t)
    (hY : ContinuousOn (fun p : E × ℝ ↦ Y p.1 p.2) (U ×ˢ I))
    (hV : ContinuousOn (fun p : E × ℝ ↦ V p.1 p.2) (U ×ˢ I)) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ α p.1 p.2) (U ×ˢ I) := by
  have hD := joint_hasFDerivAt_of_partials α Y V U I hU hI hspace htime hY hV
  have hcontinuous : ContinuousOn
      (fun p : E × ℝ ↦ (Y p.1 p.2).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (V p.1 p.2))) (U ×ˢ I) :=
    hY.continuousLinearMapCoprod
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp_continuousOn hV)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hU.prod hI).uniqueDiffOn]
  refine ⟨by simp, _, contDiffOn_zero.mpr hcontinuous, ?_⟩
  exact fun p hp ↦ (hD p hp).hasFDerivWithinAt

end HolomorphicAnosov.JointRealC1Scratch
