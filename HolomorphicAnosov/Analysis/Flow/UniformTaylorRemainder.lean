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
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform first-order Taylor remainder on a compact convex buffer. The derivative is the
actual Fréchet derivative of the field, not an assumed approximation operator. -/
theorem uniform_taylor_remainder
    (F : E → E) (B : Set E) (hB : IsCompact B) (hconv : Convex ℝ B)
    (hdiff : ∀ q ∈ B, DifferentiableAt ℝ F q)
    (hDF : ContinuousOn (fderiv ℝ F) B) :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ B, ∀ r ∈ B, dist r q < δ →
      ‖F r - F q - fderiv ℝ F q (r - q)‖ ≤ ε * ‖r - q‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hB.uniformContinuousOn_of_continuous hDF) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro q hq r hr hdist
  have hseg : segment ℝ q r ⊆ B := hconv.segment_subset hq hr
  have hball : segment ℝ q r ⊆ Metric.ball q δ :=
    (convex_ball q δ).segment_subset (by simpa using hδ) hdist
  apply (convex_segment q r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ hdiff z (hseg hz)) _ (left_mem_segment ℝ q r) (right_mem_segment ℝ q r)
  intro z hz
  exact le_of_lt (by simpa only [dist_eq_norm] using
    (hclose z (hseg hz) q hq (hball hz)))

end FirstVariationalDefect
