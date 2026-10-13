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
import HolomorphicAnosov.Analysis.Flow.AugmentedField

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The augmented field loses exactly one finite order. Its domain is the
original open state domain times ALL matrices; no global extension of F or
bounded-matrix hypothesis is made. -/
theorem augmentedField_contDiffOn (F : E → E) (Ω : Set E) (hΩ : IsOpen Ω)
    (n : ℕ) (hF : ContDiffOn ℝ (n + 1) F Ω) :
    ContDiffOn ℝ n (augmentedField F) (Ω ×ˢ (univ : Set (E →L[ℝ] E))) := by
  have hfst : ContDiffOn ℝ n (fun p : E × (E →L[ℝ] E) ↦ p.1)
      (Ω ×ˢ (univ : Set (E →L[ℝ] E))) := contDiffOn_fst
  have hFF := (hF.of_le (by simp)).comp hfst (fun _ hp ↦ hp.1)
  have hDF := (hF.fderiv_of_isOpen hΩ (m := n) (by simp)).comp hfst
    (fun _ hp ↦ hp.1)
  exact hFF.prodMk (hDF.clm_comp contDiffOn_snd)

end SmoothFlowBootstrap
