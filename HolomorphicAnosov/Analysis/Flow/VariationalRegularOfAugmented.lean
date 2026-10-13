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

namespace SmoothFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine augmented C^n regularity transfers to the same α,Y pair by
pointwise IVP identification. This uses no independent differentiability
assumption on Y. The identity must hold on the actual shared open domain. -/
theorem variational_regular_of_augmented
    (D : Set (E × ℝ)) (n : ℕ) (Γ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (α : E × ℝ → E) (Y : E × ℝ → E →L[ℝ] E)
    (hΓ : ContDiffOn ℝ n Γ
      ((fun p : E × ℝ ↦ ((p.1, ContinuousLinearMap.id ℝ E), p.2)) '' D))
    (heq : ∀ p ∈ D, Γ ((p.1, ContinuousLinearMap.id ℝ E), p.2) = (α p, Y p)) :
    ContDiffOn ℝ n Y D := by
  have hi : ContDiffOn ℝ n
      (fun p : E × ℝ ↦ ((p.1, ContinuousLinearMap.id ℝ E), p.2)) D :=
    (contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd
  have hc := hΓ.comp hi (fun p hp ↦ ⟨p, hp, rfl⟩)
  exact hc.snd.congr (fun p hp ↦ (congrArg Prod.snd (heq p hp)).symm)

end SmoothFlowBootstrap
