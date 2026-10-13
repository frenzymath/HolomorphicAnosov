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

/-- Identify the augmented trajectory with the SAME original α and matrix
first variation Y. Primal uniqueness is restricted to the actual common
carrier B. Matrix uniqueness is applied vectorwise using the genuine
coefficient bound along α; no global Lipschitz augmented field is assumed. -/
theorem augmented_trajectory_eq
    (F : E → E) (B : Set E) (a b : ℝ) (K L : NNReal)
    (ha : (0 : ℝ) ∈ Ioo a b)
    (hF : LipschitzOnWith K F B)
    (α : ℝ → E) (Y : ℝ → E →L[ℝ] E)
    (Γ : ℝ → E × (E →L[ℝ] E))
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (F (α t)) t ∧ α t ∈ B)
    (hΓ : ∀ t ∈ Ioo a b, HasDerivAt Γ (augmentedField F (Γ t)) t ∧ (Γ t).1 ∈ B)
    (hY : ∀ t ∈ Ioo a b,
      HasDerivAt Y ((fderiv ℝ F (α t)).comp (Y t)) t)
    (hbound : ∀ t ∈ Ioo a b, ‖fderiv ℝ F (α t)‖ ≤ L)
    (hinit : Γ 0 = (α 0, Y 0)) :
    EqOn Γ (fun t ↦ (α t, Y t)) (Ioo a b) := by
  have hq : EqOn (fun t ↦ (Γ t).1) α (Ioo a b) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ ↦ F) (s := fun _ ↦ B) (K := K)
      (fun _ _ ↦ hF) ha
    · intro t ht
      exact ⟨by
        simpa [augmentedField] using
          (hΓ t ht).1.hasFDerivAt.fst.hasDerivAt, (hΓ t ht).2⟩
    · exact hα
    · exact congrArg Prod.fst hinit
  have hZ : ∀ t ∈ Ioo a b, (Γ t).2 = Y t := by
    intro t ht
    ext v
    have huniq := ODE_solution_unique_of_mem_Ioo
      (v := fun s (w : E) ↦ fderiv ℝ F (α s) w)
      (s := fun _ ↦ (univ : Set E)) (K := L)
      (f := fun s ↦ (Γ s).2 v) (g := fun s ↦ Y s v)
      (fun s hs ↦ ((fderiv ℝ F (α s)).lipschitzWith.weaken
        (hbound s hs)).lipschitzOnWith) ha
      (fun s hs ↦ ⟨by
        have hz : HasDerivAt (fun t ↦ (Γ t).2)
            ((fderiv ℝ F (Γ s).1).comp (Γ s).2) s := by
          simpa [augmentedField] using
            (hΓ s hs).1.hasFDerivAt.snd.hasDerivAt
        have hd := hz.clm_apply (hasDerivAt_const s v)
        simpa only [augmentedField, ContinuousLinearMap.comp_apply, map_zero, add_zero, hq hs] using hd,
        mem_univ _⟩)
      (fun s hs ↦ ⟨by
        simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
          (hY s hs).clm_apply (hasDerivAt_const s v), mem_univ _⟩)
      (congrArg (fun p : E × (E →L[ℝ] E) ↦ p.2 v) hinit)
    exact huniq ht
  intro t ht
  exact Prod.ext (hq ht) (hZ t ht)

end SmoothFlowBootstrap
