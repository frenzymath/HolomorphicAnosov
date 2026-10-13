import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterTaylorRemainder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Local uniform parameter Taylor remainders

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69, the compact uniform Taylor remainder in equation (6.8).

DAG node: `analysis.distribution_fixed_support_local_parameter_taylor_remainder_g10`.
-/

noncomputable section
open Set Metric
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- Jointly smooth parameter families have a uniform first-order Taylor remainder on a
small closed parameter ball and any fixed compact spatial set.

Choose a positive closed ball contained in the open parameter domain. Properness makes
that ball compact. The parameter derivative depends smoothly, hence continuously, on
both variables by the parameter-dependent derivative theorem. Applying the compact
uniform Taylor estimate on the convex ball gives the conclusion. The spatial domain
need not be open. Empty spatial supports and zero-dimensional parameter spaces are
allowed; the parameter base point must belong to the open domain. -/
theorem local_parameter_taylor_remainder
    {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Set E) (U : Set X) (hP : IsOpen P)
    (H : E → X → F) (hH : ContDiffOn ℝ ∞ (Function.uncurry H) (P ×ˢ U))
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (p : E) (hp : p ∈ P) :
    ∃ ρ > 0, closedBall p ρ ⊆ P ∧
      ∀ ε > 0, ∃ δ > 0, ∀ q ∈ closedBall p ρ, ∀ r ∈ closedBall p ρ,
        ∀ y ∈ K, dist r q < δ →
        ‖H r y - H q y - fderiv ℝ (fun t ↦ H t y) q (r - q)‖ ≤ ε * ‖r - q‖ := by
  have hwithin : ContDiffOn ℝ ∞
      (fun z : E × X ↦ fderivWithin ℝ (fun q ↦ H q z.2) P z.1) (P ×ˢ U) := by
    intro z hz
    have hf : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun z : E × X ↦ fun q ↦ H q z.2))
        ((P ×ˢ U) ×ˢ P) (z, z.1) := by
      have hg : ContDiff ℝ ∞ (fun w : (E × X) × E ↦ (w.2, w.1.2)) :=
        contDiff_snd.prodMk contDiff_fst.snd
      exact (hH.comp hg.contDiffOn (fun w hw ↦ ⟨hw.2, hw.1.2⟩))
        (z, z.1) ⟨hz, hz.1⟩
    exact hf.fderivWithin (m := ∞) contDiffWithinAt_fst hP.uniqueDiffOn
      (by simp) hz (fun w hw ↦ hw.1)
  have hA : ContinuousOn
      (fun z : E × X ↦ fderiv ℝ (fun q ↦ H q z.2) z.1) (P ×ˢ U) := by
    apply hwithin.continuousOn.congr
    intro z hz
    exact (fderivWithin_of_isOpen hP hz.1).symm
  obtain ⟨ρ, hρ, hρP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds hp)
  refine ⟨ρ, hρ, hρP, ?_⟩
  apply uniform_parameter_taylor_remainder H (closedBall p ρ) K
    (isCompact_closedBall p ρ) hK (convex_closedBall p ρ)
  · intro q hq y hy
    have hslice : ContDiffOn ℝ ∞ (fun r ↦ H r y) P :=
      hH.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun r hr ↦ ⟨hr, hKU hy⟩)
    exact (hslice.contDiffAt (hP.mem_nhds (hρP hq))).differentiableAt (by simp)
  · exact hA.mono (fun z hz ↦ ⟨hρP hz.1, hKU hz.2⟩)

end HolomorphicAnosov.Analysis
