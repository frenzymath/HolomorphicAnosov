import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DifferentialClosedAt
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open Set
open scoped ContDiff

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- The actual complex differential of a holomorphic local potential is closed as a complex-valued REAL one-form. -/
theorem complex_differential_closed_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) (O : Set E) (hO : IsOpen O)
    (hg : ContDiffOn ℂ ∞ g O) (x : E) (hx : x ∈ O) :
    extDeriv (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) ((fderiv ℂ g y).restrictScalars ℝ)) x = 0 := by
  have hreal : ContDiffAt ℝ ∞ g x :=
    (hg.restrict_scalars ℝ).contDiffAt (hO.mem_nhds hx)
  have heq : (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) ((fderiv ℂ g y).restrictScalars ℝ)) =ᶠ[𝓝 x]
      (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
        (0 : Fin 1) (fderiv ℝ g y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [(hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp) |>.fderiv_restrictScalars ℝ]
  unfold extDeriv
  rw [heq.fderiv_eq]
  exact differential_closed_at g x hreal


end HolomorphicAnosov.Paper.Zhang
