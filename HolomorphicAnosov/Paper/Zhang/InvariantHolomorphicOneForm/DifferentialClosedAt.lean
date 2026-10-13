import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

open Set
open scoped ContDiff

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- The real exterior derivative of the differential of a smooth complex-valued potential vanishes
at the given point. (Zhang, Lemma 4.2; Demailly, I §3.C, (3.17)) -/
theorem differential_closed_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (x : E) (hg : ContDiffAt ℝ ∞ g x) :
    extDeriv (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) (fderiv ℝ g y)) x = 0 := by
  let zeroForm : E → E [⋀^Fin 0]→L[ℝ] ℂ :=
    fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (g y)
  have hzero : ContDiffAt ℝ ∞ zeroForm x :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.contDiffAt.comp x hg
  have h := extDeriv_extDeriv_apply hzero (by simp)
  have heq : extDeriv zeroForm = fun y ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
        (0 : Fin 1) (fderiv ℝ g y) := by
    funext y
    exact extDeriv_constOfIsEmpty g y
  rw [heq] at h
  exact h


end HolomorphicAnosov.Paper.Zhang
