import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DifferentialClosedAt

open Set
open scoped ContDiff

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- A complex covector field locally equal to the differential of a smooth scalar potential has
vanishing real exterior derivative at the given point. (Demailly, I §3.C, (3.17); Zhang, Lemma
4.2) -/
theorem locally_exact_covector_closed_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) (α : E → E →L[ℂ] ℂ) (x : E)
    (hg : ContDiffAt ℝ ∞ g x)
    (heq : (fun y ↦ (α y).restrictScalars ℝ) =ᶠ[𝓝 x] fderiv ℝ g) :
    extDeriv (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) ((α y).restrictScalars ℝ)) x = 0 := by
  have hcoef : (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
      (0 : Fin 1) ((α y).restrictScalars ℝ)) =ᶠ[𝓝 x]
      (fun y ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ
        (0 : Fin 1) (fderiv ℝ g y)) := by
    filter_upwards [heq] with y hy
    rw [hy]
  unfold extDeriv
  rw [hcoef.fderiv_eq]
  exact differential_closed_at g x hg


end HolomorphicAnosov.Paper.Zhang
