import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.Filter.Basic

noncomputable section
open Filter

namespace HolomorphicAnosov

/-- Finite chronological linear-coordinate germ identities compose in their common
transverse parameter. Motivating source: Nisoli, Local dynamics of singular holomorphic
foliations, Chapter 1, equation (1.11) and Remark 1.3.5, pp.22–23; Zhang Lemmas 2.8–2.10,
pp.9–10, linear holonomy coefficients. This common-parameter formulation is an agent-written
expansion of finite composition. Induct on the number of pieces, choose the next coefficient,
intersect the two eventual-equality sets, and compose the coefficients in chronological order.
The zero-piece case is the identity coefficient. No nontrivial-filter assumption is needed.
-/
theorem finite_linear_coordinate_germ_composition
    {Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : Filter Y) (n : ℕ) (ψ : Fin (n + 1) → Y → E)
    (h : ∀ j : Fin n, ∃ D : E ≃L[ℂ] E,
      ψ j.succ =ᶠ[l] fun v ↦ D (ψ j.castSucc v)) :
    ∃ D : E ≃L[ℂ] E, ψ (Fin.last n) =ᶠ[l] fun v ↦ D (ψ 0 v) := by
  induction n with
  | zero =>
    exact ⟨ContinuousLinearEquiv.refl ℂ E, Filter.Eventually.of_forall (fun _ ↦ rfl)⟩
  | succ n ih =>
    obtain ⟨D, hD⟩ := ih (fun i ↦ ψ i.castSucc) (fun j ↦ h j.castSucc)
    obtain ⟨D', hD'⟩ := h (Fin.last n)
    refine ⟨D.trans D', ?_⟩
    filter_upwards [hD, hD'] with v hv hv'
    exact hv'.trans (congrArg D' hv)


end HolomorphicAnosov
