import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section
namespace HolomorphicAnosov.Analysis

/-- Reindexing bounded dependent sections by an equivalence is a linear isometry.
Source: the receiving-fibre reindexing in Shub (1987), pp.72–74. The proof is the
supremum norm identity: precomposition does not increase the supremum norm, and
surjectivity of the index equivalence gives the reverse inequality. The inverse
uses dependent function reindexing, so distinct fibres are never identified.
No topology, countability, nonemptiness, or continuity of sections is required. -/
theorem exists_bounded_section_reindex
    {A B : Type*} (E : B → Type*)
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
    (e : A ≃ B) :
    ∃ J : lp (fun a ↦ E (e a)) ⊤ ≃ₗᵢ[ℝ] lp E ⊤,
      ∀ w a, J w (e a) = w a := by
  let P : lp E ⊤ →ₗ[ℝ] lp (fun a ↦ E (e a)) ⊤ :=
    { toFun := fun w ↦ ⟨fun a ↦ w (e a), memℓp_infty ⟨‖w‖, by
        rintro _ ⟨a, rfl⟩
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero w (e a)⟩⟩
      map_add' := by intro w v; rfl
      map_smul' := by intro c w; rfl }
  have hnorm (w : lp E ⊤) : ‖P w‖ = ‖w‖ := by
    apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg w)
      intro a
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero w (e a)
    · apply lp.norm_le_of_forall_le (norm_nonneg (P w))
      intro b
      obtain ⟨a, rfl⟩ := e.surjective b
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (P w) a
  let Q : lp E ⊤ →ₗᵢ[ℝ] lp (fun a ↦ E (e a)) ⊤ := ⟨P, hnorm⟩
  have hsurj : Function.Surjective Q := by
    intro w
    let v := Equiv.piCongrLeft E e (fun a ↦ w a)
    have hv : Memℓp v ⊤ := by
      apply memℓp_infty
      refine ⟨‖w‖, ?_⟩
      rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective b
      simpa only [v, Equiv.piCongrLeft_apply_apply] using
        lp.norm_apply_le_norm ENNReal.top_ne_zero w a
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    funext a
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  let J := (LinearIsometryEquiv.ofSurjective Q hsurj).symm
  refine ⟨J, ?_⟩
  intro w a
  exact congrArg (fun z : lp (fun a ↦ E (e a)) ⊤ ↦ z a)
    ((LinearIsometryEquiv.ofSurjective Q hsurj).apply_symm_apply w)

end HolomorphicAnosov.Analysis
