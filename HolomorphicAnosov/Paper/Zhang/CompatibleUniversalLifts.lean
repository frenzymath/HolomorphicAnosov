import Mathlib.Topology.Homotopy.Lifting

/-! Compatible homeomorphic lifts of conjugate dynamics to universal covers. (Zhang, eq. (20);
Hatcher, Props. 1.33, 1.34, 1.37) -/

universe u v w z

namespace HolomorphicAnosov

/-- A normalized homeomorphism between the bases has a unique homeomorphic lift to their universal
covers, and conjugation by this lift gives the unique compatible lift of the dynamics and its
inverse. (Zhang, eq. (20); Hatcher, Props. 1.33, 1.34, 1.37) -/
theorem compatible_universal_lifts
    {E : Type u} {X : Type v} {V : Type w} {N : Type z}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace V] [TopologicalSpace N]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace V] [LocallyPathConnectedSpace V]
    (p : E → X) (q : V → N)
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (_hp_surjective : Function.Surjective p) (_hq_surjective : Function.Surjective q)
    (h : X ≃ₜ N) (f : X ≃ₜ X) (α : N ≃ₜ N) (A : V ≃ₜ V)
    (hA : q ∘ A = α ∘ q) (hf : h ∘ f = α ∘ h)
    (x₀ : E) (v₀ : V) (h₀ : q v₀ = h (p x₀)) :
    let compatible : (E ≃ₜ V) × (E ≃ₜ E) → Prop := fun HF ↦
      HF.1 x₀ = v₀ ∧ q ∘ HF.1 = h ∘ p ∧ p ∘ HF.2 = f ∘ p ∧
        HF.1 ∘ HF.2 = A ∘ HF.1
    (∃! HF : (E ≃ₜ V) × (E ≃ₜ E), compatible HF) ∧
      ∀ HF : (E ≃ₜ V) × (E ≃ₜ E), compatible HF →
        p ∘ HF.1.symm = h.symm ∘ q ∧
        HF.2 = (HF.1.trans A).trans HF.1.symm ∧
        HF.2.symm = (HF.1.trans A.symm).trans HF.1.symm ∧
        p ∘ HF.2.symm = f.symm ∘ p := by
  classical
  obtain ⟨H, ⟨hH₀, hH⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    ⟨h ∘ p, h.continuous.comp hp.continuous⟩ x₀ v₀ h₀
  obtain ⟨G, ⟨hG₀, hG⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨h.symm ∘ q, h.symm.continuous.comp hq.continuous⟩ v₀ x₀
    (by change p x₀ = h.symm (q v₀); rw [h₀, h.symm_apply_apply])
  have hHp (x : E) : q (H x) = h (p x) := congrFun hH x
  have hGp (v : V) : p (G v) = h.symm (q v) := congrFun hG v
  have hGH : G ∘ H = id := hp.eq_of_comp_eq
    (G.continuous.comp H.continuous) continuous_id
    (by funext x; simp only [Function.comp_apply, hGp, hHp, h.symm_apply_apply, id_eq])
    x₀ (by simp only [Function.comp_apply, hH₀, hG₀, id_eq])
  have hHG : H ∘ G = id := hq.eq_of_comp_eq
    (H.continuous.comp G.continuous) continuous_id
    (by funext v; simp only [Function.comp_apply, hHp, hGp, h.apply_symm_apply, id_eq])
    v₀ (by simp only [Function.comp_apply, hG₀, hH₀, id_eq])
  let H₁ : E ≃ₜ V :=
    { toEquiv :=
        { toFun := H
          invFun := G
          left_inv := fun x ↦ congrFun hGH x
          right_inv := fun v ↦ congrFun hHG v }
      continuous_toFun := H.continuous
      continuous_invFun := G.continuous }
  let F₁ : E ≃ₜ E := (H₁.trans A).trans H₁.symm
  have hApoint (v : V) : q (A v) = α (q v) := congrFun hA v
  have hfpoint (x : X) : h (f x) = α (h x) := congrFun hf x
  have hF₁ : p ∘ F₁ = f ∘ p := by
    funext x
    change p (G (A (H x))) = f (p x)
    rw [hGp, hApoint, hHp, ← hfpoint, h.symm_apply_apply]
  have hcompat : H₁ x₀ = v₀ ∧ q ∘ H₁ = h ∘ p ∧ p ∘ F₁ = f ∘ p ∧
      H₁ ∘ F₁ = A ∘ H₁ := by
    refine ⟨hH₀, hH, hF₁, ?_⟩
    funext x
    exact H₁.apply_symm_apply (A (H₁ x))
  refine ⟨?_, ?_⟩
  · refine ⟨(H₁, F₁), hcompat, ?_⟩
    rintro ⟨H₂, F₂⟩ ⟨hH₂₀, hH₂, hF₂, hinter₂⟩
    have heq : H₂ = H₁ := Homeomorph.ext <| congrFun <| hq.eq_of_comp_eq
      H₂.continuous H₁.continuous (hH₂.trans hH.symm) x₀ (hH₂₀.trans hH₀.symm)
    apply Prod.ext heq
    apply Homeomorph.ext
    intro x
    apply H₁.injective
    have hx := congrFun hinter₂ x
    rw [heq] at hx
    exact hx.trans (congrFun hcompat.2.2.2 x).symm
  · rintro ⟨H₂, F₂⟩ ⟨hH₂₀, hH₂, hF₂, hinter₂⟩
    have hproj : p ∘ H₂.symm = h.symm ∘ q := by
      funext v
      apply h.injective
      have hx := congrFun hH₂ (H₂.symm v)
      simpa only [Function.comp_apply, H₂.apply_symm_apply, h.apply_symm_apply] using hx.symm
    have hformula : F₂ = (H₂.trans A).trans H₂.symm := by
      apply Homeomorph.ext
      intro x
      apply H₂.injective
      simpa only [Function.comp_apply, Homeomorph.trans_apply, H₂.apply_symm_apply]
        using congrFun hinter₂ x
    refine ⟨hproj, hformula, ?_, ?_⟩
    · rw [hformula]
      rfl
    · funext x
      apply f.injective
      have hx := congrFun hF₂ (F₂.symm x)
      simpa only [Function.comp_apply, F₂.apply_symm_apply, f.apply_symm_apply] using hx.symm

end HolomorphicAnosov

