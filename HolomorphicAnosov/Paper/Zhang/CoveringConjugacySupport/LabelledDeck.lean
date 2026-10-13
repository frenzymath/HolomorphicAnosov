import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.VectorCover

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- C5, Zhang equations (20)--(21) and Hatcher's full deck classification. -/
theorem covering_conjugacy_labelled_deck_g15
    {V Y X : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace Y] [TopologicalSpace X]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (p : Y → X) (h : X ≃ₜ V ⧸ Γ.toAddSubgroup) (H : Y ≃ₜ V)
    (hsquare : ∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y))
    (A : V ≃L[ℝ] V) (F : Y ≃ₜ Y) (hHF : ∀ y, H (F y) = A (H y)) :
    ∃ δ : Γ → Y ≃ₜ Y,
      (∀ γ y, H (δ γ y) = H y + (γ : V)) ∧
      (∀ γ y, p (δ γ y) = p y) ∧
      (∀ D : Y ≃ₜ Y, (∀ y, p (D y) = p y) ↔
        ∃! γ : Γ, ∀ y, D y = δ γ y) ∧
      (∀ γ γ' : Γ, (γ' : V) = A (γ : V) →
        ∀ y, F (δ γ y) = δ γ' (F y)) := by
  let δ : Γ → Y ≃ₜ Y := fun γ ↦
    (H.trans (Homeomorph.addRight (γ : V))).trans H.symm
  have hd : ∀ γ y, H (δ γ y) = H y + (γ : V) := by
    intro γ y
    simp [δ]
  have hp : ∀ γ y, p (δ γ y) = p y := by
    intro γ y
    apply h.injective
    rw [← hsquare, ← hsquare, hd]
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)
  refine ⟨δ, hd, hp, ?_, ?_⟩
  · intro D
    constructor
    · intro hD
      let E := (H.symm.trans D).trans H
      have hE : ∀ v, (QuotientAddGroup.mk (E v) : V ⧸ Γ.toAddSubgroup) =
          QuotientAddGroup.mk v := by
        intro v
        change QuotientAddGroup.mk (H (D (H.symm v))) = QuotientAddGroup.mk v
        rw [hsquare, hD, ← hsquare, H.apply_symm_apply]
      obtain ⟨γ, hγ, hu⟩ :=
        (covering_conjugacy_vector_cover_g15 Γ).2.2.2 E |>.mp hE
      have hDy : ∀ y, D y = δ γ y := by
        intro y
        apply H.injective
        rw [hd]
        simpa [E] using hγ (H y)
      refine ⟨γ, hDy, ?_⟩
      intro η hη
      apply hu
      intro v
      change H (D (H.symm v)) = v + (η : V)
      rw [hη, hd, H.apply_symm_apply]
    · rintro ⟨γ, hγ, _⟩ y
      rw [hγ y]
      exact hp γ y
  · intro γ γ' hγ' y
    apply H.injective
    rw [hHF, hd, map_add, hd, hHF, hγ']


end HolomorphicAnosov
