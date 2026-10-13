import Mathlib.Analysis.Complex.Basic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- An equivalence preserving the fibres of a surjective scalar projection in both directions
descends to mutually inverse scalar maps, expressed using a section of the projection. (Zhang,
Lemma 4.2) -/
theorem projection_fibre_factorization {Y : Type*}
    (q : Y → ℂ) (i : ℂ → Y) (hi : ∀ z, q (i z) = z)
    (D : Y ≃ Y)
    (hD : ∀ y z, q y = q z → q (D y) = q (D z))
    (hDi : ∀ y z, q y = q z → q (D.symm y) = q (D.symm z)) :
    ∃ G J : ℂ → ℂ,
      (∀ y, G (q y) = q (D y)) ∧
      (∀ y, J (q y) = q (D.symm y)) ∧
      (∀ z, J (G z) = z) ∧ (∀ z, G (J z) = z) ∧
      (∀ H : ℂ → ℂ, (∀ y, H (q y) = q (D y)) → H = G) := by
  let G : ℂ → ℂ := fun z ↦ q (D (i z))
  let J : ℂ → ℂ := fun z ↦ q (D.symm (i z))
  have hG : ∀ y, G (q y) = q (D y) :=
    fun y ↦ hD (i (q y)) y (hi (q y))
  have hJ : ∀ y, J (q y) = q (D.symm y) :=
    fun y ↦ hDi (i (q y)) y (hi (q y))
  refine ⟨G, J, hG, hJ, ?_, ?_, ?_⟩
  · intro z
    calc
      J (G z) = J (q (D (i z))) := rfl
      _ = q (D.symm (D (i z))) := hJ _
      _ = z := by simp [hi]
  · intro z
    calc
      G (J z) = G (q (D.symm (i z))) := rfl
      _ = q (D (D.symm (i z))) := hG _
      _ = z := by simp [hi]
  · intro H hH
    funext z
    calc
      H z = H (q (i z)) := by rw [hi]
      _ = q (D (i z)) := hH _
      _ = G z := rfl


end HolomorphicAnosov.Paper.Zhang
