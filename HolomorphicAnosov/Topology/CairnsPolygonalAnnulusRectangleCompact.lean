import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Compactness of the containing affine rectangle

This provider isolates the elementary compactness step in the Cairns
parameterization: an affine isometric image of a finite coordinate box is
compact.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A nondegenerate affine-isometric coordinate rectangle is compact. -/
theorem cairns_polygonal_annulus_rectangle_compact
    (R : Set Plane)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧
      R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) :
    IsCompact R := by
  obtain ⟨e, a, b, hab, rfl⟩ := hrectangle
  let C : Set (Fin 2 → ℝ) := Set.Icc a b
  have hC : IsCompact C := isCompact_Icc
  have heq : {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm '' C := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, C, Set.mem_Icc]
    constructor
    · intro hx
      exact ⟨x, ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact fun i ↦ ⟨hy.1 i, hy.2 i⟩
  rw [heq]
  exact (hC.image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous).image e.continuous

end HolomorphicAnosov.Topology

