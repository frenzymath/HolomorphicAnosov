import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.CompactSupportUnionGluing
import HolomorphicAnosov.Topology.SingularHomologyExcision
import Mathlib.Topology.Compactness.Compact

noncomputable section
namespace HolomorphicAnosov
open CategoryTheory CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology
open Set
universe u

/-- Excision isomorphism for compact support and an open neighborhood whose closure lies inside it. -/
theorem integral_support_neighborhood_excision_homology_isIso
    (X : TopCat.{u}) (K U : Set X) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularExcisionInclusion X Kᶜ U) R q) := by
  have hcover : interior Kᶜ ∪ interior U = Set.univ := by
    apply Set.Subset.antisymm
    · intro x hx; exact Set.mem_univ x
    · intro x _
      by_cases hx : x ∈ closure K
      · exact Set.mem_union_right _ ((subset_interior_iff_isOpen.mpr hU) (hKU hx))
      · exact Set.mem_union_left _ (by rw [interior_compl]; exact hx)
  have h := singular_homology_excision_barycentric_subdivision.2.1 X Kᶜ U hcover R
  exact h.2.2 q

/-- The signed restriction to a compact union is injective when the next intersection term vanishes, as supplied by the support Mayer--Vietoris sequence. -/
theorem integral_union_restriction_injective (D : CompactSupportMVData.{u}) (q : ℕ)
    (hnext : Subsingleton (supportSingularHomology D.space (D.left ∩ D.right)
      D.coefficients (q + 1) : Type u)) :
    Function.Injective (supportMayerVietorisPhi D.space D.coefficients D.left D.right q) := by
  obtain ⟨δ, hδ, _⟩ := hatcher_compact_support_mayer_vietoris
  have he := (hδ D).1 q |>.1
  have hz : δ D q = 0 := by
    ext x
    have hx := hnext.elim x 0
    rw [hx, map_zero]
    simp
  rw [hz] at he
  intro x y hxy
  have hker : supportMayerVietorisPhi D.space D.coefficients D.left D.right q (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := he (x - y) |>.mp hker
  exact sub_eq_zero.mp (by simpa using hz.symm)

/-- A union class whose restrictions to both compact pieces vanish is zero under the same Mayer--Vietoris next-degree hypothesis. -/
theorem integral_union_zero_of_restrictions (D : CompactSupportMVData.{u}) (q : ℕ)
    (hnext : Subsingleton (supportSingularHomology D.space (D.left ∩ D.right)
      D.coefficients (q + 1) : Type u))
    (c : supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q)
    (hleft : supportSingularHomologyRestrict D.space D.coefficients
      Set.subset_union_left q c = 0)
    (hright : supportSingularHomologyRestrict D.space D.coefficients
      Set.subset_union_right q c = 0) : c = 0 := by
  apply integral_union_restriction_injective D q hnext
  change (_, -_) = _
  rw [hleft, hright]
  simp

/-- Above-dimension vanishing propagates through a compact union by Mayer--Vietoris. -/
theorem integral_union_above_dimension_subsingleton
    (D : CompactSupportMVData.{u}) (n : ℕ)
    (hleft : ∀ i : ℕ, n < i → Subsingleton
      (supportSingularHomology D.space D.left D.coefficients i : Type u))
    (hright : ∀ i : ℕ, n < i → Subsingleton
      (supportSingularHomology D.space D.right D.coefficients i : Type u))
    (hinter : ∀ i : ℕ, n < i → Subsingleton
      (supportSingularHomology D.space (D.left ∩ D.right) D.coefficients i : Type u)) :
    ∀ i : ℕ, n < i → Subsingleton
      (supportSingularHomology D.space (D.left ∪ D.right) D.coefficients i : Type u) := by
  intro i hi
  refine ⟨fun x y ↦ ?_⟩
  apply integral_union_restriction_injective D i
    (hinter (i + 1) (lt_trans hi (Nat.lt_succ_self i)))
  apply Prod.ext
  · exact hleft i hi |>.elim _ _
  · exact congrArg Neg.neg (hright i hi |>.elim _ _)

end HolomorphicAnosov
