import HolomorphicAnosov.Topology.GoodPairCollapse
import Mathlib.Topology.Homeomorph.Lemmas

/-! Intrinsic neighborhood collapse and its ambient quotient image. -/

open Set Topology _root_.Topology

namespace HolomorphicAnosov.GoodPair.NeighborhoodImageG8

universe u
variable {X : Type u} [TopologicalSpace X]

noncomputable section

/-- The subset collapsed inside the original subspace `V`. -/
def intrinsicCollapsedSubset (A V : Set X) : Set V := {x | x.1 ∈ A}

/-- The projection to the ambient quotient image. (Hatcher, Prop. 2.22) -/
def imageProjection (A V : Set X) (x : V) : (collapse A '' V) :=
  ⟨collapse A x.1, ⟨x.1, x.2, rfl⟩⟩

/-- Intrinsic related representatives have equal ambient quotient-image projections.(Hatcher, Prop. 2.22) -/
theorem imageProjection_respects (A V : Set X) (x y : V)
    (h : (collapseSetoid (intrinsicCollapsedSubset A V)).r x y) :
    imageProjection A V x = imageProjection A V y := by
  apply Subtype.ext
  rcases h with hxy | ⟨hx, hy⟩
  · simp [hxy]
  · apply Quotient.sound
    exact Or.inr ⟨hx, hy⟩

/-- The quotient lift carries the quotient topology. -/
def quotientImageMap (A V : Set X) :
    Collapsed (intrinsicCollapsedSubset A V) → (collapse A '' V) :=
  Quotient.lift (imageProjection A V) (imageProjection_respects A V)

/-- Containment makes the restricted projection a quotient map, although `V` need not be open. (Hatcher, Prop. 2.22) -/
theorem isQuotientMap_imageProjection {A V : Set X} (hAV : A ⊆ V) :
    IsQuotientMap (imageProjection A V) := by
  have hc : Continuous (imageProjection A V) :=
    ((collapse A).continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective (imageProjection A V) := by
    rintro ⟨z, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨.of_isOpen_preimage_iff_isOpen (fun S ↦ ⟨?_, fun h ↦ h.preimage hc⟩), hs⟩
  intro hS
  obtain ⟨O, hO, heq⟩ := IsInducing.subtypeVal.isOpen_iff.mp hS
  have hmem (x : V) : x.1 ∈ O ↔ imageProjection A V x ∈ S :=
    Set.ext_iff.mp heq x
  have hsat : collapse A ⁻¹' (collapse A '' O) = O := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rcases Quotient.exact hyx with h | ⟨hyA, hxA⟩
      · exact h ▸ hy
      · apply (hmem ⟨x, hAV hxA⟩).mpr
        have he : imageProjection A V ⟨y, hAV hyA⟩ =
            imageProjection A V ⟨x, hAV hxA⟩ := Subtype.ext hyx
        exact he ▸ (hmem ⟨y, hAV hyA⟩).mp hy
    · exact fun hx ↦ ⟨x, hx, rfl⟩
  have hqO : IsOpen (collapse A '' O) :=
    (isQuotientMap_quotient_mk'.isOpen_preimage).mp (hsat.symm ▸ hO)
  have heqS : Subtype.val ⁻¹' (collapse A '' O) = S := by
    ext z
    obtain ⟨x, rfl⟩ := hs z
    change collapse A x.1 ∈ collapse A '' O ↔ imageProjection A V x ∈ S
    rw [← hmem x]
    exact Set.ext_iff.mp hsat x.1
  exact heqS ▸ hqO.preimage continuous_subtype_val

/-- The exact quotient lift is a homeomorphism under containment. (Hatcher, Prop. 2.22) -/
theorem isHomeomorph_quotientImageMap {A V : Set X} (hAV : A ⊆ V) :
    IsHomeomorph (quotientImageMap A V) := by
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨isQuotientMap_quotient_mk'.of_comp_isQuotientMap
    (isQuotientMap_imageProjection hAV), ?_⟩
  intro z w
  induction z using Quotient.inductionOn with | h x =>
    induction w using Quotient.inductionOn with | h y =>
      intro hxy
      apply Quotient.sound
      rcases Quotient.exact (congrArg Subtype.val hxy) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr h

/-- The homeomorphism has forward function `quotientImageMap`. (Hatcher, Prop. 2.22) -/
def quotientImageHomeomorph {A V : Set X} (hAV : A ⊆ V) :
    Collapsed (intrinsicCollapsedSubset A V) ≃ₜ (collapse A '' V) :=
  IsHomeomorph.homeomorph (quotientImageMap A V) (isHomeomorph_quotientImageMap hAV)

/-- The neighborhood specialization applies when `A ⊆ interior V`.(Hatcher, Prop. 2.22) -/
def neighborhoodQuotientImageHomeomorph {A V : Set X} (hAV : A ⊆ interior V) :
    Collapsed {x : V | x.1 ∈ A} ≃ₜ (collapse A '' V) :=
  quotientImageHomeomorph (hAV.trans interior_subset)

/-- The exact representative square commutes as functions, including at the frontier of `V`. (Hatcher, Prop. 2.22) -/
theorem neighborhood_inclusion_projection_square {A V : Set X}
    (hAV : A ⊆ interior V) :
    (fun x : V ↦
      (neighborhoodQuotientImageHomeomorph hAV (collapse {x : V | x.1 ∈ A} x)).1) =
      (fun x : V ↦ collapse A x.1) := by
  rfl

/-- The homeomorphism preserves exactly the collapsed parts, including empty parts. (Hatcher, Prop. 2.22) -/
theorem neighborhoodQuotientImageHomeomorph_mem_collapsedPart {A V : Set X}
    (hAV : A ⊆ interior V) (z : Collapsed {x : V | x.1 ∈ A}) :
    z ∈ collapsedPart {x : V | x.1 ∈ A} ↔
      (neighborhoodQuotientImageHomeomorph hAV z).1 ∈ collapsedPart A := by
  induction z using Quotient.inductionOn with | h x =>
    change collapse {x : V | x.1 ∈ A} x ∈ collapsedPart {x : V | x.1 ∈ A} ↔
      collapse A x.1 ∈ collapsedPart A
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y.1, hy, ?_⟩
      exact congrArg (fun z ↦ (quotientImageMap A V z).1) hyx
    · rintro ⟨a, ha, hax⟩
      have hx : x.1 ∈ A := by
        rcases Quotient.exact hax with h | h
        · exact h ▸ ha
        · exact h.2
      exact ⟨x, hx, rfl⟩

end
end HolomorphicAnosov.GoodPair.NeighborhoodImageG8
