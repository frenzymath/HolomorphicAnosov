import HolomorphicAnosov.Topology.SingularSubspaceMembership
import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false
/-- The original subspace pair and nested intersection pair identify with the
supported singular subcomplex pairs, compatibly with the excision inclusion.
Source: Hatcher, Algebraic Topology, pp.110–111 and 124. The simplex map into a
subspace is a monomorphism, hence isomorphic to its image. For the intersection,
a simplex supported in both A and B lifts continuously to the nested subtype
by its two membership proofs. The lift and its inverse preserve every simplex
value, so they define a simplicial isomorphism. The two pair maps commute with
the inclusions because both composites forget the same membership proofs. -/
theorem singular_excision_pair_comparison (X : TopCat.{u}) (A B : Set X) :
    ∃ ep : singularSubspacePair X A ≅ (singularSubspace X A).pair,
      ∃ ei : singularExcisionSource X A B ≅ singularIntersectionPair X A B,
        ei.hom ≫ singularIntersectionInclusion X A B =
          singularExcisionInclusion X A B ≫ ep.hom := by
  let eA (Y : TopCat.{u}) (C : Set Y) :
      TopCat.toSSet.obj (TopCat.of C) ≅ (singularSubspace Y C : SSet.{u}) := by
    have : Mono (singularSubspaceInclusion Y C) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    exact asIso (Subfunctor.toRange (TopCat.toSSet.map (singularSubspaceInclusion Y C)))
  let ep : singularSubspacePair X A ≅ (singularSubspace X A).pair :=
    MorphismProperty.Comma.isoMk (eA X A) (Iso.refl _) (by
      change Subfunctor.toRange _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.comp_id]
      rfl)
  let N := {x : B | (x : X) ∈ A}
  let j : TopCat.of N ⟶ X :=
    singularSubspaceInclusion (TopCat.of B) N ≫ singularSubspaceInclusion X B
  have hj : Mono j := by
    have : Mono (singularSubspaceInclusion (TopCat.of B) N) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    have : Mono (singularSubspaceInclusion X B) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    dsimp [j]; infer_instance
  have hr : SSet.Subcomplex.range (TopCat.toSSet.map j) ≤
      singularSubspace X A ⊓ singularSubspace X B := by
    intro n τ hτ
    obtain ⟨σ, rfl⟩ := hτ
    constructor
    · apply (singularSubspace_mem_iff X A n _).mpr
      intro t
      exact (((TopCat.of N).toSSetObjEquiv n σ) t).property
    · apply (singularSubspace_mem_iff X B n _).mpr
      intro t
      exact (((TopCat.of N).toSSetObjEquiv n σ) t).val.property
  let m := SSet.Subcomplex.lift (TopCat.toSSet.map j) hr
  have hm : Mono m := mono_of_mono_fac (SSet.Subcomplex.lift_ι _ hr)
  have hsurj (n : SimplexCategoryᵒᵖ) : Function.Surjective (m.app n) := by
    intro τ
    have hA := (singularSubspace_mem_iff X A n τ.val).mp τ.property.1
    have hB := (singularSubspace_mem_iff X B n τ.val).mp τ.property.2
    let f : C(Convexity.StdSimplex ℝ (Fin ((unop n).len + 1)), N) :=
      ⟨fun t => ⟨⟨X.toSSetObjEquiv n τ.val t, hB t⟩, hA t⟩,
        ((X.toSSetObjEquiv n τ.val).continuous.subtype_mk _).subtype_mk _⟩
    refine ⟨((TopCat.of N).toSSetObjEquiv n).symm f, ?_⟩
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    ext t
    rfl
  have : IsIso m := by
    apply (NatTrans.isIso_iff_isIso_app m).mpr
    intro n
    exact (isIso_iff_bijective _).mpr
      ⟨(CategoryTheory.mono_iff_injective _).mp inferInstance, hsurj n⟩
  let ei : singularExcisionSource X A B ≅ singularIntersectionPair X A B :=
    MorphismProperty.Comma.isoMk (asIso m) (eA X B) (by
      ext n σ
      apply Subtype.ext
      rfl)
  refine ⟨ep, ei, ?_⟩
  apply MorphismProperty.Arrow.Hom.ext
  · ext n σ
    apply Subtype.ext
    rfl
  · rfl
end HolomorphicAnosov
