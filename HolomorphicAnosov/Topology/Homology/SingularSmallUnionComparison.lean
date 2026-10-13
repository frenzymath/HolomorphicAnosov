import HolomorphicAnosov.Topology.Homology.RelativeHomologyMapIso
import HolomorphicAnosov.Topology.Homology.SmallChainInclusionEquivalence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped _root_.Topology
namespace HolomorphicAnosov.Topology
universe u

/-- Singular subspaces respect intersection. -/
theorem singularSubspace_inter (X : TopCat.{u}) (A B : Set X) :
    singularSubspace X (A ∩ B) = singularSubspace X A ⊓ singularSubspace X B := by
  obtain ⟨_, _, _, h, _⟩ := singular_subspace_subcomplex_adapter.{u,u,u}
  exact h X A B

/-- Singular subspaces respect inclusions. -/
theorem singularSubspace_mono (X : TopCat.{u}) : Monotone (singularSubspace X) := by
  obtain ⟨_, _, _, _, h, _⟩ := singular_subspace_subcomplex_adapter.{u,u,u}
  exact h X

/-- Taking singular subspaces commutes with continuous preimages. -/
theorem singularSubspace_preimage {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set Y) :
    singularSubspace X (f ⁻¹' A) = (singularSubspace Y A).preimage (TopCat.toSSet.map f) := by
  ext n σ
  simp only [SSet.Subcomplex.preimage_obj, Set.mem_preimage, singularSubspace_mem_iff]
  rfl

/-- The image of a preimage subcomplex is the original subcomplex when it lies
in the range of the ambient simplicial map. -/
theorem subcomplex_image_preimage {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : Y.Subcomplex) (hA : A ≤ SSet.Subcomplex.range f) :
    (A.preimage f).image f = A := by
  apply le_antisymm (A.image_preimage_le f)
  intro n σ hσ
  obtain ⟨τ, rfl⟩ := hA n hσ
  exact ⟨τ, hσ, rfl⟩

/-- Restricting a monomorphism to a subcomplex in its range is an isomorphism. -/
theorem subcomplex_fromPreimage_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (A : Y.Subcomplex) (hA : A ≤ SSet.Subcomplex.range f) :
    IsIso (A.fromPreimage f) := by
  have : Mono (A.fromPreimage f) := mono_of_mono_fac (A.fromPreimage_ι f)
  have : Epi (A.fromPreimage f) := by
    rw [NatTrans.epi_iff_epi_app]
    intro n
    rw [epi_iff_surjective]
    rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ⟩ := hA n hσ
    exact ⟨⟨τ, by change f.app n τ ∈ A.obj n; rwa [hτ]⟩, Subtype.ext hτ⟩
  exact isIso_of_mono_of_epi _

/-- Transport an inclusion homology isomorphism through the range of a mono. -/
theorem subcomplex_range_homology_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (A : Y.Subcomplex) (hA : A ≤ SSet.Subcomplex.range f)
    (R : ModuleCat.{u} ℤ) (n : ℕ)
    (h : IsIso (SSet.homologyMap (A.preimage f).ι R n)) :
    IsIso (SSet.homologyMap (SSet.Subcomplex.homOfLE hA) R n) := by
  have := subcomplex_fromPreimage_isIso f A hA
  have : IsIso (SSet.Subcomplex.toRange f) := inferInstance
  have w : A.fromPreimage f ≫ SSet.Subcomplex.homOfLE hA =
      (A.preimage f).ι ≫ SSet.Subcomplex.toRange f := by rfl
  have hw := congrArg (fun k ↦ SSet.homologyMap k R n) w
  simp only [SSet.homologyMap_comp] at hw
  have : IsIso (SSet.homologyMap (A.fromPreimage f) R n ≫
      SSet.homologyMap (SSet.Subcomplex.homOfLE hA) R n) := by
    rw [hw]
    infer_instance
  exact IsIso.of_isIso_comp_left (SSet.homologyMap (A.fromPreimage f) R n) _

/-- For two open subsets, chains small in either subset have the homology of
all chains in their union. Apply the small-chain equivalence inside the union
subspace, then transport along the singular image isomorphisms. -/
theorem singularSmallUnion_homology_isIso (X : TopCat.{u}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSet.homologyMap (SSet.Subcomplex.homOfLE
      (sup_le (singularSubspace_mono X (Set.subset_union_left : A ⊆ A ∪ B))
        (singularSubspace_mono X (Set.subset_union_right : B ⊆ A ∪ B)))) R n) := by
  let Y := TopCat.of ↥(A ∪ B)
  let i := singularSubspaceInclusion X (A ∪ B)
  let f := TopCat.toSSet.map i
  have : Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  have : Mono f := inferInstance
  apply subcomplex_range_homology_isIso f (singularSubspace X A ⊔ singularSubspace X B)
  have hU : IsOpen (i ⁻¹' A) := hA.preimage i.hom.continuous
  have hV : IsOpen (i ⁻¹' B) := hB.preimage i.hom.continuous
  have hcover : interior (i ⁻¹' A) ∪ interior (i ⁻¹' B) = Set.univ := by
    rw [hU.interior_eq, hV.interior_eq]
    exact Set.eq_univ_of_forall (fun x ↦ x.property)
  obtain ⟨e, he⟩ := small_chain_inclusion_homotopy_equivalence Y
    (i ⁻¹' A) (i ⁻¹' B) hcover R
  have hsmall : IsIso (SSet.homologyMap
      (singularSubspace Y (i ⁻¹' A) ⊔ singularSubspace Y (i ⁻¹' B)).ι R n) := by
    change IsIso (HomologicalComplex.homologyMap _ n)
    rw [← he]
    exact (e.toHomologyIso n).isIso_hom
  rw [singularSubspace_preimage, singularSubspace_preimage] at hsmall
  exact hsmall

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A map of simplicial pairs induces the corresponding map of short exact
chain sequences. -/
def pairChainShortComplexMap {P Q : SSetPair.{u}} (f : P ⟶ Q)
    (R : ModuleCat.{u} ℤ) : P.chainComplexShortComplex R ⟶ Q.chainComplexShortComplex R where
  τ₁ := SSet.chainComplexMap f.hom.left R
  τ₂ := SSet.chainComplexMap f.hom.right R
  τ₃ := SSetPair.chainComplexMap f R
  comm₁₂ := by
    dsimp [SSetPair.chainComplexShortComplex]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k ↦ SSet.chainComplexMap k R) f.hom.w
  comm₂₃ := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality f)

/-- The small-union quotient computes the actual relative homology modulo
the topological union. The two absolute comparison maps are a small-chain
homology equivalence and the identity, so the relative comparison is an
isomorphism by the long exact sequences. -/
theorem singularSmallUnion_relative_homology_isIso (X : TopCat.{u}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (SSetPair.homMk (X := (singularSubspace X A ⊔ singularSubspace X B).pair)
        (Y := (singularSubspace X (A ∪ B)).pair)
        (SSet.Subcomplex.homOfLE
          (sup_le (singularSubspace_mono X (Set.subset_union_left : A ⊆ A ∪ B))
            (singularSubspace_mono X (Set.subset_union_right : B ⊆ A ∪ B))))
        (𝟙 (TopCat.toSSet.obj X)) (by rfl)) R n) := by
  apply relative_homologyMap_isIso_of_absolute
  · intro k
    exact singularSmallUnion_homology_isIso X A B hA hB R k
  · intro k
    change IsIso (SSet.homologyMap (𝟙 (TopCat.toSSet.obj X)) R k)
    infer_instance

end HolomorphicAnosov.Topology
