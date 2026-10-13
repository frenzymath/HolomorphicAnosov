import HolomorphicAnosov.Topology.Homology.IntegralULiftSupportHomologyTransport
import HolomorphicAnosov.Topology.Homology.IntegralSupportRestrictionNormalization
import HolomorphicAnosov.Topology.Homology.IntegralSupportProfileHomeomorphTransport

/-! # Restriction-compatible integral support profiles across universes

Source: Hatcher, Algebraic Topology, relative chains and maps of pairs pp.115–118,
coefficients p.153. This is a universe adapter for those chain constructions.
The already constructed relative chain comparison commutes with quotient
projections. Both support restrictions are induced by the identity ambient map,
so cancelling the epic source projection proves naturality of the comparison.
Taking homology and using the exact ULift functor preserves this square.
Comparing two universe lifts through their common integral model gives linear
equivalences compatible with all support restrictions, including singletons.
Injectivity transfers point detection and above-dimension vanishing.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov
open HolomorphicAnosov.Topology _root_.Topology
universe u v
namespace IntegralSupportLift
open IntegralTransportG14

lemma relativeIso_projection (X : Type) [TopologicalSpace X] (A : Set X) :
    (actualPair X A).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫
      (relativeIso X A).hom =
    (absIso (TopCat.of X)).hom ≫
      ((ModuleCat.uliftFunctor.{u,0} ℤ).mapHomologicalComplex (.down ℕ)).map
        ((supportSingularPair (TopCat.of X) A).chainComplexπ (ModuleCat.of ℤ ℤ)) := by
  unfold relativeIso
  dsimp only [CokernelCofork.mapIsoOfIsColimit]
  change ((actualPair X A).cokernelCoforkChainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).π ≫ _ = _
  rw [CokernelCofork.π_mapOfIsColimit]
  simp only [Arrow.isoMk_hom_right, Iso.trans_hom, Functor.mapIso_hom,
    CokernelCofork.map_π]
  have hid : TopCat.toSSet.map (actualRightIso X).hom = 𝟙 _ := by
    change TopCat.toSSet.map (𝟙 _) = _
    exact TopCat.toSSet.map_id _
  rw [hid]
  erw [((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).map_id]
  change (𝟙 _ ≫ (absIso (TopCat.of X)).hom) ≫
    ((ModuleCat.uliftFunctor.{u,0} ℤ).mapHomologicalComplex (.down ℕ)).map
      ((supportSingularPair (TopCat.of X) A).chainComplexπ (ModuleCat.of ℤ ℤ)) = _
  rw [Category.id_comp]


/-- The identity of the ambient space induces restriction of support pairs. -/
def restrictPair (X : TopCat.{v}) {A B : Set X} (h : B ⊆ A) :
    supportSingularPair X A ⟶ supportSingularPair X B :=
  supportSingularPairMap A B (𝟙 X) (fun _ hx hb ↦ hx (h hb))

lemma projection_restrict (X : TopCat.{v}) {A B : Set X} (h : B ⊆ A)
    (R : ModuleCat.{v} ℤ) :
    (supportSingularPair X A).chainComplexπ R ≫
      SSetPair.chainComplexMap (restrictPair X h) R =
      (supportSingularPair X B).chainComplexπ R := by
  have hn := (((SSetPair.chainComplexFunctorπ (ModuleCat.{v} ℤ)).app R).naturality
    (restrictPair X h)).symm
  change _ = _ at hn
  have hr : (restrictPair X h).hom.right = 𝟙 _ := by
    change TopCat.toSSet.map (𝟙 X) = _
    exact TopCat.toSSet.map_id X
  change (supportSingularPair X A).chainComplexπ R ≫
    SSetPair.chainComplexMap (restrictPair X h) R =
      SSet.chainComplexMap (restrictPair X h).hom.right R ≫
        (supportSingularPair X B).chainComplexπ R at hn
  rw [hr] at hn
  simpa using hn

lemma relativeIso_restrict (X : Type) [TopologicalSpace X] {A B : Set X} (h : B ⊆ A) :
    SSetPair.chainComplexMap (restrictPair (TopCat.of (ULift.{u} X))
      (A := ULift.down ⁻¹' A) (B := ULift.down ⁻¹' B) (fun _ hx ↦ h hx))
        (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫ (relativeIso X B).hom =
    (relativeIso X A).hom ≫
      ((ModuleCat.uliftFunctor.{u,0} ℤ).mapHomologicalComplex (.down ℕ)).map
        (SSetPair.chainComplexMap (restrictPair (TopCat.of X) h) (ModuleCat.of ℤ ℤ)) := by
  apply (cancel_epi ((actualPair X A).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ)))).mp
  rw [← Category.assoc]
  erw [projection_restrict]
  erw [relativeIso_projection, ← Category.assoc, relativeIso_projection,
    Category.assoc, ← CategoryTheory.Functor.map_comp, projection_restrict]
  rfl


/-- The coherent homology comparison obtained from the relative chain isomorphism. -/
def homIso (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) :
    supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q ≅
    (ModuleCat.uliftFunctor.{u,0} ℤ).obj
      (supportSingularHomology (TopCat.of X) A (ModuleCat.of ℤ ℤ) q) :=
  HomologicalComplex.homologyMapIso (relativeIso X A) q ≪≫
    ((supportSingularChainComplex (TopCat.of X) A (ModuleCat.of ℤ ℤ)).sc q).mapHomologyIso
      (ModuleCat.uliftFunctor.{u,0} ℤ)

lemma homIso_restrict (X : Type) [TopologicalSpace X] {A B : Set X} (h : B ⊆ A) (q : ℕ) :
    SSetPair.homologyMap (restrictPair (TopCat.of (ULift.{u} X))
      (A := ULift.down ⁻¹' A) (B := ULift.down ⁻¹' B) (fun _ hx ↦ h hx))
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q ≫ (homIso X B q).hom =
    (homIso X A q).hom ≫ (ModuleCat.uliftFunctor.{u,0} ℤ).map
      (SSetPair.homologyMap (restrictPair (TopCat.of X) h) (ModuleCat.of ℤ ℤ) q) := by
  let F := ModuleCat.uliftFunctor.{u,0} ℤ
  let f := SSetPair.chainComplexMap (restrictPair (TopCat.of X) h) (ModuleCat.of ℤ ℤ)
  have hn := congrArg (fun f ↦ HomologicalComplex.homologyMap f q) (relativeIso_restrict.{u} X h)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  simp only [homIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  erw [← Category.assoc, hn, Category.assoc]
  rw [Category.assoc]
  exact congrArg (fun g ↦ HomologicalComplex.homologyMap (relativeIso X A).hom q ≫ g)
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (.down ℕ) q).map f) F)

/-- Lower the lifted homology carrier after the canonical comparison. -/
def homEquiv (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) :
    supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q ≃ₗ[ℤ]
    supportSingularHomology (TopCat.of X) A (ModuleCat.of ℤ ℤ) q :=
  (homIso X A q).toLinearEquiv.trans ULift.moduleEquiv

lemma homEquiv_restrict (X : Type) [TopologicalSpace X] {A B : Set X} (h : B ⊆ A) (q : ℕ)
    (a : supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q) :
    homEquiv X B q (supportSingularHomologyRestrict (TopCat.of (ULift.{u} X))
      (ModuleCat.of ℤ (ULift.{u} ℤ)) (fun _ hx ↦ h hx) q a) =
    supportSingularHomologyRestrict (TopCat.of X) (ModuleCat.of ℤ ℤ) h q (homEquiv X A q a) := by
  rw [integral_support_restrict_native_apply, integral_support_restrict_native_apply]
  exact congrArg (fun f ↦ (f a).down) (homIso_restrict.{u} X h q)


/-- Compare lifted support groups using their common integral chain model. -/
def compare (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) :
    supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q ≃ₗ[ℤ]
    supportSingularHomology (TopCat.of (ULift.{0} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) q :=
  (homEquiv.{u} X A q).trans (homEquiv.{0} X A q).symm

lemma compare_restrict (X : Type) [TopologicalSpace X] {A B : Set X} (h : B ⊆ A) (q : ℕ)
    (a : supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q) :
    compare X B q (supportSingularHomologyRestrict (TopCat.of (ULift.{u} X))
      (ModuleCat.of ℤ (ULift.{u} ℤ)) (fun _ hx ↦ h hx) q a) =
    supportSingularHomologyRestrict (TopCat.of (ULift.{0} X))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (fun _ hx ↦ h hx) q (compare X A q a) := by
  apply (homEquiv.{0} X B q).injective
  change homEquiv.{0} X B q ((homEquiv.{0} X B q).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  erw [homEquiv_restrict, homEquiv_restrict]
  congr 1
  exact ((homEquiv.{0} X A q).apply_symm_apply _).symm

lemma restrict_zero_seteq (X : TopCat.{v}) (R : ModuleCat.{v} ℤ)
    {A B D : Set X} (hBD : B = D) (hB : B ⊆ A) (hD : D ⊆ A) (q : ℕ)
    (a : supportSingularHomology X A R q) :
    supportSingularHomologyRestrict X R hB q a = 0 ↔
      supportSingularHomologyRestrict X R hD q a = 0 := by
  subst D
  rfl

/-- Point detection and higher-degree vanishing are unchanged by the universe lift.
The proof uses the natural relative-chain comparison, so the point restrictions
are the original restrictions and not a newly selected family of linear maps. -/
theorem profile (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    (hdetect : ∀ a : supportSingularHomology (TopCat.of X) A
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
      (∀ x (hx : x ∈ A), supportSingularHomologyRestrict (TopCat.of X)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0)
    (hvanish : ∀ q, n < q → Subsingleton (supportSingularHomology (TopCat.of X) A
      (ModuleCat.of ℤ (ULift.{0} ℤ)) q : Type)) :
    (∀ a : supportSingularHomology (TopCat.of (ULift.{u} X)) (ULift.down ⁻¹' A)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ (x : ULift.{u} X) (hx : x.down ∈ A), supportSingularHomologyRestrict (TopCat.of (ULift.{u} X))
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q, n < q → Subsingleton (supportSingularHomology (TopCat.of (ULift.{u} X))
      (ULift.down ⁻¹' A) (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) := by
  obtain ⟨hd,hv⟩ := integral_support_profile_homeomorph_transport
    (Homeomorph.ulift : ULift.{0} X ≃ₜ X) (ULift.down ⁻¹' A) A (fun _ ↦ Iff.rfl)
    n hdetect hvanish
  constructor
  · intro a ha
    apply (compare.{u} X A n).injective
    rw [map_zero]
    apply hd
    intro x hx
    have heH : (ULift.down ⁻¹' ({x.down} : Set X) : Set (ULift.{u} X)) = {ULift.up x.down} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ULift.ext_iff]
    have heL : (ULift.down ⁻¹' ({x.down} : Set X) : Set (ULift.{0} X)) = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ULift.ext_iff]
    have hzero : supportSingularHomologyRestrict (TopCat.of (ULift.{u} X))
        (ModuleCat.of ℤ (ULift.{u} ℤ))
        (show ULift.down ⁻¹' ({x.down} : Set X) ⊆ ULift.down ⁻¹' A from
          Set.preimage_mono (Set.singleton_subset_iff.mpr hx)) n a = 0 := by
      exact (restrict_zero_seteq _ _ heH _ _ _ _).mpr (ha (ULift.up x.down) hx)
    have hh := compare_restrict.{u} X (Set.singleton_subset_iff.mpr hx) n a
    erw [hzero, map_zero] at hh
    exact (restrict_zero_seteq _ _ heL _ _ _ _).mp hh.symm
  · intro q hq
    have := hv q hq
    exact (compare.{u} X A q).injective.subsingleton

end IntegralSupportLift
end HolomorphicAnosov

