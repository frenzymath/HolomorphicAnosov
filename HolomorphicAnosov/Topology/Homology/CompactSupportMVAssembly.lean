import HolomorphicAnosov.Topology.Homology.SimplicialRelativeMayerVietoris
import HolomorphicAnosov.Topology.Homology.SupportSingularSubcomplexComparison
import HolomorphicAnosov.Topology.Homology.SingularSmallUnionComparison
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [-instance] AddCommGroup.toIntModule
attribute [-instance] CategoryTheory.Functor.hasBinaryBiproduct_of_preserves

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped _root_.Topology
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
namespace HolomorphicAnosov.Topology
universe u

/-- The chain map underlying the support homology map. -/
def supportChainMap {X Y : TopCat.{u}} (K : Set X) (L : Set Y)
    {R Q : ModuleCat.{u} ℤ} (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ) (γ : R ⟶ Q) :=
  (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app (supportSingularPair X K)) ≫
    SSetPair.chainComplexMap (supportSingularPairMap K L f hf) Q

@[reassoc (attr := simp)]
theorem supportChainMap_projection {X Y : TopCat.{u}} (K : Set X) (L : Set Y)
    {R Q : ModuleCat.{u} ℤ} (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ) (γ : R ⟶ Q) :
    (supportSingularPair X K).chainComplexπ R ≫ supportChainMap K L f hf γ =
      ambientChainMapOf R (TopCat.toSSet.map f) γ ≫ (supportSingularPair Y L).chainComplexπ Q := by
  dsimp [supportChainMap, ambientChainMapOf]
  rw [← Category.assoc]
  have hc := congrArg (fun t ↦ t.app (supportSingularPair X K))
    ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).naturality γ)
  have hp := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app Q).naturality
    (supportSingularPairMap K L f hf))
  change (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app (TopCat.toSSet.obj X)) ≫
    (supportSingularPair X K).chainComplexπ Q =
      (supportSingularPair X K).chainComplexπ R ≫ _ at hc
  change SSet.chainComplexMap (TopCat.toSSet.map f) Q ≫
    (supportSingularPair Y L).chainComplexπ Q =
      (supportSingularPair X K).chainComplexπ Q ≫ _ at hp
  rw [← hc, Category.assoc, ← hp, Category.assoc]

/-- A map of topological subspaces induces the required simplicial containment. -/
theorem singularSubspace_map_le {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    singularSubspace X A ≤ (singularSubspace Y B).preimage (TopCat.toSSet.map f) := by
  rw [← singularSubspace_preimage]
  exact singularSubspace_mono X hf

/-- Map from a support quotient to a larger simplicial quotient. -/
def supportToSubcomplex {X : TopCat.{u}} (K : Set X) (R : ModuleCat.{u} ℤ)
    {A : (TopCat.toSSet.obj X).Subcomplex} (h : singularSubspace X Kᶜ ≤ A) :
    supportSingularChainComplex X K R ⟶ A.pair.chainComplex R :=
  (supportSingularChainIso X K R).hom ≫ subcomplexRelativeMap R h

@[reassoc (attr := simp)]
theorem supportToSubcomplex_projection {X : TopCat.{u}} (K : Set X) (R : ModuleCat.{u} ℤ)
    {A : (TopCat.toSSet.obj X).Subcomplex} (h : singularSubspace X Kᶜ ≤ A) :
    (supportSingularPair X K).chainComplexπ R ≫ supportToSubcomplex K R h =
      A.pair.chainComplexπ R := by
  unfold supportToSubcomplex
  rw [← Category.assoc, supportSingularChainIso_projection, subcomplexRelativeMap_projection]

/-- A support comparison is an isomorphism whenever its subcomplex is exactly
the complement subcomplex. -/
theorem supportToSubcomplex_isIso {X : TopCat.{u}} (K : Set X) (R : ModuleCat.{u} ℤ)
    {A : (TopCat.toSSet.obj X).Subcomplex} (h : singularSubspace X Kᶜ ≤ A)
    (he : singularSubspace X Kᶜ = A) : IsIso (supportToSubcomplex K R h) := by
  subst A
  have hr : subcomplexRelativeMap R h = 𝟙 _ := by
    change ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R).map _ = _
    convert ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R).map_id
      (singularSubspace X Kᶜ).pair using 1
    congr 1
  rw [supportToSubcomplex, hr, Category.comp_id]
  infer_instance

/-- Naturality of support-to-subcomplex comparisons with coefficients. -/
theorem supportToSubcomplex_naturality {X Y : TopCat.{u}} (K : Set X) (L : Set Y)
    {R Q : ModuleCat.{u} ℤ} (f : X ⟶ Y) (hf : Set.MapsTo f Kᶜ Lᶜ) (γ : R ⟶ Q)
    {A : (TopCat.toSSet.obj X).Subcomplex} {B : (TopCat.toSSet.obj Y).Subcomplex}
    (hK : singularSubspace X Kᶜ ≤ A) (hL : singularSubspace Y Lᶜ ≤ B)
    (hAB : A ≤ B.preimage (TopCat.toSSet.map f)) :
    supportToSubcomplex K R hK ≫ subcomplexRelativeMapOf R (TopCat.toSSet.map f) hAB γ =
      supportChainMap K L f hf γ ≫ supportToSubcomplex L Q hL := by
  apply (cancel_epi ((supportSingularPair X K).chainComplexπ R)).mp
  simp only [← Category.assoc, supportToSubcomplex_projection,
    subcomplexRelativeMapOf_projection, supportChainMap_projection]
  rw [Category.assoc, supportToSubcomplex_projection]

/-- Support restrictions commute with the concrete quotient comparisons. -/
theorem supportToSubcomplex_restrict {X : TopCat.{u}} (K L : Set X)
    (R : ModuleCat.{u} ℤ) (h : L ⊆ K)
    {A B : (TopCat.toSSet.obj X).Subcomplex}
    (hK : singularSubspace X Kᶜ ≤ A) (hL : singularSubspace X Lᶜ ≤ B) (hAB : A ≤ B) :
    supportToSubcomplex K R hK ≫ subcomplexRelativeMap R hAB =
      supportChainMap K L (𝟙 X) (fun _ hx hL ↦ hx (h hL)) (𝟙 R) ≫
        supportToSubcomplex L R hL := by
  apply (cancel_epi ((supportSingularPair X K).chainComplexπ R)).mp
  rw [← Category.assoc, supportToSubcomplex_projection, subcomplexRelativeMap_projection,
    ← Category.assoc, supportChainMap_projection, Category.assoc, supportToSubcomplex_projection]
  have hi : ambientChainMapOf R (TopCat.toSSet.map (𝟙 X)) (𝟙 R) = 𝟙 _ := by
    simp [ambientChainMapOf]
  rw [hi]
  exact (Category.id_comp _).symm

@[simp]
theorem supportToSubcomplex_refl (X : TopCat.{u}) (K : Set X) (R : ModuleCat.{u} ℤ) :
    supportToSubcomplex K R le_rfl = (supportSingularChainIso X K R).hom := by
  apply (cancel_epi ((supportSingularPair X K).chainComplexπ R)).mp
  rw [supportToSubcomplex_projection, supportSingularChainIso_projection]

@[reassoc (attr := simp)]
theorem biprod_inl_isoProd (M N : ModuleCat.{u} ℤ) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom = ModuleCat.ofHom (LinearMap.inl ℤ M N) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M N).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;> simp only [Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst, ModuleCat.biprodIsoProd_inv_comp_snd]
  · ext x
    simp
  · ext x
    simp

@[reassoc (attr := simp)]
theorem biprod_inr_isoProd (M N : ModuleCat.{u} ℤ) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom = ModuleCat.ofHom (LinearMap.inr ℤ M N) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M N).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;> simp only [Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst, ModuleCat.biprodIsoProd_inv_comp_snd]
  · ext x
    simp
  · ext x
    simp

/-- Exactness is preserved by three module isomorphisms forming a commutative
ladder. This transports the native categorical long exact sequence. -/
theorem moduleExact_of_iso {M₁ M₂ M₃ : ModuleCat.{u} ℤ}
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (S : ShortComplex (ModuleCat.{u} ℤ))
    (e₁ : M₁ ≅ S.X₁) (e₂ : M₂ ≅ S.X₂) (e₃ : M₃ ≅ S.X₃)
    (h₁ : e₁.hom ≫ S.f = f ≫ e₂.hom) (h₂ : e₂.hom ≫ S.g = g ≫ e₃.hom)
    (hS : S.Exact) : Function.Exact f.hom.toAddMonoidHom g.hom.toAddMonoidHom := by
  apply (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.hom.toAddMonoidHom g.hom.toAddMonoidHom S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom
    e₁.hom.hom.toAddMonoidHom e₂.hom.hom.toAddMonoidHom e₃.hom.hom.toAddMonoidHom
    (congrArg (fun m ↦ m.hom.toAddMonoidHom) h₁)
    (congrArg (fun m ↦ m.hom.toAddMonoidHom) h₂)
    e₁.toLinearEquiv.surjective e₂.toLinearEquiv.bijective e₃.toLinearEquiv.injective).mpr
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS

namespace CompactSupportMVData

abbrev leftSubcomplex (D : CompactSupportMVData.{u}) := singularSubspace D.space D.leftᶜ
abbrev rightSubcomplex (D : CompactSupportMVData.{u}) := singularSubspace D.space D.rightᶜ
abbrev chainRow (D : CompactSupportMVData.{u}) :=
  nativeRelativeChainMV D.leftSubcomplex D.rightSubcomplex D.coefficients

theorem unionSubcomplex_eq (D : CompactSupportMVData.{u}) :
    singularSubspace D.space (D.left ∪ D.right)ᶜ = D.leftSubcomplex ⊓ D.rightSubcomplex := by
  rw [Set.compl_union, singularSubspace_inter]

theorem interSubcomplex_eq (D : CompactSupportMVData.{u}) :
    singularSubspace D.space (D.left ∩ D.right)ᶜ =
      singularSubspace D.space (D.leftᶜ ∪ D.rightᶜ) := by rw [Set.compl_inter]

/-- Union-support chains are exactly the first term of the quotient row. -/
def unionChainIso (D : CompactSupportMVData.{u}) :
    supportSingularChainComplex D.space (D.left ∪ D.right) D.coefficients ≅ D.chainRow.X₁ := by
  have := supportToSubcomplex_isIso (D.left ∪ D.right) D.coefficients
    D.unionSubcomplex_eq.le D.unionSubcomplex_eq
  exact asIso (supportToSubcomplex (D.left ∪ D.right) D.coefficients D.unionSubcomplex_eq.le)

/-- Intersection-support chains in the actual topological union quotient. -/
def interChainIso (D : CompactSupportMVData.{u}) :
    supportSingularChainComplex D.space (D.left ∩ D.right) D.coefficients ≅
      (singularSubspace D.space (D.leftᶜ ∪ D.rightᶜ)).pair.chainComplex D.coefficients := by
  have := supportToSubcomplex_isIso (D.left ∩ D.right) D.coefficients
    D.interSubcomplex_eq.le D.interSubcomplex_eq
  exact asIso (supportToSubcomplex (D.left ∩ D.right) D.coefficients D.interSubcomplex_eq.le)

/-- Inclusion from the small quotient to the actual topological union quotient. -/
abbrev smallQuotientMap (D : CompactSupportMVData.{u}) :=
  subcomplexRelativeMap D.coefficients
    (sup_le (singularSubspace_mono D.space (Set.subset_union_left : D.leftᶜ ⊆ D.leftᶜ ∪ D.rightᶜ))
      (singularSubspace_mono D.space (Set.subset_union_right : D.rightᶜ ⊆ D.leftᶜ ∪ D.rightᶜ)))

instance smallQuotientMap_homology_isIso (D : CompactSupportMVData.{u}) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap D.smallQuotientMap k) := by
  let : T2Space D.space := D.hausdorff
  exact singularSmallUnion_relative_homology_isIso D.space D.leftᶜ D.rightᶜ
    D.compact_left.isClosed.isOpen_compl D.compact_right.isClosed.isOpen_compl D.coefficients k

/-- First-term homology comparison, oriented from the support group to the chain row. -/
def unionHomologyIso (D : CompactSupportMVData.{u}) (k : ℕ) :
    supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k ≅ D.chainRow.X₁.homology k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).mapIso D.unionChainIso

/-- Last-term homology comparison uses the inverse of the actual excision map. -/
def interHomologyIso (D : CompactSupportMVData.{u}) (k : ℕ) :
    supportSingularHomology D.space (D.left ∩ D.right) D.coefficients k ≅ D.chainRow.X₃.homology k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).mapIso D.interChainIso ≪≫
    (asIso (HomologicalComplex.homologyMap D.smallQuotientMap k)).symm

/-- The actual product of support homology groups identifies with homology of
the biproduct of the two relative chain complexes. -/
def middleHomologyIso (D : CompactSupportMVData.{u}) (k : ℕ) :
    ModuleCat.of ℤ (supportSingularHomology D.space D.left D.coefficients k ×
      supportSingularHomology D.space D.right D.coefficients k) ≅ D.chainRow.X₂.homology k :=
  (ModuleCat.biprodIsoProd
    (supportSingularHomology D.space D.left D.coefficients k)
    (supportSingularHomology D.space D.right D.coefficients k)).symm ≪≫
    biprod.mapIso
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).mapIso
        (supportSingularChainIso D.space D.left D.coefficients))
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).mapIso
        (supportSingularChainIso D.space D.right D.coefficients)) ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).mapBiprod
      (D.leftSubcomplex.pair.chainComplex D.coefficients)
      (D.rightSubcomplex.pair.chainComplex D.coefficients)).symm

/-- The signed restriction as an integer-module morphism. -/
def phiMorphism (D : CompactSupportMVData.{u}) (k : ℕ) :
    supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k ⟶
      ModuleCat.of ℤ (supportSingularHomology D.space D.left D.coefficients k ×
        supportSingularHomology D.space D.right D.coefficients k) :=
  ModuleCat.ofHom ((HomologicalComplex.homologyMap
    (supportChainMap (D.left ∪ D.right) D.left (𝟙 D.space)
      (fun _ hx h ↦ hx (Or.inl h)) (𝟙 D.coefficients)) k).hom.prod
    (-(HomologicalComplex.homologyMap
      (supportChainMap (D.left ∪ D.right) D.right (𝟙 D.space)
        (fun _ hx h ↦ hx (Or.inr h)) (𝟙 D.coefficients)) k).hom))

/-- The sum restriction as an integer-module morphism. -/
def psiMorphism (D : CompactSupportMVData.{u}) (k : ℕ) :
    ModuleCat.of ℤ (supportSingularHomology D.space D.left D.coefficients k ×
      supportSingularHomology D.space D.right D.coefficients k) ⟶
        supportSingularHomology D.space (D.left ∩ D.right) D.coefficients k :=
  ModuleCat.ofHom ((HomologicalComplex.homologyMap
    (supportChainMap D.left (D.left ∩ D.right) (𝟙 D.space)
      (fun _ hx h ↦ hx h.1) (𝟙 D.coefficients)) k).hom.coprod
    (HomologicalComplex.homologyMap
      (supportChainMap D.right (D.left ∩ D.right) (𝟙 D.space)
        (fun _ hx h ↦ hx h.2) (𝟙 D.coefficients)) k).hom)

theorem unionChainIso_left (D : CompactSupportMVData.{u}) :
    D.unionChainIso.hom ≫ subcomplexRelativeMap D.coefficients
      (inf_le_left : D.leftSubcomplex ⊓ D.rightSubcomplex ≤ D.leftSubcomplex) =
      supportChainMap (D.left ∪ D.right) D.left (𝟙 D.space)
        (fun _ hx h ↦ hx (Or.inl h)) (𝟙 D.coefficients) ≫
          (supportSingularChainIso D.space D.left D.coefficients).hom := by
  simpa only [unionChainIso, asIso_hom, supportToSubcomplex_refl] using
    supportToSubcomplex_restrict (D.left ∪ D.right) D.left D.coefficients
      Set.subset_union_left D.unionSubcomplex_eq.le le_rfl inf_le_left

theorem unionChainIso_right (D : CompactSupportMVData.{u}) :
    D.unionChainIso.hom ≫ subcomplexRelativeMap D.coefficients
      (inf_le_right : D.leftSubcomplex ⊓ D.rightSubcomplex ≤ D.rightSubcomplex) =
      supportChainMap (D.left ∪ D.right) D.right (𝟙 D.space)
        (fun _ hx h ↦ hx (Or.inr h)) (𝟙 D.coefficients) ≫
          (supportSingularChainIso D.space D.right D.coefficients).hom := by
  simpa only [unionChainIso, asIso_hom, supportToSubcomplex_refl] using
    supportToSubcomplex_restrict (D.left ∪ D.right) D.right D.coefficients
      Set.subset_union_right D.unionSubcomplex_eq.le le_rfl inf_le_right

/-- The homology comparison intertwines the actual signed support restriction. -/
theorem phi_comparison (D : CompactSupportMVData.{u}) (k : ℕ) :
    (D.unionHomologyIso k).hom ≫ HomologicalComplex.homologyMap D.chainRow.f k =
      D.phiMorphism k ≫ (D.middleHomologyIso k).hom := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k
  apply (cancel_mono (H.mapBiprod
    (D.leftSubcomplex.pair.chainComplex D.coefficients)
    (D.rightSubcomplex.pair.chainComplex D.coefficients)).hom).mp
  change (H.map D.unionChainIso.hom ≫ H.map (biprod.lift
      (subcomplexRelativeMap D.coefficients (inf_le_left : D.leftSubcomplex ⊓ D.rightSubcomplex ≤ D.leftSubcomplex))
      (-subcomplexRelativeMap D.coefficients (inf_le_right : D.leftSubcomplex ⊓ D.rightSubcomplex ≤ D.rightSubcomplex)))) ≫
      (H.mapBiprod _ _).hom =
    (D.phiMorphism k ≫ (ModuleCat.biprodIsoProd _ _).inv ≫
      biprod.map (H.map (supportSingularChainIso D.space D.left D.coefficients).hom)
        (H.map (supportSingularChainIso D.space D.right D.coefficients).hom) ≫
      (H.mapBiprod _ _).inv) ≫ (H.mapBiprod _ _).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, biprod.map_lift_mapBiprod]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst]
    rw [← H.map_comp, D.unionChainIso_left, H.map_comp]
    ext x
    simp [phiMorphism, H, ModuleCat.biprodIsoProd_inv_comp_fst_apply]
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      Functor.map_neg]
    rw [Preadditive.comp_neg, ← H.map_comp, D.unionChainIso_right, H.map_comp]
    ext x
    simp [phiMorphism, supportChainMap, H, ModuleCat.biprodIsoProd_inv_comp_snd_apply]

theorem smallQuotient_left (D : CompactSupportMVData.{u}) :
    (supportSingularChainIso D.space D.left D.coefficients).hom ≫
        subcomplexRelativeMap D.coefficients (le_sup_left : D.leftSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex) ≫
          D.smallQuotientMap =
      supportChainMap D.left (D.left ∩ D.right) (𝟙 D.space)
        (fun _ hx h ↦ hx h.1) (𝟙 D.coefficients) ≫ D.interChainIso.hom := by
  rw [subcomplexRelativeMap_comp]
  simpa only [interChainIso, asIso_hom, supportToSubcomplex_refl] using
    supportToSubcomplex_restrict D.left (D.left ∩ D.right) D.coefficients
      Set.inter_subset_left le_rfl D.interSubcomplex_eq.le _

theorem smallQuotient_right (D : CompactSupportMVData.{u}) :
    (supportSingularChainIso D.space D.right D.coefficients).hom ≫
        subcomplexRelativeMap D.coefficients (le_sup_right : D.rightSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex) ≫
          D.smallQuotientMap =
      supportChainMap D.right (D.left ∩ D.right) (𝟙 D.space)
        (fun _ hx h ↦ hx h.2) (𝟙 D.coefficients) ≫ D.interChainIso.hom := by
  rw [subcomplexRelativeMap_comp]
  simpa only [interChainIso, asIso_hom, supportToSubcomplex_refl] using
    supportToSubcomplex_restrict D.right (D.left ∩ D.right) D.coefficients
      Set.inter_subset_right le_rfl D.interSubcomplex_eq.le _

/-- The homology comparison intertwines the actual sum of restrictions. -/
theorem psi_comparison (D : CompactSupportMVData.{u}) (k : ℕ) :
    (D.middleHomologyIso k).hom ≫ HomologicalComplex.homologyMap D.chainRow.g k =
      D.psiMorphism k ≫ (D.interHomologyIso k).hom := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k
  have : IsIso (H.map D.smallQuotientMap) := D.smallQuotientMap_homology_isIso k
  apply (cancel_mono (HomologicalComplex.homologyMap D.smallQuotientMap k)).mp
  apply (cancel_epi (ModuleCat.biprodIsoProd
    (supportSingularHomology D.space D.left D.coefficients k)
    (supportSingularHomology D.space D.right D.coefficients k)).hom).mp
  change (ModuleCat.biprodIsoProd _ _).hom ≫
    ((ModuleCat.biprodIsoProd _ _).inv ≫
      biprod.map (H.map (supportSingularChainIso D.space D.left D.coefficients).hom)
        (H.map (supportSingularChainIso D.space D.right D.coefficients).hom) ≫
      (H.mapBiprod _ _).inv) ≫
    H.map (biprod.desc (subcomplexRelativeMap D.coefficients (le_sup_left : D.leftSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex))
      (subcomplexRelativeMap D.coefficients (le_sup_right : D.rightSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex))) ≫
      H.map D.smallQuotientMap =
    (ModuleCat.biprodIsoProd _ _).hom ≫ D.psiMorphism k ≫
      (H.map D.interChainIso.hom ≫ (asIso (H.map D.smallQuotientMap)).inv) ≫ H.map D.smallQuotientMap
  have hdesc := biprod.mapBiprod_inv_map_desc H
    (D.leftSubcomplex.pair.chainComplex D.coefficients)
    (D.rightSubcomplex.pair.chainComplex D.coefficients)
    (subcomplexRelativeMap D.coefficients (le_sup_left : D.leftSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex))
    (subcomplexRelativeMap D.coefficients (le_sup_right : D.rightSubcomplex ≤ D.leftSubcomplex ⊔ D.rightSubcomplex))
  simp only [Category.assoc, Iso.hom_inv_id_assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id,
    reassoc_of% hdesc]
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc]
    rw [← H.map_comp, ← H.map_comp, D.smallQuotient_left, H.map_comp]
    ext x
    simp [psiMorphism, H]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc]
    rw [← H.map_comp, ← H.map_comp, D.smallQuotient_right, H.map_comp]
    ext x
    simp [psiMorphism, H]

/-- The connecting morphism on the actual support homology modules. -/
def connectingMorphism (D : CompactSupportMVData.{u}) (k : ℕ) :
    supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (k + 1) ⟶
      supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k :=
  (D.interHomologyIso (k + 1)).hom ≫
    nativeRelativeConnecting D.leftSubcomplex D.rightSubcomplex D.coefficients k ≫
    (D.unionHomologyIso k).inv

/-- The additive connecting homomorphism. -/
def connecting (D : CompactSupportMVData.{u}) (k : ℕ) :
    supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (k + 1) →+
      supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k :=
  (D.connectingMorphism k).hom.toAddMonoidHom

/-- The definition transports the native connecting map. -/
theorem connecting_comparison (D : CompactSupportMVData.{u}) (k : ℕ) :
    (D.interHomologyIso (k + 1)).hom ≫
      nativeRelativeConnecting D.leftSubcomplex D.rightSubcomplex D.coefficients k =
        D.connectingMorphism k ≫ (D.unionHomologyIso k).hom := by
  simp [connectingMorphism]

/-- All three exactness positions of the support sequence follow by transporting
the native short exact chain sequence along the three proven homology comparisons. -/
theorem connecting_exact (D : CompactSupportMVData.{u}) (k : ℕ) :
    Function.Exact (D.connecting k)
      (supportMayerVietorisPhi D.space D.coefficients D.left D.right k) ∧
    Function.Exact (supportMayerVietorisPhi D.space D.coefficients D.left D.right k)
      (supportMayerVietorisPsi D.space D.coefficients D.left D.right k) ∧
    Function.Exact (supportMayerVietorisPsi D.space D.coefficients D.left D.right (k + 1))
      (D.connecting k) := by
  let h := nativeRelativeChainMV_shortExact D.leftSubcomplex D.rightSubcomplex D.coefficients
  refine ⟨?_, ?_, ?_⟩
  · exact moduleExact_of_iso (D.connectingMorphism k) (D.phiMorphism k)
      (ShortComplex.mk _ _ (h.δ_comp (k + 1) k (by simp)))
      (D.interHomologyIso (k + 1)) (D.unionHomologyIso k) (D.middleHomologyIso k)
      (D.connecting_comparison k) (D.phi_comparison k) (h.homology_exact₁ (k + 1) k (by simp))
  · exact moduleExact_of_iso (D.phiMorphism k) (D.psiMorphism k)
      (D.chainRow.map (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k))
      (D.unionHomologyIso k) (D.middleHomologyIso k) (D.interHomologyIso k)
      (D.phi_comparison k) (D.psi_comparison k) (h.homology_exact₂ k)
  · exact moduleExact_of_iso (D.psiMorphism (k + 1)) (D.connectingMorphism k)
      (ShortComplex.mk _ _ (h.comp_δ (k + 1) k (by simp)))
      (D.middleHomologyIso (k + 1)) (D.interHomologyIso (k + 1)) (D.unionHomologyIso k)
      (D.psi_comparison (k + 1)) (D.connecting_comparison k) (h.homology_exact₃ (k + 1) k (by simp))

end CompactSupportMVData
namespace CompactSupportMVMap
open CompactSupportMVData
variable {D E : CompactSupportMVData.{u}}

/-- The map of native quotient short exact sequences induced by a map of support data. -/
def chainRowMap (F : CompactSupportMVMap D E) : D.chainRow ⟶ E.chainRow :=
  nativeRelativeChainMVMap D.coefficients (TopCat.toSSet.map F.ambient)
    (singularSubspace_map_le F.ambient D.leftᶜ E.leftᶜ F.left_complement)
    (singularSubspace_map_le F.ambient D.rightᶜ E.rightᶜ F.right_complement) F.coefficients

theorem unionChain_naturality (F : CompactSupportMVMap D E) :
    D.unionChainIso.hom ≫ F.chainRowMap.τ₁ =
      supportChainMap (D.left ∪ D.right) (E.left ∪ E.right) F.ambient F.unionComplement F.coefficients ≫
        E.unionChainIso.hom :=
  supportToSubcomplex_naturality _ _ F.ambient F.unionComplement F.coefficients
    D.unionSubcomplex_eq.le E.unionSubcomplex_eq.le _

/-- Map on the actual union-of-complements quotient. -/
def interActualMap (F : CompactSupportMVMap D E) :=
  subcomplexRelativeMapOf D.coefficients (TopCat.toSSet.map F.ambient)
    (singularSubspace_map_le F.ambient (D.leftᶜ ∪ D.rightᶜ) (E.leftᶜ ∪ E.rightᶜ)
      (fun _ hx ↦ hx.elim (fun h ↦ Or.inl (F.left_complement h))
        (fun h ↦ Or.inr (F.right_complement h)))) F.coefficients

theorem interChain_naturality (F : CompactSupportMVMap D E) :
    D.interChainIso.hom ≫ F.interActualMap =
      supportChainMap (D.left ∩ D.right) (E.left ∩ E.right) F.ambient F.interComplement F.coefficients ≫
        E.interChainIso.hom :=
  supportToSubcomplex_naturality _ _ F.ambient F.interComplement F.coefficients
    D.interSubcomplex_eq.le E.interSubcomplex_eq.le _

theorem smallQuotient_naturality (F : CompactSupportMVMap D E) :
    D.smallQuotientMap ≫ F.interActualMap = F.chainRowMap.τ₃ ≫ E.smallQuotientMap :=
  subcomplexRelativeMapOf_inclusion D.coefficients (TopCat.toSSet.map F.ambient) _ _ _ _ F.coefficients

theorem unionHomology_naturality (F : CompactSupportMVMap D E) (k : ℕ) :
    (D.unionHomologyIso k).hom ≫ HomologicalComplex.homologyMap F.chainRowMap.τ₁ k =
      HomologicalComplex.homologyMap
        (supportChainMap (D.left ∪ D.right) (E.left ∪ E.right) F.ambient F.unionComplement F.coefficients) k ≫
          (E.unionHomologyIso k).hom := by
  change HomologicalComplex.homologyMap D.unionChainIso.hom k ≫ _ = _ ≫
    HomologicalComplex.homologyMap E.unionChainIso.hom k
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f ↦ HomologicalComplex.homologyMap f k) F.unionChain_naturality

theorem interHomology_naturality (F : CompactSupportMVMap D E) (k : ℕ) :
    (D.interHomologyIso k).hom ≫ HomologicalComplex.homologyMap F.chainRowMap.τ₃ k =
      HomologicalComplex.homologyMap
        (supportChainMap (D.left ∩ D.right) (E.left ∩ E.right) F.ambient F.interComplement F.coefficients) k ≫
          (E.interHomologyIso k).hom := by
  apply (cancel_mono (HomologicalComplex.homologyMap E.smallQuotientMap k)).mp
  change (HomologicalComplex.homologyMap D.interChainIso.hom k ≫
    inv (HomologicalComplex.homologyMap D.smallQuotientMap k) ≫
      HomologicalComplex.homologyMap F.chainRowMap.τ₃ k) ≫
        HomologicalComplex.homologyMap E.smallQuotientMap k =
    (HomologicalComplex.homologyMap
        (supportChainMap (D.left ∩ D.right) (E.left ∩ E.right) F.ambient F.interComplement F.coefficients) k ≫
      HomologicalComplex.homologyMap E.interChainIso.hom k ≫
        inv (HomologicalComplex.homologyMap E.smallQuotientMap k)) ≫
          HomologicalComplex.homologyMap E.smallQuotientMap k
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← HomologicalComplex.homologyMap_comp, ← F.smallQuotient_naturality,
    HomologicalComplex.homologyMap_comp]
  rw [IsIso.inv_hom_id_assoc, ← HomologicalComplex.homologyMap_comp,
    F.interChain_naturality, HomologicalComplex.homologyMap_comp]

/-- Naturality of the transported connecting maps, for the actual space and
coefficient maps in the support data. -/
theorem connecting_naturality (F : CompactSupportMVMap D E) (k : ℕ) :
    (F.unionMap k).comp (D.connecting k) = (E.connecting k).comp (F.interMap (k + 1)) := by
  have hd := HomologicalComplex.HomologySequence.δ_naturality F.chainRowMap
    (nativeRelativeChainMV_shortExact D.leftSubcomplex D.rightSubcomplex D.coefficients)
    (nativeRelativeChainMV_shortExact E.leftSubcomplex E.rightSubcomplex E.coefficients)
    (k + 1) k (by simp)
  have h : D.connectingMorphism k ≫ HomologicalComplex.homologyMap
      (supportChainMap (D.left ∪ D.right) (E.left ∪ E.right) F.ambient F.unionComplement F.coefficients) k =
    HomologicalComplex.homologyMap
      (supportChainMap (D.left ∩ D.right) (E.left ∩ E.right) F.ambient F.interComplement F.coefficients) (k + 1) ≫
        E.connectingMorphism k := by
    apply (cancel_mono (E.unionHomologyIso k).hom).mp
    rw [Category.assoc, ← F.unionHomology_naturality, ← Category.assoc,
      ← D.connecting_comparison, Category.assoc]
    change (D.interHomologyIso (k + 1)).hom ≫
      ((nativeRelativeChainMV_shortExact D.leftSubcomplex D.rightSubcomplex D.coefficients).δ (k + 1) k (by simp)) ≫
        HomologicalComplex.homologyMap F.chainRowMap.τ₁ k = _
    rw [hd, ← Category.assoc, F.interHomology_naturality, Category.assoc]
    have hE := E.connecting_comparison k
    dsimp [nativeRelativeConnecting] at hE
    rw [hE, Category.assoc]
  exact congrArg (fun m ↦ m.hom.toAddMonoidHom) h

end CompactSupportMVMap
end HolomorphicAnosov.Topology
