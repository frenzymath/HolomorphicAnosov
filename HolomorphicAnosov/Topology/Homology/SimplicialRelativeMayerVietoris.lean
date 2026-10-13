import HolomorphicAnosov.Topology.Homology.SimplicialSubcomplexMayerVietoris
import HolomorphicAnosov.Topology.Homology.ShortExactCokernelSequence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology
universe u

variable {X : SSet.{u}} (A B : X.Subcomplex) (R : ModuleCat.{u} ℤ)

/-- The signed diagonal/sum split sequence on ambient chains. -/
def ambientChainMV : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  (show CommSq (𝟙 (X.chainComplex R)) (𝟙 (X.chainComplex R))
    (𝟙 (X.chainComplex R)) (𝟙 (X.chainComplex R)) from ⟨by simp⟩).shortComplex

set_option backward.isDefEq.respectTransparency false in
theorem ambientChainMV_shortExact : (ambientChainMV (X := X) R).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine { r := biprod.fst, s := biprod.inr, f_r := ?_, s_g := ?_, id := ?_ }
  · simp [ambientChainMV, CommSq.shortComplex]
  · simp [ambientChainMV, CommSq.shortComplex]
  · dsimp [ambientChainMV, CommSq.shortComplex]
    apply biprod.hom_ext
    · simp only [Preadditive.add_comp, Category.assoc, biprod.lift_fst,
        Category.comp_id, biprod.inr_fst, comp_zero, add_zero, Category.id_comp]
    · apply biprod.hom_ext' <;> simp

/-- Include the subcomplex chain sequence into the ambient split sequence. -/
def subcomplexChainMVInclusion :
    (subcomplexChainSquare A B R).shortComplex ⟶ ambientChainMV (X := X) R where
  τ₁ := SSet.chainComplexMap (A ⊓ B).ι R
  τ₂ := biprod.map (SSet.chainComplexMap A.ι R) (SSet.chainComplexMap B.ι R)
  τ₃ := SSet.chainComplexMap (A ⊔ B).ι R
  comm₁₂ := by
    dsimp [CommSq.shortComplex, ambientChainMV]
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  comm₂₃ := by
    dsimp [CommSq.shortComplex, ambientChainMV]
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]

/-- The quotient of the subcomplex sequence in the ambient sequence. Its three
terms are the relative chains modulo the intersection, the direct sum of the
two relative complexes, and the relative chains modulo the union subcomplex. -/
abbrev relativeChainMV := cokernel (subcomplexChainMVInclusion A B R)

/-- The relative simplicial Mayer–Vietoris sequence is short exact. The first
row is the chain pushout sequence, the ambient row splits, and the third
vertical map is monic. The snake lemma therefore makes the quotient row short
exact. Source: Hatcher, relative Mayer–Vietoris, pp.152–153. -/
theorem relativeChainMV_shortExact : (relativeChainMV A B R).ShortExact := by
  have : Mono (subcomplexChainMVInclusion A B R).τ₃ :=
    inferInstanceAs (Mono (SSet.chainComplexMap (A ⊔ B).pair.hom R))
  exact shortExact_cokernel_sequence (subcomplexChainMVInclusion A B R)
    (cokernel.π _) (cokernel.condition _) (cokernelIsCokernel _)
    (subcomplexChainSquare_shortExact A B R) (ambientChainMV_shortExact R)


/-- The canonical projection from the ambient split row to its quotient row. -/
abbrev relativeChainMVπ := cokernel.π (subcomplexChainMVInclusion A B R)

/-- Cokernel comparison for the intersection term. -/
def relativeChainMVFirstIso : (relativeChainMV A B R).X₁ ≅
    (A ⊓ B).pair.chainComplex R :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₁
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).coconePointUniqueUpToIso
      ((A ⊓ B).pair.isColimitCokernelCoforkChainComplex R)

/-- Cokernel comparison for the union subcomplex term. -/
def relativeChainMVLastIso : (relativeChainMV A B R).X₃ ≅
    (A ⊔ B).pair.chainComplex R :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₃
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).coconePointUniqueUpToIso
      ((A ⊔ B).pair.isColimitCokernelCoforkChainComplex R)

/-- Cokernel comparison for the direct sum of the two relative complexes. -/
def relativeChainMVMiddleIso : (relativeChainMV A B R).X₂ ≅
    A.pair.chainComplex R ⊞ B.pair.chainComplex R :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₂
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).coconePointUniqueUpToIso
      (biprodCokernelIsColimit (A.pair.chainComplex_condition R)
        (B.pair.chainComplex_condition R) (A.pair.isColimitCokernelCoforkChainComplex R)
        (B.pair.isColimitCokernelCoforkChainComplex R))

@[reassoc (attr := simp)]
theorem relativeChainMVFirstIso_projection : (relativeChainMVπ A B R).τ₁ ≫
    (relativeChainMVFirstIso A B R).hom = (A ⊓ B).pair.chainComplexπ R :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₁
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).comp_coconePointUniqueUpToIso_hom
    ((A ⊓ B).pair.isColimitCokernelCoforkChainComplex R) WalkingParallelPair.one

@[reassoc (attr := simp)]
theorem relativeChainMVLastIso_projection : (relativeChainMVπ A B R).τ₃ ≫
    (relativeChainMVLastIso A B R).hom = (A ⊔ B).pair.chainComplexπ R :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₃
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).comp_coconePointUniqueUpToIso_hom
    ((A ⊔ B).pair.isColimitCokernelCoforkChainComplex R) WalkingParallelPair.one

@[reassoc (attr := simp)]
theorem relativeChainMVMiddleIso_projection : (relativeChainMVπ A B R).τ₂ ≫
    (relativeChainMVMiddleIso A B R).hom =
      biprod.map (A.pair.chainComplexπ R) (B.pair.chainComplexπ R) :=
  (isColimitCoforkMapOfIsColimit' ShortComplex.π₂
    (cokernel.condition (subcomplexChainMVInclusion A B R))
    (cokernelIsCokernel (subcomplexChainMVInclusion A B R))).comp_coconePointUniqueUpToIso_hom
    (biprodCokernelIsColimit (A.pair.chainComplex_condition R)
      (B.pair.chainComplex_condition R) (A.pair.isColimitCokernelCoforkChainComplex R)
      (B.pair.isColimitCokernelCoforkChainComplex R)) WalkingParallelPair.one


/-- The map of relative chains for an inclusion of subcomplexes. -/
abbrev subcomplexRelativeMap {A B : X.Subcomplex} (h : A ≤ B) :
    A.pair.chainComplex R ⟶ B.pair.chainComplex R :=
  SSetPair.chainComplexMap (SSetPair.homMk (X := A.pair) (Y := B.pair) (SSet.Subcomplex.homOfLE h) (𝟙 X)
    (by rfl)) R

@[reassoc (attr := simp)]
theorem subcomplexRelativeMap_projection {A B : X.Subcomplex} (h : A ≤ B) :
    A.pair.chainComplexπ R ≫ subcomplexRelativeMap R h = B.pair.chainComplexπ R := by
  have hn := ((((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality
    (SSetPair.homMk (X := A.pair) (Y := B.pair) (SSet.Subcomplex.homOfLE h) (𝟙 X) (by rfl)))).symm
  change A.pair.chainComplexπ R ≫ subcomplexRelativeMap R h =
    SSet.chainComplexMap (𝟙 X) R ≫ B.pair.chainComplexπ R at hn
  simpa using hn

@[reassoc (attr := simp)]
theorem subcomplexRelativeMap_comp {A B C : X.Subcomplex} (h : A ≤ B) (h' : B ≤ C) :
    subcomplexRelativeMap R h ≫ subcomplexRelativeMap R h' =
      subcomplexRelativeMap R (h.trans h') := by
  rw [← Functor.map_comp]
  rfl

/-- The concrete signed relative simplicial chain sequence. -/
def nativeRelativeChainMV : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk
    (biprod.lift (subcomplexRelativeMap R (inf_le_left : A ⊓ B ≤ A))
      (-subcomplexRelativeMap R (inf_le_right : A ⊓ B ≤ B)))
    (biprod.desc (subcomplexRelativeMap R (le_sup_left : A ≤ A ⊔ B))
      (subcomplexRelativeMap R (le_sup_right : B ≤ A ⊔ B))) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The categorical cokernel row is the native relative chain row. -/
def relativeChainMVIso : relativeChainMV A B R ≅ nativeRelativeChainMV A B R := by
  have : Epi (relativeChainMVπ A B R).τ₁ :=
    inferInstanceAs (Epi (ShortComplex.π₁.map (cokernel.π (subcomplexChainMVInclusion A B R))))
  have : Epi (relativeChainMVπ A B R).τ₂ :=
    inferInstanceAs (Epi (ShortComplex.π₂.map (cokernel.π (subcomplexChainMVInclusion A B R))))
  refine ShortComplex.isoMk (relativeChainMVFirstIso A B R)
    (relativeChainMVMiddleIso A B R) (relativeChainMVLastIso A B R) ?_ ?_
  · apply (cancel_epi (relativeChainMVπ A B R).τ₁).mp
    simp only [← Category.assoc, relativeChainMVFirstIso_projection,
      (relativeChainMVπ A B R).comm₁₂]
    rw [Category.assoc, relativeChainMVMiddleIso_projection]
    dsimp [ambientChainMV, CommSq.shortComplex, nativeRelativeChainMV]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst]
      erw [subcomplexRelativeMap_projection, ← Category.assoc, biprod.lift_fst (𝟙 (X.chainComplex R)) (-𝟙 (X.chainComplex R)), Category.id_comp]
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, Preadditive.comp_neg]
      erw [subcomplexRelativeMap_projection, ← Category.assoc, biprod.lift_snd (𝟙 (X.chainComplex R)) (-𝟙 (X.chainComplex R))]
      simp
  · apply (cancel_epi (relativeChainMVπ A B R).τ₂).mp
    simp only [← Category.assoc, relativeChainMVMiddleIso_projection,
      (relativeChainMVπ A B R).comm₂₃]
    rw [Category.assoc, relativeChainMVLastIso_projection]
    dsimp [ambientChainMV, CommSq.shortComplex, nativeRelativeChainMV]
    apply biprod.hom_ext' <;> simp

/-- The native relative simplicial Mayer–Vietoris chain sequence is short exact. -/
theorem nativeRelativeChainMV_shortExact : (nativeRelativeChainMV A B R).ShortExact :=
  ShortComplex.shortExact_of_iso (relativeChainMVIso A B R) (relativeChainMV_shortExact A B R)


/-- Homology connecting maps for the native relative Mayer–Vietoris sequence.
For complement subcomplexes, the source represents intersection support and
the target represents union support. -/
def nativeRelativeConnecting (k : ℕ) :
    (A ⊔ B).pair.homology R (k + 1) ⟶ (A ⊓ B).pair.homology R k :=
  (nativeRelativeChainMV_shortExact A B R).δ (k + 1) k (by simp)

section Naturality
variable {Y : SSet.{u}} {R' : ModuleCat.{u} ℤ}

/-- A simplicial map carrying a subcomplex into another defines a map of pairs. -/
def subcomplexPairMap {A : X.Subcomplex} {B : Y.Subcomplex} (f : X ⟶ Y)
    (h : A ≤ B.preimage f) : A.pair ⟶ B.pair :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE h ≫ B.fromPreimage f) f (by rfl)

/-- The chain map with both a simplicial and a coefficient component. -/
def subcomplexRelativeMapOf {A : X.Subcomplex} {B : Y.Subcomplex} (f : X ⟶ Y)
    (h : A ≤ B.preimage f) (γ : R ⟶ R') : A.pair.chainComplex R ⟶ B.pair.chainComplex R' :=
  (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app A.pair) ≫
    SSetPair.chainComplexMap (subcomplexPairMap f h) R'

/-- The corresponding absolute chain map. -/
def ambientChainMapOf (f : X ⟶ Y) (γ : R ⟶ R') : X.chainComplex R ⟶ Y.chainComplex R' :=
  (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app X) ≫ SSet.chainComplexMap f R'

@[reassoc (attr := simp)]
theorem subcomplexRelativeMapOf_projection {A : X.Subcomplex} {B : Y.Subcomplex}
    (f : X ⟶ Y) (h : A ≤ B.preimage f) (γ : R ⟶ R') :
    A.pair.chainComplexπ R ≫ subcomplexRelativeMapOf R f h γ =
      ambientChainMapOf R f γ ≫ B.pair.chainComplexπ R' := by
  dsimp [subcomplexRelativeMapOf, ambientChainMapOf]
  rw [← Category.assoc]
  have hc := congrArg (fun t ↦ t.app A.pair)
    ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).naturality γ)
  have hp := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R').naturality
    (subcomplexPairMap f h))
  change (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map γ).app X) ≫
    A.pair.chainComplexπ R' = A.pair.chainComplexπ R ≫ _ at hc
  change SSet.chainComplexMap f R' ≫ B.pair.chainComplexπ R' =
    A.pair.chainComplexπ R' ≫ SSetPair.chainComplexMap (subcomplexPairMap f h) R' at hp
  rw [← hc, Category.assoc, ← hp, Category.assoc]

@[reassoc]
theorem subcomplexRelativeMapOf_inclusion {A A' : X.Subcomplex} {B B' : Y.Subcomplex}
    (f : X ⟶ Y) (h : A ≤ B.preimage f) (h' : A' ≤ B'.preimage f)
    (ha : A ≤ A') (hb : B ≤ B') (γ : R ⟶ R') :
    subcomplexRelativeMap R ha ≫ subcomplexRelativeMapOf R f h' γ =
      subcomplexRelativeMapOf R f h γ ≫ subcomplexRelativeMap R' hb := by
  apply (cancel_epi (A.pair.chainComplexπ R)).mp
  simp only [← Category.assoc, subcomplexRelativeMap_projection,
    subcomplexRelativeMapOf_projection]
  simp only [Category.assoc, subcomplexRelativeMap_projection]

/-- Naturality of the signed relative Mayer–Vietoris chain sequence. -/
def nativeRelativeChainMVMap {A B : X.Subcomplex} {A' B' : Y.Subcomplex}
    (f : X ⟶ Y) (ha : A ≤ A'.preimage f) (hb : B ≤ B'.preimage f)
    (γ : R ⟶ R') : nativeRelativeChainMV A B R ⟶ nativeRelativeChainMV A' B' R' where
  τ₁ := subcomplexRelativeMapOf R f (inf_le_inf ha hb) γ
  τ₂ := biprod.map (subcomplexRelativeMapOf R f ha γ) (subcomplexRelativeMapOf R f hb γ)
  τ₃ := subcomplexRelativeMapOf R f (sup_le_sup ha hb) γ
  comm₁₂ := by
    dsimp [nativeRelativeChainMV]
    apply biprod.hom_ext <;> simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
      Preadditive.neg_comp, Preadditive.comp_neg]
    · exact (subcomplexRelativeMapOf_inclusion R f (inf_le_inf ha hb) ha inf_le_left inf_le_left γ).symm
    · exact congrArg Neg.neg
        (subcomplexRelativeMapOf_inclusion R f (inf_le_inf ha hb) hb inf_le_right inf_le_right γ).symm
  comm₂₃ := by
    dsimp [nativeRelativeChainMV]
    apply biprod.hom_ext' <;> simp only [biprod.inl_map_assoc,
      biprod.inr_map_assoc, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc]
    · exact (subcomplexRelativeMapOf_inclusion R f ha (sup_le_sup ha hb) le_sup_left le_sup_left γ).symm
    · exact (subcomplexRelativeMapOf_inclusion R f hb (sup_le_sup ha hb) le_sup_right le_sup_right γ).symm

end Naturality
end HolomorphicAnosov.Topology
