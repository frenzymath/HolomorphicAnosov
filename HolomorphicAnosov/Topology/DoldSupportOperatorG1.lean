import HolomorphicAnosov.Topology.Cubical.FiniteCubicalCompactNeighborhoodG1
import HolomorphicAnosov.Topology.Cubical.CoordinateCellBoundaryCompact
import HolomorphicAnosov.Topology.Cubical.FiniteCellUnionCompact
import HolomorphicAnosov.Topology.Cubical.SkeletonHomologyNeighborhoods
import Mathlib.Geometry.Manifold.Instances.Sphere
import HolomorphicAnosov.Topology.Homology.EmptySingularChainComplex
import HolomorphicAnosov.Topology.EuclideanConstantFixedPointIndexOneTranslation
import HolomorphicAnosov.Topology.DiskDegreePairHomotopy
import HolomorphicAnosov.Topology.InvertibleLinearLocalHomologyAction
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsHomologyNaturality
import HolomorphicAnosov.Topology.Homology.RationalRelativeKunneth
import HolomorphicAnosov.Topology.Homology.EuclideanLocalHomologyProfile
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import HolomorphicAnosov.Topology.ENRRetractionRepresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Dold’s compact support operator identity

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), (4.2)--(4.4), pp.5--6, and §5, pp.6--8.
The homology theory below is explicitly ordinary rational singular homology.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace HolomorphicAnosov.FixedPointIndexInterface

universe u

namespace DoldConstruction

variable {V : Type u} [NormedAddCommGroup V] (U K : Set V)

/-- The support complement in the original open domain. -/
abbrev supportComplement : Set U := {v | v.val ∉ K}

/-- The graph map into the product with the compact image. -/
def graph (g : C(U, K)) : C(U, U × K) :=
  ⟨fun v ↦ (v, g v), continuous_id.prodMk g.continuous⟩

/-- The literal difference map used in Dold (4.3). -/
def difference : C(U × K, V) :=
  ⟨fun v ↦ v.1.val - v.2.val,
    (continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)⟩

/-- Off the support in the first factor, the difference never vanishes. -/
lemma difference_mapsTo : Set.MapsTo (difference U K)
    {v : U × K | v.1.val ∉ K} ({0} : Set V)ᶜ := by
  intro v hv hzero
  have heq : v.1.val = v.2.val := sub_eq_zero.mp hzero
  exact hv (heq ▸ v.2.property)

/-- The graph is a map of the original support pair to its product pair. -/
def graphPairMap (g : C(U, K)) :
    singularSubspacePair (TopCat.of U) (supportComplement U K) ⟶
      singularSubspacePair (TopCat.of (U × K)) {v | v.1.val ∉ K} :=
  singularSubspacePairMap (TopCat.ofHom (graph U K g)) _ _ (fun _ hv ↦ hv)

/-- Difference as a map to the punctured ambient pair. -/
def differencePairMap :
    singularSubspacePair (TopCat.of (U × K)) {v | v.1.val ∉ K} ⟶
      singularSubspacePair (TopCat.of V) ({0} : Set V)ᶜ :=
  singularSubspacePairMap (TopCat.ofHom (difference U K)) _ _ (difference_mapsTo U K)

/-- The displacement on the original domain, with Dold's sign convention. -/
def displacement (g : C(U, K)) : C(U, V) :=
  (difference U K).comp (graph U K g)

/-- Displacement is a map of pairs already off the compact image, before restricting
support further to the fixed set. -/
def displacementPairMap (g : C(U, K)) :
    singularSubspacePair (TopCat.of U) (supportComplement U K) ⟶
      singularSubspacePair (TopCat.of V) ({0} : Set V)ᶜ :=
  singularSubspacePairMap (TopCat.ofHom (displacement U K g)) _ _
    (fun v hv ↦ difference_mapsTo U K (show (graph U K g v).1.val ∉ K from hv))

/-- The outer path in Dold's first diagram is the literal displacement map. -/
lemma graph_difference (g : C(U, K)) :
    graphPairMap U K g ≫ differencePairMap U K = displacementPairMap U K g := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl

/-- Functoriality gives the commuting displacement triangle on ordinary homology,
with any module of coefficients and in every degree. -/
lemma graph_difference_homology {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    (g : C(U, K)) (n : ℕ) :
    SSetPair.homologyMap (graphPairMap U K g) M n ≫
      SSetPair.homologyMap (differencePairMap U K) M n =
        SSetPair.homologyMap (displacementPairMap U K g) M n := by
  rw [← SSetPair.homologyMap_comp, graph_difference]

/-- Dold's diagonal, transposition, and difference composite on actual points. -/
def supportMap : C(U × K, V × U) :=
  ⟨fun v ↦ (v.1.val - v.2.val, v.1),
    (difference U K).continuous.prodMk continuous_fst⟩

/-- The support operator before dividing by the positive local class. -/
def supportPairMap :
    singularSubspacePair (TopCat.of (U × K)) {v | v.1.val ∉ K} ⟶
      singularSubspacePair (TopCat.of (V × U)) {v | v.1 ≠ 0} :=
  singularSubspacePairMap (TopCat.ofHom (supportMap U K)) _ _
    (fun _ hv ↦ difference_mapsTo U K hv)

/-- The diagonal is relative only in its first coordinate. -/
def diagonalPairMap :
    singularSubspacePair (TopCat.of U) (supportComplement U K) ⟶
      singularSubspacePair (TopCat.of (U × U)) {v | v.1.val ∉ K} :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨fun v : U ↦ (v, v), continuous_id.prodMk continuous_id⟩) _ _
    (fun _ hv ↦ hv)

/-- Applying the compact-image map in the second factor. -/
def secondFactorPairMap (g : C(U, K)) :
    singularSubspacePair (TopCat.of (U × U)) {v | v.1.val ∉ K} ⟶
      singularSubspacePair (TopCat.of (U × K)) {v | v.1.val ∉ K} :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨fun v : U × U ↦ (v.1, g v.2),
      continuous_fst.prodMk (g.continuous.comp continuous_snd)⟩) _ _ (fun _ hv ↦ hv)

/-- The diagonal followed by the second-factor map is the graph in Dold (4.3). -/
lemma diagonal_secondFactor (g : C(U, K)) :
    diagonalPairMap U K ≫ secondFactorPairMap U K g = graphPairMap U K g := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl

/-- Dold's diagonal, compact-image map, and difference are the literal displacement. -/
lemma diagonal_difference (g : C(U, K)) :
    diagonalPairMap U K ≫ secondFactorPairMap U K g ≫ differencePairMap U K =
      displacementPairMap U K g := by
  rw [← Category.assoc, diagonal_secondFactor, graph_difference]

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

instance extendScalars_additive : (ModuleCat.extendScalars.{0, 0, u} f).Additive where
  map_add := by
    intro M N a b
    let := f.toAlgebra
    apply ModuleCat.hom_ext
    change (a.hom + b.hom).baseChange S = a.hom.baseChange S + b.hom.baseChange S
    exact LinearMap.baseChange_add (A := S) a.hom b.hom

/-- Flat scalar extension preserves exact short complexes in every carrier universe. -/
lemma extendScalars_exact
    (hflat : @Module.Flat R S _ _ (Module.compHom S f))
    (C : ShortComplex (ModuleCat.{u} R)) (hC : C.Exact) :
    (C.map (ModuleCat.extendScalars f)).Exact := by
  let := Module.compHom S f
  let : Module.Flat R S := hflat
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

/-- Consequently flat extension preserves homology without a finite generation guard. -/
lemma extendScalars_preservesHomology
    (hflat : @Module.Flat R S _ _ (Module.compHom S f)) :
    Functor.PreservesHomology (ModuleCat.extendScalars.{0, 0, u} f) := by
  exact ((Functor.exact_tfae (ModuleCat.extendScalars f)).out 2 3).mp
    (extendScalars_exact f hflat)

/-- Extension of scalars commutes with the actual quotient defining relative chains. -/
def extendScalarsRelativeChainIso (P : SSetPair.{u}) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.down ℕ)).obj
        (P.chainComplex M) ≅ P.chainComplex ((ModuleCat.extendScalars f).obj M) := by
  let F := ModuleCat.extendScalars.{0, 0, u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := SSet.chainComplexFunctorObjCompMapIso F M
  exact CokernelCofork.mapIsoOfIsColimit
    (CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex M) G)
    (P.isColimitCokernelCoforkChainComplex (F.obj M))
    (Arrow.isoMk (e.app P.left) (e.app P.right) (e.hom.naturality P.hom).symm)

/-- The rational universal coefficient comparison is the flat special case of this
isomorphism. It concerns the original relative homology, in every degree. -/
def extendScalarsRelativeHomologyIso
    (hflat : @Module.Flat R S _ _ (Module.compHom S f))
    (P : SSetPair.{u}) (M : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (P.homology M n) ≅
      P.homology ((ModuleCat.extendScalars f).obj M) n := by
  let F := ModuleCat.extendScalars.{0, 0, u} f
  have : Functor.PreservesHomology F := extendScalars_preservesHomology f hflat
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := extendScalarsRelativeChainIso f P M
  exact ((P.chainComplex M).sc n |>.mapHomologyIso F).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso (ModuleCat S) (.down ℕ) n).app
      (G.obj (P.chainComplex M))).symm ≪≫
    HomologicalComplex.homologyMapIso e n

/-- The integral coefficient unit extends to the prescribed rational coefficient unit. -/
def rationalExtensionCoefficientIso :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      ModuleCat.of ℚ (ULift.{u} ℚ) := by
  let e : ℚ ⊗[ℤ] ULift.{u} ℤ ≃ₗ[ℚ] ULift.{u} ℚ :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
      (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ)).trans
        ((TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).trans ULift.moduleEquiv.symm)
  exact e.toModuleIso

/-- Ordinary rational relative homology is flat scalar extension of the ordinary
integral relative homology; no finite-generation hypothesis is required. -/
def rationalRelativeHomologyIso (P : SSetPair.{u}) (n : ℕ) :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj
      (P.homology (ModuleCat.of ℤ (ULift.{u} ℤ)) n) ≅
    P.homology (ModuleCat.of ℚ (ULift.{u} ℚ)) n := by
  have hflat : @Module.Flat ℤ ℚ _ _ (Module.compHom ℚ (Int.castRingHom ℚ)) :=
    IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact extendScalarsRelativeHomologyIso (Int.castRingHom ℚ) hflat P _ n ≪≫
    HomologicalComplex.homologyMapIso
      (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℚ)).mapIso
        rationalExtensionCoefficientIso).app P) n

theorem extendScalarsRelativeChainIso_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {P Q : SSetPair.{u}} (g : P ⟶ Q) (V : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.down ℕ)).map (P.chainComplexMap g V) ≫
      (extendScalarsRelativeChainIso f Q V).hom =
    (extendScalarsRelativeChainIso f P V).hom ≫
      P.chainComplexMap g ((ModuleCat.extendScalars f).obj V) := by
  let F := ModuleCat.extendScalars.{0, 0, u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := SSet.chainComplexFunctorObjCompMapIso F V
  apply Cofork.IsColimit.hom_ext
    (CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex V) G)
  change G.map (P.chainComplexπ V) ≫ G.map (SSetPair.chainComplexMap g V) ≫ _ =
    G.map (P.chainComplexπ V) ≫ _ ≫ _
  have hp := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} R)).app V).naturality g
  change SSet.chainComplexMap g.hom.right V ≫ Q.chainComplexπ V =
    P.chainComplexπ V ≫ SSetPair.chainComplexMap g V at hp
  rw [← Category.assoc, ← G.map_comp, ← hp, G.map_comp, Category.assoc]
  have hQ := CokernelCofork.π_mapOfIsColimit
    ((Q.cokernelCoforkChainComplex V).mapIsColimit
      (Q.isColimitCokernelCoforkChainComplex V) G)
    (Q.cokernelCoforkChainComplex (F.obj V))
    (Arrow.isoMk (e.app Q.left) (e.app Q.right)
      (e.hom.naturality Q.hom).symm).hom
  have hP := CokernelCofork.π_mapOfIsColimit
    ((P.cokernelCoforkChainComplex V).mapIsColimit
      (P.isColimitCokernelCoforkChainComplex V) G)
    (P.cokernelCoforkChainComplex (F.obj V))
    (Arrow.isoMk (e.app P.left) (e.app P.right)
      (e.hom.naturality P.hom).symm).hom
  have hQ' : G.map (Q.chainComplexπ V) ≫
      (extendScalarsRelativeChainIso f Q V).hom =
      (e.app Q.right).hom ≫ Q.chainComplexπ (F.obj V) := by
    dsimp [extendScalarsRelativeChainIso]
    change G.map (Cofork.π (Q.cokernelCoforkChainComplex V)) ≫ _ = _
    rw [← CokernelCofork.map_π]
    exact hQ
  have hP' : G.map (P.chainComplexπ V) ≫
      (extendScalarsRelativeChainIso f P V).hom =
      (e.app P.right).hom ≫ P.chainComplexπ (F.obj V) := by
    dsimp [extendScalarsRelativeChainIso]
    change G.map (Cofork.π (P.cokernelCoforkChainComplex V)) ≫ _ = _
    rw [← CokernelCofork.map_π]
    exact hP
  rw [hQ']
  rw [← Category.assoc (G.map (P.chainComplexπ V)), hP']
  simp only [Category.assoc]
  change G.map (SSet.chainComplexMap g.hom.right V) ≫ (e.app Q.right).hom ≫
    Q.chainComplexπ (F.obj V) = (e.app P.right).hom ≫
    P.chainComplexπ (F.obj V) ≫ SSetPair.chainComplexMap g (F.obj V)
  have he := e.hom.naturality g.hom.right
  change G.map (SSet.chainComplexMap g.hom.right V) ≫ (e.app Q.right).hom =
    (e.app P.right).hom ≫ SSet.chainComplexMap g.hom.right (F.obj V) at he
  rw [← Category.assoc, he]
  rw [← Category.assoc]
  exact congrArg ((e.app P.right).hom ≫ ·)
    (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} S)).app (F.obj V)).naturality g)

theorem extendScalarsRelativeHomologyIso_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : @Module.Flat R S _ _ (Module.compHom S f)) {P Q : SSetPair.{u}} (g : P ⟶ Q) (V : ModuleCat.{u} R) (n : ℕ)
    :
    (ModuleCat.extendScalars f).map (SSetPair.homologyMap g V n) ≫
        (extendScalarsRelativeHomologyIso f hflat Q V n).hom =
      (extendScalarsRelativeHomologyIso f hflat P V n).hom ≫
        SSetPair.homologyMap g ((ModuleCat.extendScalars f).obj V) n := by
  have : Functor.PreservesHomology (ModuleCat.extendScalars.{0, 0, u} f) :=
    extendScalars_preservesHomology f hflat
  have hnat := extendScalarsRelativeChainIso_naturality f g V
  let F := ModuleCat.extendScalars.{0, 0, u} f
  let G := F.mapHomologicalComplex (.down ℕ)
  let φ := SSetPair.chainComplexMap g V
  let ψ := SSetPair.chainComplexMap g (F.obj V)
  let eP := extendScalarsRelativeChainIso f P V
  let eQ := extendScalarsRelativeChainIso f Q V
  let t := HomologicalComplex.homologyFunctorIso (ModuleCat.{u} S) (.down ℕ) n
  change F.map (HomologicalComplex.homologyMap φ n) ≫
      (extendScalarsRelativeHomologyIso f hflat Q V n).hom =
    (extendScalarsRelativeHomologyIso f hflat P V n).hom ≫
      HomologicalComplex.homologyMap ψ n
  have ha := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.down ℕ) n).map φ) F
  have hb := t.inv.naturality (G.map φ)
  have hc := congrArg (fun k ↦ HomologicalComplex.homologyMap k n) hnat
  simp only [HomologicalComplex.homologyMap_comp] at hc
  change G.map φ ≫ eQ.hom = eP.hom ≫ ψ at hnat
  have hc' : HomologicalComplex.homologyMap (G.map φ) n ≫
      HomologicalComplex.homologyMap eQ.hom n =
      HomologicalComplex.homologyMap eP.hom n ≫ HomologicalComplex.homologyMap ψ n := by
    simpa only [← HomologicalComplex.homologyMap_comp] using hc
  change F.map (HomologicalComplex.homologyMap φ n) ≫
      (((Q.chainComplex V).sc n).mapHomologyIso F).inv ≫
      (t.app (G.obj (Q.chainComplex V))).inv ≫
      HomologicalComplex.homologyMap eQ.hom n =
    (((P.chainComplex V).sc n).mapHomologyIso F).inv ≫
      (t.app (G.obj (P.chainComplex V))).inv ≫
      HomologicalComplex.homologyMap eP.hom n ≫ HomologicalComplex.homologyMap ψ n
  have ha' : F.map (HomologicalComplex.homologyMap φ n) ≫
      (((Q.chainComplex V).sc n).mapHomologyIso F).inv =
    (((P.chainComplex V).sc n).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap
        (F.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.down ℕ) n).map φ)) := ha
  erw [← Category.assoc, ha']
  have hb' : ShortComplex.homologyMap
      (F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.down ℕ) n).map φ)) ≫
      (t.app (G.obj (Q.chainComplex V))).inv =
      (t.app (G.obj (P.chainComplex V))).inv ≫
        HomologicalComplex.homologyMap (G.map φ) n := hb
  erw [Category.assoc]
  erw [← Category.assoc (ShortComplex.homologyMap _), hb']
  erw [Category.assoc, Category.assoc, hc']
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Naturality of flat rationalization in the original pair variable. -/
lemma rationalRelativeHomologyIso_naturality {P Q : SSetPair.{u}} (g : P ⟶ Q) (n : ℕ) :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).map
      (SSetPair.homologyMap g (ModuleCat.of ℤ (ULift.{u} ℤ)) n) ≫
        (rationalRelativeHomologyIso Q n).hom =
      (rationalRelativeHomologyIso P n).hom ≫
        SSetPair.homologyMap g (ModuleCat.of ℚ (ULift.{u} ℚ)) n := by
  have hflat : @Module.Flat ℤ ℚ _ _ (Module.compHom ℚ (Int.castRingHom ℚ)) :=
    IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have ha := extendScalarsRelativeHomologyIso_naturality (Int.castRingHom ℚ)
    hflat g (ModuleCat.of ℤ (ULift.{u} ℤ)) n
  have hc := (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℚ)).map
    rationalExtensionCoefficientIso.hom).naturality g)
  have hh := congrArg (fun k ↦ HomologicalComplex.homologyMap k n) hc
  simp only [HomologicalComplex.homologyMap_comp] at hh
  unfold rationalRelativeHomologyIso
  simp only [Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [← Category.assoc, ha, Category.assoc]
  exact congrArg (_ ≫ ·) hh

abbrev integralCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
abbrev rationalCoefficients : ModuleCat.{u} ℚ := ModuleCat.of ℚ (ULift.{u} ℚ)
abbrev rationalRestriction := ModuleCat.restrictScalars.{u} (Int.castRingHom ℚ)

/-- The coefficient passage factors through the canonical unit of flat scalar extension. -/
def rationalize (P : SSetPair.{u}) (n : ℕ) :
    P.homology integralCoefficients n ⟶
      rationalRestriction.obj (P.homology rationalCoefficients n) :=
  (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).unit.app
    (P.homology integralCoefficients n) ≫
    rationalRestriction.map (rationalRelativeHomologyIso P n).hom

set_option backward.isDefEq.respectTransparency false in
lemma rationalize_naturality {P Q : SSetPair.{u}} (g : P ⟶ Q) (n : ℕ) :
    SSetPair.homologyMap g integralCoefficients n ≫ rationalize Q n =
      rationalize P n ≫ rationalRestriction.map
        (SSetPair.homologyMap g rationalCoefficients n) := by
  have hn := (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).unit.naturality
    (SSetPair.homologyMap g integralCoefficients n)
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hi := congrArg rationalRestriction.map (rationalRelativeHomologyIso_naturality g n)
  simp only [Functor.map_comp] at hi
  unfold rationalize
  change SSetPair.homologyMap g integralCoefficients n ≫
      (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).unit.app _ ≫ _ = _
  erw [← Category.assoc, hn, Category.assoc, hi, ← Category.assoc]

/-- Evaluating rationalization is the ordinary tensor-unit inclusion. -/
lemma rationalize_apply (P : SSetPair.{u}) (n : ℕ)
    (a : ↥(P.homology integralCoefficients n)) :
    (rationalize P n).hom a =
      (rationalRelativeHomologyIso P n).hom.hom ((1 : ℚ) ⊗ₜ[ℤ] a) := rfl

/-- The rational extension of an integral coordinate reads the rational cast of
that coordinate on classes coming from integral homology. -/
def extendIntegralCoordinate {P : SSetPair.{u}} {n : ℕ}
    (e : ↥(P.homology integralCoefficients n) ≃ₗ[ℤ] ℤ) :
    ↥(P.homology rationalCoefficients n) ≃ₗ[ℚ] ℚ :=
  ((rationalRelativeHomologyIso _ n).symm ≪≫
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).mapIso
      (e.trans (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).symm).toModuleIso ≪≫
    rationalExtensionCoefficientIso).toLinearEquiv.trans ULift.moduleEquiv

set_option backward.isDefEq.respectTransparency false in
lemma extendIntegralCoordinate_rationalize {P : SSetPair.{u}} {n : ℕ}
    (e : ↥(P.homology integralCoefficients n) ≃ₗ[ℤ] ℤ)
    (a : ↥(P.homology integralCoefficients n)) :
    extendIntegralCoordinate e ((rationalize P n).hom a) = (e a : ℚ) := by
  rw [rationalize_apply]
  change (rationalExtensionCoefficientIso.hom.hom
    (((ModuleCat.extendScalars (Int.castRingHom ℚ)).map
      (e.trans (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).symm).toModuleIso.hom).hom
      ((rationalRelativeHomologyIso P n).inv.hom
        ((rationalRelativeHomologyIso P n).hom.hom ((1 : ℚ) ⊗ₜ[ℤ] a))))).down = _
  have hh := congrArg (fun k ↦ k.hom ((1 : ℚ) ⊗ₜ[ℤ] a))
    (rationalRelativeHomologyIso P n).hom_inv_id
  change (rationalRelativeHomologyIso P n).inv.hom
    ((rationalRelativeHomologyIso P n).hom.hom ((1 : ℚ) ⊗ₜ[ℤ] a)) = _ at hh
  rw [hh]
  change (e a : ℤ) • (1 : ℚ) = _
  simp

/-- An integral homology coefficient is carried to its rational cast under the
same map of pairs. This is the coefficient passage used in Dold (4.3). -/
lemma rationalize_coefficient {P Q : SSetPair.{u}} (f : P ⟶ Q) (n : ℕ)
    (a : ↥(P.homology integralCoefficients n)) (ω : ↥(Q.homology integralCoefficients n))
    (z : ℤ) (h : (SSetPair.homologyMap f integralCoefficients n).hom a = z • ω) :
    (SSetPair.homologyMap f rationalCoefficients n).hom ((rationalize P n).hom a) =
      (z : ℚ) • (rationalize Q n).hom ω := by
  have hn := congrArg (fun k ↦ k.hom a) (rationalize_naturality f n)
  change (rationalize Q n).hom ((SSetPair.homologyMap f integralCoefficients n).hom a) =
    (SSetPair.homologyMap f rationalCoefficients n).hom ((rationalize P n).hom a) at hn
  rw [h] at hn
  have hz := (rationalize Q n).hom.map_smul z ω
  have hcast : (rationalize Q n).hom (z • ω) =
      (z : ℚ) • (rationalize Q n).hom ω := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ ↥(Q.homology integralCoefficients n))]
    exact hz
  exact hn.symm.trans hcast

/-- Any equality of integral classes induced by a map of pairs remains true after
rationalization. Applied to support restriction and domain inclusion, this transports
the already proved naturality of the prescribed integral orientation. -/
lemma rationalize_map_eq {P Q : SSetPair.{u}} (f : P ⟶ Q) (n : ℕ)
    (a : ↥(P.homology integralCoefficients n))
    (b : ↥(Q.homology integralCoefficients n))
    (h : (SSetPair.homologyMap f integralCoefficients n).hom a = b) :
    (SSetPair.homologyMap f rationalCoefficients n).hom ((rationalize P n).hom a) =
      (rationalize Q n).hom b := by
  have hn := congrArg (fun k ↦ k.hom a) (rationalize_naturality f n)
  change (rationalize Q n).hom ((SSetPair.homologyMap f integralCoefficients n).hom a) =
    (SSetPair.homologyMap f rationalCoefficients n).hom ((rationalize P n).hom a) at hn
  rw [h] at hn
  exact hn.symm

/-- The positive rational support class is the image of the prescribed integral class. -/
def rationalSupportOrientation (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    RationalRelativeKunneth.relativeHomology (TopCat.of U) (supportComplement U K) n :=
  (rationalize (euclideanSupportPair n U K) n).hom
    (euclideanSupportOrientation n U K hU hK hKU)

/-- The positive local rational class uses the same orientation as the integral index. -/
def rationalPositiveLocalClass (n : ℕ) :
    ↥((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).homology rationalCoefficients n) :=
  (rationalize _ n).hom (euclideanPositiveLocalClass n)

/-- The original displacement carries the rationalized support class to the integer
index times the positive rational local class; no rational orientation is chosen anew.
Source: Dold (1.2), (4.3); coefficient naturality transports the defining integral
coefficient equation, and linearity casts its integer scalar to the rationals. -/
lemma rational_displacement_index {n : ℕ}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f)) :
    (SSetPair.homologyMap (euclideanDisplacementPairMap f) rationalCoefficients n).hom
      (rationalSupportOrientation n U (euclideanAmbientFixedSet f) U.isOpen
        (hK.image continuous_subtype_val) (by rintro x ⟨y, _hy, rfl⟩; exact y.property)) =
      (euclideanFixedPointIndex f hK : ℚ) • rationalPositiveLocalClass n := by
  apply rationalize_coefficient
  exact ((euclideanPositiveLocalCoordinate_characterization n).2.1 _).symm

/-- The local rational coordinate extends the prescribed positive integral coordinate. -/
def rationalLocalCoordinate (n : ℕ) :
    RationalRelativeKunneth.relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ n ≃ₗ[ℚ] ℚ :=
  extendIntegralCoordinate (euclideanPositiveLocalCoordinate n)

/-- The rational local generator retains its positive normalization. -/
lemma rationalLocalCoordinate_positive (n : ℕ) :
    rationalLocalCoordinate n (rationalPositiveLocalClass n) = 1 := by
  change extendIntegralCoordinate (euclideanPositiveLocalCoordinate n)
    ((rationalize _ n).hom (euclideanPositiveLocalClass n)) = 1
  rw [extendIntegralCoordinate_rationalize,
    (euclideanPositiveLocalCoordinate_characterization n).1, Int.cast_one]

/-- Outside the ambient dimension, integral point-local homology vanishes. -/
lemma integralLocalHomology_isZero (n k : ℕ) (hk : k ≠ n) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).homology integralCoefficients k) := by
  cases n with
  | zero => exact euclidean_zero_local_above_dimension_isZero 0 k (Nat.pos_of_ne_zero hk)
  | succ n =>
    cases k with
    | zero =>
      have : Nontrivial (EuclideanSpace ℝ (Fin (n + 1))) := inferInstance
      obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin (n + 1)))
      have : Nonempty {x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0} := ⟨⟨v, hv⟩⟩
      exact normedSpacePuncturedRelativeH0_isZero
    | succ k =>
      exact ((Topology.Homology.reduced_sphere_homology n).2.1 k
        (fun h ↦ hk (congrArg Nat.succ h))).of_iso
          (normedSpacePuncturedRelativeSphereIso (E := EuclideanSpace ℝ (Fin (n + 1))) k)

/-- Flat rationalization gives the full rational concentration of the punctured
Euclidean pair, including the ordinary degree-zero boundary case. -/
lemma rationalLocalHomology_isZero (n k : ℕ) (hk : k ≠ n) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).homology rationalCoefficients k) := by
  have hz := (ModuleCat.extendScalars (Int.castRingHom ℚ)).map_isZero
    (integralLocalHomology_isZero n k hk)
  exact hz.of_iso (rationalRelativeHomologyIso _ k).symm

open RationalRelativeKunneth in
/-- The inverse of product with the local positive generator, expressed using the
actual Künneth inverse and its `(n,q)` summand. No replacement homology theory occurs. -/
def localProductCoordinate (n : ℕ) (Z : TopCat.{0}) (q : ℕ) :
    kunnethTarget (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ (n + q) →ₗ[ℚ]
      homology Z q :=
  (TensorProduct.lid ℚ (homology Z q)).toLinearMap.comp
    ((TensorProduct.map (rationalLocalCoordinate n).toLinearMap (LinearMap.id)).comp
      ((DirectSum.component ℚ (bidegree (n + q)) _ ⟨(n, q), rfl⟩).comp
        (LinearEquiv.ofBijective
          (kunnethMap (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ (n + q))
          (kunnethMap_bijective _ _ _ _)).symm.toLinearMap))

open RationalRelativeKunneth in
/-- The literal diagonal-difference support map applied to the cross product of
the supported orientation with the input class. This is Dold (4.2) before the
last identification with homology of the ambient open domain. -/
def supportOperatorValue (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (q : ℕ) :
    homology (TopCat.of K) q →ₗ[ℚ]
      kunnethTarget (TopCat.of (EuclideanSpace ℝ (Fin n))) (TopCat.of U)
        ({0} : Set _)ᶜ (n + q) :=
  (SSetPair.homologyMap (supportPairMap U K) rationalCoefficients (n + q)).hom.comp
    ((crossTensor (TopCat.of U) (TopCat.of K) (supportComplement U K) n q).comp
      (TensorProduct.mk ℚ _ _ (rationalSupportOrientation n U K hU hK hKU)))

open RationalRelativeKunneth in
/-- Dold's support operator on the original compact subset and open ambient domain. -/
def supportOperator (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (q : ℕ) :
    homology (TopCat.of K) q →ₗ[ℚ] homology (TopCat.of U) q :=
  (localProductCoordinate n (TopCat.of U) q).comp
    (supportOperatorValue n U K hU hK hKU q)

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Reading the local Künneth component of a pure cross product applies exactly
the chosen positive coordinate to its local factor. -/
lemma localProductCoordinate_cross (n : ℕ) (Z : TopCat.{0}) (q : ℕ)
    (a : relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ n)
    (b : homology Z q) :
    localProductCoordinate n Z q
      (cross (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ n q a b) =
      rationalLocalCoordinate n a • b := by
  classical
  let X := TopCat.of (EuclideanSpace ℝ (Fin n))
  let B : Set X := ({0} : Set _)ᶜ
  let e := LinearEquiv.ofBijective (kunnethMap X Z B (n + q))
    (kunnethMap_bijective X Z B (n + q))
  have hc : e (DirectSum.lof ℚ (bidegree (n + q)) _ ⟨(n, q), rfl⟩ (a ⊗ₜ[ℚ] b)) =
      cross X Z B n q a b := by
    simp [e, kunnethMap, cross, regradeRelative]
  change (TensorProduct.lid ℚ (homology Z q))
    (TensorProduct.map (rationalLocalCoordinate n).toLinearMap LinearMap.id
      ((DirectSum.component ℚ (bidegree (n + q)) _ ⟨(n, q), rfl⟩)
        (e.symm (cross X Z B n q a b)))) = _
  rw [← hc, LinearEquiv.symm_apply_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- The local product coordinate loses no information: every other Künneth
summand vanishes by concentration of Euclidean local homology. -/
lemma localProductCoordinate_injective (n : ℕ) (Z : TopCat.{0}) (q : ℕ) :
    Function.Injective (localProductCoordinate n Z q) := by
  classical
  let X := TopCat.of (EuclideanSpace ℝ (Fin n))
  let B : Set X := ({0} : Set _)ᶜ
  let e := LinearEquiv.ofBijective (kunnethMap X Z B (n + q))
    (kunnethMap_bijective X Z B (n + q))
  intro a b hab
  apply e.symm.injective
  apply DirectSum.ext_component (R := ℚ)
  intro i
  by_cases hi : i.val.1 = n
  · have hiq : i.val.2 = q := by have := i.property; omega
    have hieq : i = ⟨(n, q), rfl⟩ := Subtype.ext (Prod.ext hi hiq)
    subst i
    apply (TensorProduct.congr (rationalLocalCoordinate n)
      (LinearEquiv.refl ℚ (homology Z q))).injective
    apply (TensorProduct.lid ℚ (homology Z q)).injective
    exact hab
  · have : Subsingleton (relativeHomology X B i.val.1) :=
      ModuleCat.subsingleton_of_isZero (rationalLocalHomology_isZero n i.val.1 hi)
    exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Product with the coordinate-one local class inverts the local product coordinate. -/
lemma cross_localProductCoordinate (n : ℕ) (Z : TopCat.{0}) (q : ℕ)
    (a : kunnethTarget (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ (n + q)) :
    cross (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ n q
      ((rationalLocalCoordinate n).symm 1) (localProductCoordinate n Z q a) = a := by
  apply localProductCoordinate_injective n Z q
  rw [localProductCoordinate_cross, LinearEquiv.apply_symm_apply, one_smul]

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Pure cross-product form of the published Künneth naturality square. -/
lemma cross_naturality {X Z X' Z' : TopCat.{u}} (B : Set X) (hB : IsOpen B)
    (D : Set X') (f : X ⟶ X') (hf : Set.MapsTo f B D) (g : Z ⟶ Z')
    (p q : ℕ) (a : relativeHomology X B p) (b : homology Z q) :
    targetMap B D f hf g (p + q) (cross X Z B p q a b) =
      cross X' Z' D p q ((relativeMap B D f hf p).hom a) ((homologyMap g q).hom b) := by
  classical
  have hn := (rational_relative_homology_cross_product_kunneth X Z B hB).2.2.2.2.1
    X' Z' D f hf g (p + q)
  have he := congrArg (fun L ↦ L (DirectSum.lof ℚ (bidegree (p + q)) _
    ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b))) hn
  simpa [kunnethMap, sourceMap, cross, regradeRelative] using he

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma relativeMap_identity (X : TopCat.{u}) (B : Set X) (n : ℕ) :
    relativeMap B B (𝟙 X) (fun _ h ↦ h) n = 𝟙 _ := by
  have hp : pairMap B B (𝟙 X) (fun _ h ↦ h) = 𝟙 (pair X B) := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ = 𝟙 _
      rw [← TopCat.toSSet.map_id]
      rfl
    · change TopCat.toSSet.map _ = 𝟙 _
      exact TopCat.toSSet.map_id X
  rw [relativeMap, hp, SSetPair.homologyMap_id]

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- The inverse local product coordinate commutes with maps of its absolute factor. -/
lemma localProductCoordinate_naturality (n : ℕ) {Z Z' : TopCat.{0}} (g : Z ⟶ Z') (q : ℕ)
    (a : kunnethTarget (TopCat.of (EuclideanSpace ℝ (Fin n))) Z ({0} : Set _)ᶜ (n + q)) :
    localProductCoordinate n Z' q
      (targetMap ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ ({0} : Set _)ᶜ
        (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin n)))) (fun _ h ↦ h) g (n + q) a) =
      (homologyMap g q).hom (localProductCoordinate n Z q a) := by
  conv_lhs => rw [← cross_localProductCoordinate n Z q a]
  rw [cross_naturality _ isClosed_singleton.isOpen_compl]
  rw [relativeMap_identity]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]
  rw [localProductCoordinate_cross, LinearEquiv.apply_symm_apply, one_smul]

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- The rational support class is natural under enlargement of the open domain. -/
lemma rationalSupportOrientation_domain (n : ℕ)
    (U V K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hKU : K ⊆ U) (hUV : U ⊆ V) :
    (relativeMap (supportComplement U K) (supportComplement V K)
      (TopCat.ofHom (ContinuousMap.inclusion hUV)) (fun _ h ↦ h) n).hom
        (rationalSupportOrientation n U K hU hK hKU) =
      rationalSupportOrientation n V K hV hK (hKU.trans hUV) := by
  exact rationalize_map_eq
    (singularSubspacePairMap (TopCat.ofHom (ContinuousMap.inclusion hUV))
      (supportComplement U K) (supportComplement V K) (fun _ h ↦ h)) n _ _
    (euclideanSupportOrientation_subset_naturality n U V K hU hV hK hKU hUV)

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Restriction from a larger compact support carries its positive rational
orientation to that of the smaller support. -/
lemma rationalSupportOrientation_support (n : ℕ)
    (U K L : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ U) :
    (relativeMap (supportComplement U L) (supportComplement U K)
      (𝟙 (TopCat.of U)) (fun _ h hk ↦ h (hKL hk)) n).hom
        (rationalSupportOrientation n U L hU hL hLU) =
      rationalSupportOrientation n U K hU hK (hKL.trans hLU) := by
  exact rationalize_map_eq
    (singularSubspacePairMap (𝟙 (TopCat.of U))
      (supportComplement U L) (supportComplement U K) (fun _ h hk ↦ h (hKL hk))) n _ _
    (euclideanSupportOrientation_enlargement n U K L hU hK hL hKL hLU)

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma supportPairMap_support {V : Type} [NormedAddCommGroup V]
    (U K L : Set V) (hKL : K ⊆ L) :
    pairMap (X := TopCat.of (U × K)) (Y := TopCat.of (U × L)) (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U L))
      (productSubspace (TopCat.of U) (TopCat.of L) (supportComplement U L))
      (productMap (𝟙 (TopCat.of U)) (TopCat.ofHom (ContinuousMap.inclusion hKL))) (fun _ h ↦ h) ≫
        supportPairMap U L =
    pairMap (X := TopCat.of (U × K)) (Y := TopCat.of (U × K)) (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U L))
      (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
      (𝟙 (TopCat.of (U × K))) (by intro x h hk; exact h (hKL hk)) ≫ supportPairMap U K := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma supportPairMap_domain {W : Type} [NormedAddCommGroup W] (U V K : Set W)
    (hUV : U ⊆ V) :
    supportPairMap U K ≫
      pairMap (X := TopCat.of (W × U))
        (Y := TopCat.of (W × V))
        (productSubspace (TopCat.of (W)) (TopCat.of U)
        ({0} : Set _)ᶜ)
        (productSubspace (TopCat.of (W)) (TopCat.of V)
          ({0} : Set _)ᶜ)
        (productMap (𝟙 (TopCat.of (W))) (TopCat.ofHom (ContinuousMap.inclusion hUV))) (fun _ h ↦ h) =
    pairMap (X := TopCat.of (U × K)) (Y := TopCat.of (V × K))
      (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
      (productSubspace (TopCat.of V) (TopCat.of K) (supportComplement V K))
      (productMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) (𝟙 (TopCat.of K))) (fun _ h ↦ h) ≫
        supportPairMap V K := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl


open RationalRelativeKunneth in
def supportValue {V : Type} [NormedAddCommGroup V] (U K : Set V) (p q : ℕ)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (z : homology (TopCat.of K) q) :
    kunnethTarget (TopCat.of V) (TopCat.of U) ({0} : Set _)ᶜ (p + q) :=
  (SSetPair.homologyMap (supportPairMap U K) (ModuleCat.of ℚ (ULift ℚ)) (p + q)).hom
    (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q a z)

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma supportValue_domain {W : Type} [NormedAddCommGroup W] (U V K : Set W)
    (hK : IsClosed K) (hUV : U ⊆ V) (p q : ℕ)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (z : homology (TopCat.of K) q) :
    supportValue V K p q
      ((relativeMap (X := TopCat.of U) (Y := TopCat.of V) (supportComplement U K) (supportComplement V K)
        (TopCat.ofHom (ContinuousMap.inclusion hUV)) (fun _ h ↦ h) p).hom a) z =
    targetMap ({0} : Set (W))ᶜ ({0} : Set _)ᶜ
      (𝟙 (TopCat.of (W))) (fun _ h ↦ h) (TopCat.ofHom (ContinuousMap.inclusion hUV)) (p + q)
      (supportValue U K p q a z) := by
  have hc := cross_naturality (X := TopCat.of U) (Z := TopCat.of K)
    (X' := TopCat.of V) (Z' := TopCat.of K) (supportComplement U K)
    (hK.isOpen_compl.preimage continuous_subtype_val)
    (supportComplement V K) (TopCat.ofHom (ContinuousMap.inclusion hUV))
    (fun _ h ↦ h) (𝟙 (TopCat.of K)) p q a z
  have hi : homologyMap (𝟙 (TopCat.of K)) q = 𝟙 _ := by
    unfold homologyMap
    rw [TopCat.toSSet.map_id, SSet.homologyMap_id]
  rw [hi] at hc
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hc
  have hs := congrArg (fun F ↦
    (SSetPair.homologyMap F (ModuleCat.of ℚ (ULift ℚ)) (p + q)).hom
      (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q a z))
    (supportPairMap_domain U V K hUV)
  simp only [SSetPair.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  unfold supportValue
  rw [← hc]
  exact hs.symm

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma supportValue_support {W : Type} [NormedAddCommGroup W] (U K L : Set W)
    (hL : IsClosed L) (hKL : K ⊆ L) (p q : ℕ)
    (a : relativeHomology (TopCat.of U) (supportComplement U L) p)
    (z : homology (TopCat.of K) q) :
    supportValue U L p q a
      ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKL)) q).hom z) =
    supportValue U K p q
      ((relativeMap (X := TopCat.of U) (Y := TopCat.of U)
        (supportComplement U L) (supportComplement U K)
        (𝟙 (TopCat.of U)) (fun _ h hk ↦ h (hKL hk)) p).hom a) z := by
  have hcL := cross_naturality (X := TopCat.of U) (Z := TopCat.of K)
    (X' := TopCat.of U) (Z' := TopCat.of L) (supportComplement U L)
    (hL.isOpen_compl.preimage continuous_subtype_val)
    (supportComplement U L) (𝟙 (TopCat.of U)) (fun _ h ↦ h)
    (TopCat.ofHom (ContinuousMap.inclusion hKL)) p q a z
  rw [relativeMap_identity] at hcL
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hcL
  have hcK := cross_naturality (X := TopCat.of U) (Z := TopCat.of K)
    (X' := TopCat.of U) (Z' := TopCat.of K) (supportComplement U L)
    (hL.isOpen_compl.preimage continuous_subtype_val)
    (supportComplement U K) (𝟙 (TopCat.of U)) (fun _ h hk ↦ h (hKL hk))
    (𝟙 (TopCat.of K)) p q a z
  have hi : homologyMap (𝟙 (TopCat.of K)) q = 𝟙 _ := by
    unfold homologyMap
    rw [TopCat.toSSet.map_id, SSet.homologyMap_id]
  rw [hi] at hcK
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hcK
  have hs := congrArg (fun F ↦
    (SSetPair.homologyMap F (ModuleCat.of ℚ (ULift ℚ)) (p + q)).hom
      (cross (TopCat.of U) (TopCat.of K) (supportComplement U L) p q a z))
    (supportPairMap_support U K L hKL)
  simp only [SSetPair.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  unfold supportValue
  rw [← hcL, ← hcK]
  exact hs

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.1): enlarging the open domain composes the support operator with inclusion. -/
lemma supportOperator_domain (n : ℕ) (U V K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (q : ℕ) (z : homology (TopCat.of K) q) :
    supportOperator n V K hV hK (hKU.trans hUV) q z =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom
        (supportOperator n U K hU hK hKU q z) := by
  change localProductCoordinate n (TopCat.of V) q
    (supportValue V K n q (rationalSupportOrientation n V K hV hK (hKU.trans hUV)) z) =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom
        (localProductCoordinate n (TopCat.of U) q
          (supportValue U K n q (rationalSupportOrientation n U K hU hK hKU) z))
  rw [← rationalSupportOrientation_domain n U V K hU hV hK hKU hUV,
    supportValue_domain U V K hK.isClosed hUV]
  exact localProductCoordinate_naturality n _ q _

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.2): restriction of compact support is compatible with inclusion on homology. -/
lemma supportOperator_support (n : ℕ) (U K L : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ U) (q : ℕ) (z : homology (TopCat.of K) q) :
    supportOperator n U L hU hL hLU q
      ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKL)) q).hom z) =
    supportOperator n U K hU hK (hKL.trans hLU) q z := by
  change localProductCoordinate n (TopCat.of U) q
    (supportValue U L n q (rationalSupportOrientation n U L hU hL hLU)
      ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKL)) q).hom z)) =
    localProductCoordinate n (TopCat.of U) q
      (supportValue U K n q (rationalSupportOrientation n U K hU hK (hKL.trans hLU)) z)
  rw [supportValue_support U K L hL.isClosed hKL,
    rationalSupportOrientation_support n U K L hU hK hL hKL hLU]
/-- The diagonal support map with its second coordinate moved to the compact factor. -/
def anchoredSupportMap {W : Type} [NormedAddCommGroup W] (U K : Set W) (hKU : K ⊆ U) :
    C(U × K, W × U) :=
  ⟨fun x ↦ (x.1.val - x.2.val, ⟨x.2.val, hKU x.2.property⟩), by fun_prop⟩

/-- In a convex ambient domain, moving the output point from the first input to
its compact partner leaves the displacement coordinate fixed throughout. -/
def supportConvexHomotopy {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U K : Set W) (hKU : K ⊆ U) (hU : Convex ℝ U) :
    ContinuousMap.Homotopy (supportMap U K) (anchoredSupportMap U K hKU) where
  toFun x := (x.2.1.val - x.2.2.val,
    ⟨(1 - (x.1 : ℝ)) • x.2.1.val + (x.1 : ℝ) • x.2.2.val,
      hU x.2.1.property (hKU x.2.2.property)
        (sub_nonneg.mpr x.1.property.2) x.1.property.1 (sub_add_cancel 1 _)⟩)
  continuous_toFun := by fun_prop
  map_zero_left := by intro x; simp [supportMap]; rfl
  map_one_left := by intro x; simp [anchoredSupportMap]

/-- Pair preservation along this homotopy follows from the fixed first coordinate. -/
lemma supportConvexHomotopy_mapsTo {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U K : Set W) (hKU : K ⊆ U) (hU : Convex ℝ U)
    (t : unitInterval) (x : U × K) (hx : x.1.val ∉ K) :
    (supportConvexHomotopy U K hKU hU (t, x)).1 ≠ 0 := by
  intro h
  exact hx ((sub_eq_zero.mp h) ▸ x.2.property)

/-- The endpoint of the convex homotopy is a map of the same relative pairs. -/
def anchoredSupportPairMap {W : Type} [NormedAddCommGroup W]
    (U K : Set W) (hKU : K ⊆ U) :
    singularSubspacePair (TopCat.of (U × K)) {x | x.1.val ∉ K} ⟶
      singularSubspacePair (TopCat.of (W × U)) {x | x.1 ≠ 0} :=
  singularSubspacePairMap (TopCat.ofHom (anchoredSupportMap U K hKU)) _ _
    (by intro x hx h; exact hx ((sub_eq_zero.mp h) ▸ x.2.property))

set_option backward.isDefEq.respectTransparency false in
/-- The convex homotopy identifies the two induced relative homology maps. -/
lemma supportPairMap_convex {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U K : Set W) (hKU : K ⊆ U) (hU : Convex ℝ U) (n : ℕ) :
    SSetPair.homologyMap (supportPairMap U K) (ModuleCat.of ℚ (ULift ℚ)) n =
      SSetPair.homologyMap (anchoredSupportPairMap U K hKU) (ModuleCat.of ℚ (ULift ℚ)) n := by
  let H := supportConvexHomotopy U K hKU hU
  have hH := supportConvexHomotopy_mapsTo U K hKU hU
  exact (relative_singular_homotopy_invariance (ModuleCat ℚ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy
      {x : U × K | x.1.val ∉ K} {x : W × U | x.1 ≠ 0}
      (supportMap U K) (anchoredSupportMap U K hKU)
      (by intro x hx h; exact hx ((sub_eq_zero.mp h) ▸ x.2.property))
      (by intro x hx h; exact hx ((sub_eq_zero.mp h) ▸ x.2.property)) H (by intro t x hx; exact hH t x hx))
    (ModuleCat.of ℚ (ULift ℚ))).2 n

/-- Translation to zero, restricted to the actual ambient domain. -/
def pointDifferenceMap {W : Type} [NormedAddCommGroup W] (U : Set W) (c : W) : C(U, W) :=
  ⟨fun x ↦ x.val - c, continuous_subtype_val.sub continuous_const⟩

lemma pointDifferenceMap_mapsTo {W : Type} [NormedAddCommGroup W] (U : Set W) (c : W) :
    Set.MapsTo (pointDifferenceMap U c) (supportComplement U {c}) ({0} : Set W)ᶜ := by
  intro x hx h
  exact hx (Set.mem_singleton_iff.mpr (sub_eq_zero.mp h))

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma anchoredSupportPairMap_singleton {W : Type} [NormedAddCommGroup W]
    (U : Set W) (c : W) (hc : c ∈ U) :
    anchoredSupportPairMap U {c} (Set.singleton_subset_iff.mpr hc) =
      pairMap (X := TopCat.of (U × ({c} : Set W))) (Y := TopCat.of (W × U))
        (productSubspace (TopCat.of U) (TopCat.of ({c} : Set W)) (supportComplement U {c}))
        (productSubspace (TopCat.of W) (TopCat.of U) ({0} : Set W)ᶜ)
        (productMap (TopCat.ofHom (pointDifferenceMap U c))
          (TopCat.ofHom (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))))
        (fun _x hx ↦ pointDifferenceMap_mapsTo U c hx) := by
  have hmap : TopCat.ofHom (anchoredSupportMap U {c} (Set.singleton_subset_iff.mpr hc)) =
      productMap (TopCat.ofHom (pointDifferenceMap U c))
        (TopCat.ofHom (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))) := by
    apply TopCat.ext
    intro x
    apply Prod.ext
    · exact congrArg (x.1.val - ·) (Set.mem_singleton_iff.mp x.2.property)
    · rfl
  apply MorphismProperty.Arrow.Hom.ext
  · apply congrArg (fun k ↦ TopCat.toSSet.map k)
    apply TopCat.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k ↦ k x.val) hmap
  · exact congrArg (fun k ↦ TopCat.toSSet.map k) hmap

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- For singleton support in a convex domain, the diagonal-difference operator is
cross product with the translated local class followed by inclusion of the point. -/
lemma supportValue_singleton_convex {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U : Set W) (c : W) (hc : c ∈ U) (hU : Convex ℝ U) (p q : ℕ)
    (a : relativeHomology (TopCat.of U) (supportComplement U {c}) p)
    (z : homology (TopCat.of ({c} : Set W)) q) :
    supportValue U {c} p q a z =
      cross (TopCat.of W) (TopCat.of U) ({0} : Set W)ᶜ p q
        ((relativeMap (X := TopCat.of U) (Y := TopCat.of W)
          (supportComplement U {c}) ({0} : Set W)ᶜ
          (TopCat.ofHom (pointDifferenceMap U c)) (pointDifferenceMap_mapsTo U c) p).hom a)
        ((homologyMap (TopCat.ofHom
          (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))) q).hom z) := by
  unfold supportValue
  rw [supportPairMap_convex U {c} (Set.singleton_subset_iff.mpr hc) hU,
    anchoredSupportPairMap_singleton U c hc]
  exact cross_naturality (X := TopCat.of U) (Z := TopCat.of ({c} : Set W))
    (X' := TopCat.of W) (Z' := TopCat.of U) (supportComplement U {c})
    (isClosed_singleton.isOpen_compl.preimage continuous_subtype_val)
    ({0} : Set W)ᶜ (TopCat.ofHom (pointDifferenceMap U c))
    (pointDifferenceMap_mapsTo U c)
    (TopCat.ofHom (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))) p q a z

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Constant-displacement normalization sends the singleton support class to the
prescribed positive rational local generator, including dimension zero. -/
lemma rationalSupportOrientation_singleton (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U) :
    (relativeMap (X := TopCat.of U) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (supportComplement U {c}) ({0} : Set _)ᶜ (TopCat.ofHom (pointDifferenceMap U c))
      (pointDifferenceMap_mapsTo U c) n).hom
      (rationalSupportOrientation n U {c} hU isCompact_singleton
        (Set.singleton_subset_iff.mpr hc)) = rationalPositiveLocalClass n := by
  let O : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hU⟩
  let f : C(O, EuclideanSpace ℝ (Fin n)) := ContinuousMap.const O c
  have hK : IsCompact (euclideanFixedSet f) := constant_fixedSet_compact c hc
  have hfixed : euclideanAmbientFixedSet f = {c} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Set.mem_singleton_iff.mpr hy.symm
    · intro hx
      have hxc := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨c, hc⟩, rfl, rfl⟩
  have h := rationalize_map_eq (euclideanDisplacementPairMap f) n _ _
    (euclidean_constant_displacement_positive_class (U := O) c hc)
  change (relativeMap (X := TopCat.of U) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (supportComplement U (euclideanAmbientFixedSet f)) ({0} : Set _)ᶜ
    (TopCat.ofHom (pointDifferenceMap U c))
      (by intro x hx hz; apply hx; rw [hfixed];
          exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hz)) n).hom
      (rationalSupportOrientation n U (euclideanAmbientFixedSet f) hU
        (hK.image continuous_subtype_val)
        (by rintro x ⟨y, hy, rfl⟩; exact y.property)) = rationalPositiveLocalClass n at h
  generalize_proofs hp hcompact hsub at h
  revert hp hcompact hsub h
  rw [hfixed]
  intro hp hcompact hsub h
  exact h

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold's support operator agrees with inclusion for a point in a convex open domain. -/
lemma supportOperator_singleton_convex (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hconv : Convex ℝ U) (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U)
    (q : ℕ) (z : homology (TopCat.of ({c} : Set (EuclideanSpace ℝ (Fin n)))) q) :
    supportOperator n U {c} hU isCompact_singleton (Set.singleton_subset_iff.mpr hc) q z =
      (homologyMap (TopCat.ofHom
        (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))) q).hom z := by
  change localProductCoordinate n (TopCat.of U) q
    (supportValue U {c} n q (rationalSupportOrientation n U {c} hU isCompact_singleton
      (Set.singleton_subset_iff.mpr hc)) z) = _
  rw [supportValue_singleton_convex U c hc hconv,
    rationalSupportOrientation_singleton n U hU c hc,
    localProductCoordinate_cross, rationalLocalCoordinate_positive, one_smul]

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma homologyMap_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    homologyMap (f ≫ g) q = homologyMap f q ≫ homologyMap g q := by
  unfold homologyMap
  rw [TopCat.toSSet.map_comp, SSet.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold's point case on every open domain follows by shrinking to a convex ball. -/
lemma supportOperator_singleton (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (c : EuclideanSpace ℝ (Fin n)) (hc : c ∈ U)
    (q : ℕ) (z : homology (TopCat.of ({c} : Set (EuclideanSpace ℝ (Fin n)))) q) :
    supportOperator n U {c} hU isCompact_singleton (Set.singleton_subset_iff.mpr hc) q z =
      (homologyMap (TopCat.ofHom
        (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hc))) q).hom z := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU c hc
  have hcB : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have h := supportOperator_domain n (Metric.ball c r) U {c}
    Metric.isOpen_ball hU isCompact_singleton (Set.singleton_subset_iff.mpr hcB) hrU q z
  rw [supportOperator_singleton_convex n (Metric.ball c r) Metric.isOpen_ball
    (convex_ball c r) c hcB] at h
  refine h.trans ?_
  change ((homologyMap (TopCat.ofHom
    (ContinuousMap.inclusion (Set.singleton_subset_iff.mpr hcB))) q ≫
      homologyMap (TopCat.ofHom (ContinuousMap.inclusion hrU)) q).hom z) = _
  rw [← homologyMap_comp]
  rfl
set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
lemma pointClass_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (homologyMap f 0).hom (pointClass X x) = pointClass Y (f x) := by
  unfold pointClass homologyMap
  apply cycleClass_map
  change SignedShuffle.pushforward f.hom 0
    (SignedShuffle.generator X (SignedShuffle.pointSimplex X x)) =
      SignedShuffle.generator Y (SignedShuffle.pointSimplex Y (f x))
  rw [SignedShuffle.pushforward_generator]
  congr 1

open RationalRelativeKunneth in
/-- Degree-zero homology is generated by its actual singular point classes. -/
lemma homologyZero_linearMap_ext (X : TopCat.{u}) (M : ModuleCat.{u} ℚ)
    (f g : homology X 0 →ₗ[ℚ] M) (h : ∀ x : X, f (pointClass X x) = g (pointClass X x)) :
    f = g := by
  let liftCycle : (chains X).X 0 →ₗ[ℚ] cycles (chains X) 0 :=
    LinearMap.codRestrict _ LinearMap.id (by
      intro a
      simp [cycles, HomologicalComplex.dFrom, ComplexShape.down_Rel])
  let π := (cycleClass (chains X) 0).comp liftCycle
  have hπ : Function.Surjective π := by
    intro a
    obtain ⟨c, hc⟩ := cycleClass_surjective (chains X) 0 a
    exact ⟨c.val, hc⟩
  have hh : f.comp π = g.comp π := by
    apply SignedShuffle.chain_linearMap_ext X 0 M
    intro σ
    let x : X := (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))) σ (Classical.arbitrary _)
    have : Subsingleton (Convexity.StdSimplex ℝ (Fin 1)) := inferInstance
    have hσ : σ = SignedShuffle.pointSimplex X x := by
      apply (TopCat.toSSetObjEquiv X _).injective
      apply ContinuousMap.ext
      intro t
      change (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))) σ t = x
      exact congrArg ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))) σ)
        (Subsingleton.elim t _)
    rw [hσ]
    exact h x
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := hπ a
  exact congrArg (fun k ↦ k b) hh

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold's degree-zero case follows from compact-support naturality and generation
of ordinary H₀ by the point classes. Empty supports are included. -/
lemma supportOperator_zero (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    supportOperator n U K hU hK hKU 0 =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) 0).hom := by
  apply homologyZero_linearMap_ext
  intro x
  have h := supportOperator_support n U {x.val} K hU isCompact_singleton hK
    (Set.singleton_subset_iff.mpr x.property) hKU 0
      (pointClass (TopCat.of ({x.val} : Set (EuclideanSpace ℝ (Fin n)))) ⟨x.val, rfl⟩)
  rw [supportOperator_singleton n U hU x.val (hKU x.property),
    pointClass_naturality, pointClass_naturality] at h
  rw [pointClass_naturality]
  exact h

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.2): the support identity passes from a smaller open domain to a larger one. -/
lemma supportOperator_identity_enlarge_domain (n : ℕ)
    (U V K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (q : ℕ)
    (h : supportOperator n U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom) :
    supportOperator n V K hV hK (hKU.trans hUV) q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hKU.trans hUV))) q).hom := by
  ext z
  rw [supportOperator_domain n U V K hU hV hK hKU hUV, h]
  change ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q ≫
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom z) = _
  rw [← homologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.3): the support identity passes to every compact subsupport. -/
lemma supportOperator_identity_restrict_support (n : ℕ)
    (U K L : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ U) (q : ℕ)
    (h : supportOperator n U L hU hL hLU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hLU)) q).hom) :
    supportOperator n U K hU hK (hKL.trans hLU) q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hKL.trans hLU))) q).hom := by
  ext z
  rw [← supportOperator_support n U K L hU hK hL hKL hLU, h]
  change ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKL)) q ≫
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion hLU)) q).hom z) = _
  rw [← homologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.4): injectivity of homology under domain inclusion lets the support
identity descend to a smaller open neighborhood. -/
lemma supportOperator_identity_of_domain_injective (n : ℕ)
    (U V K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (q : ℕ)
    (hinj : Function.Injective (homologyMap
      (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom)
    (h : supportOperator n V K hV hK (hKU.trans hUV) q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hKU.trans hUV))) q).hom) :
    supportOperator n U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  ext z
  apply hinj
  rw [← supportOperator_domain n U V K hU hV hK hKU hUV, h]
  change _ = ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q ≫
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom z)
  rw [← homologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
open RationalRelativeKunneth in
/-- Dold (5.5): support identities on compact subspaces whose homology images span
imply the identity on their ambient compact support. This is the generating step
for the full cubical skeleton and for a subcomplex's top skeleton. -/
lemma supportOperator_identity_of_spanning (n : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (q : ℕ)
    {ι : Type} (L : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hL : ∀ i, IsCompact (L i)) (hLK : ∀ i, L i ⊆ K)
    (hspan : Submodule.span ℚ (⋃ i, Set.range
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hLK i))) q).hom) = ⊤)
    (h : ∀ i, supportOperator n U (L i) hU (hL i) ((hLK i).trans hKU) q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion ((hLK i).trans hKU))) q).hom) :
    supportOperator n U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).mpr
  intro z
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp z.property
  change _ = _ at hx
  rw [← hx, supportOperator_support n U (L i) K hU (hL i) hK (hLK i) hKU, h i]
  change _ = ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hLK i))) q ≫
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom x)
  rw [← homologyMap_comp]
  rfl
/-- Flat scalar extension commutes with ordinary absolute simplicial homology. -/
def extendScalarsAbsoluteHomologyIso {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : @Module.Flat R S _ _ (Module.compHom S f))
    (X : SSet.{u}) (M : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (X.homology M n) ≅
      X.homology ((ModuleCat.extendScalars f).obj M) n := by
  let F := ModuleCat.extendScalars.{0, 0, u} f
  have : Functor.PreservesHomology F := extendScalars_preservesHomology f hflat
  let G := F.mapHomologicalComplex (.down ℕ)
  let e := (SSet.chainComplexFunctorObjCompMapIso F M).app X
  exact ((X.chainComplex M).sc n |>.mapHomologyIso F).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso (ModuleCat S) (.down ℕ) n).app
      (G.obj (X.chainComplex M))).symm ≪≫
    HomologicalComplex.homologyMapIso e n

/-- Rational homology of the original absolute singular complex is the flat
extension of its integral homology, without finite-generation restrictions. -/
def rationalAbsoluteHomologyIso (X : TopCat.{u}) (n : ℕ) :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj
      ((TopCat.toSSet.obj X).homology integralCoefficients n) ≅
        (TopCat.toSSet.obj X).homology rationalCoefficients n := by
  have hflat : @Module.Flat ℤ ℚ _ _ (Module.compHom ℚ (Int.castRingHom ℚ)) :=
    IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact extendScalarsAbsoluteHomologyIso (Int.castRingHom ℚ) hflat _ _ n ≪≫
    HomologicalComplex.homologyMapIso
      (((SSet.chainComplexFunctor (ModuleCat.{u} ℚ)).mapIso
        rationalExtensionCoefficientIso).app (TopCat.toSSet.obj X)) n

/-- Positive-degree rational homology of the unit sphere vanishes off its dimension. -/
lemma rationalSphereHomology_isZero (q k : ℕ) (hk : 0 < k) (hkq : k ≠ q) :
    IsZero ((TopCat.toSSet.obj (TopCat.of
      {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1})).homology rationalCoefficients k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let X := TopCat.of {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1}
  have hz := (Topology.Homology.unitSphere_profile q).2 (k + 1) hkq
  have hi : IsZero ((TopCat.toSSet.obj X).homology integralCoefficients (k + 1)) :=
    hz.of_iso (Topology.Homology.integralReducedPositiveOrdinaryIso X k).symm
  exact ((ModuleCat.extendScalars (Int.castRingHom ℚ)).map_isZero hi).of_iso
    (rationalAbsoluteHomologyIso X (k + 1)).symm

/-- The positive-dimensional unit sphere has a one-dimensional rational top homology. -/
def rationalSphereTopIso (q : ℕ) :
    (TopCat.toSSet.obj (TopCat.of
      {x : EuclideanSpace ℝ (Fin (q + 1 + 1)) // ‖x‖ = 1})).homology
        rationalCoefficients (q + 1) ≅ rationalCoefficients := by
  let X := TopCat.of {x : EuclideanSpace ℝ (Fin (q + 1 + 1)) // ‖x‖ = 1}
  let e := Classical.choice (Topology.Homology.unitSphere_profile (q + 1)).1
  exact (rationalAbsoluteHomologyIso X (q + 1)).symm ≪≫
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).mapIso
      ((Topology.Homology.integralReducedPositiveOrdinaryIso X q).symm ≪≫ e) ≪≫
    rationalExtensionCoefficientIso

open RationalRelativeKunneth
/-- Relative chains modulo the empty subspace are the original absolute chains. -/
lemma chainProjection_empty_isIso (X : TopCat.{u}) :
    IsIso (chainProjection X ∅) := by
  have hz : IsZero (((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).chainComplex coefficients)) :=
    singular_chain_isZero_of_isEmpty _ _
  exact CokernelCofork.IsColimit.isIso_π ((pair X ∅).cokernelCoforkChainComplex coefficients)
    ((pair X ∅).isColimitCokernelCoforkChainComplex coefficients)
    (hz.eq_of_src _ _)

/-- The ordinary absolute-to-relative projection at the empty subspace is an isomorphism. -/
def emptyPairHomologyIso (X : TopCat.{u}) (n : ℕ) :
    homology X n ≅ relativeHomology X ∅ n := by
  have := chainProjection_empty_isIso X
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (.down ℕ) n).mapIso
    (asIso (chainProjection X ∅))

set_option backward.isDefEq.respectTransparency false in
/-- On an empty relative subspace, the quotient of the absolute cross product
is the prescribed relative cross product. -/
lemma emptyPairHomologyIso_cross (X Z : TopCat.{u}) (p q : ℕ)
    (a : homology X p) (b : homology Z q) :
    (emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).hom.hom
      (absoluteCross X Z p q a b) =
      cross X Z ∅ p q ((emptyPairHomologyIso X p).hom.hom a) b := by
  have h := (rational_relative_homology_cross_product_kunneth X Z ∅ isOpen_empty).2.2.2.2.2.2.1
    p q a b
  exact h

/-- The absolute rational Künneth equivalence is obtained from the relative one
at the empty subspace, through the literal quotient projections. -/
def absoluteKunnethEquiv (X Z : TopCat.{u}) (n : ℕ) :
    DirectSum (bidegree n) (fun pq ↦
      TensorProduct ℚ (homology X pq.val.1) (homology Z pq.val.2)) ≃ₗ[ℚ]
        homology (TopCat.of (X × Z)) n :=
  (DirectSum.congrLinearEquiv fun pq ↦
    TensorProduct.congr (emptyPairHomologyIso X pq.val.1).toLinearEquiv
      (LinearEquiv.refl ℚ _)).trans
    ((LinearEquiv.ofBijective (kunnethMap X Z ∅ n) (kunnethMap_bijective X Z ∅ n)).trans
      (emptyPairHomologyIso (TopCat.of (X × Z)) n).symm.toLinearEquiv)

set_option backward.isDefEq.respectTransparency false in
lemma absoluteKunnethEquiv_tmul (X Z : TopCat.{u}) (p q : ℕ)
    (a : homology X p) (b : homology Z q) :
    absoluteKunnethEquiv X Z (p + q)
      (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b)) =
        absoluteCross X Z p q a b := by
  apply (emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).toLinearEquiv.injective
  change (emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).hom.hom _ =
    (emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).hom.hom _
  rw [emptyPairHomologyIso_cross]
  change (emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).hom.hom
    ((emptyPairHomologyIso (TopCat.of (X × Z)) (p + q)).inv.hom _) = _
  rw [Iso.inv_hom_id_apply]
  simp [DirectSum.coe_congrLinearEquiv, kunnethMap, cross, regradeRelative]

set_option backward.isDefEq.respectTransparency false in
lemma absoluteCross_point_right (X Z : TopCat.{u}) (p : ℕ) (a : homology X p) (z : Z) :
    absoluteCross X Z p 0 a (pointClass Z z) =
      (homologyMap (insertPoint X Z z) p).hom a := by
  apply (emptyPairHomologyIso (TopCat.of (X × Z)) p).toLinearEquiv.injective
  change (emptyPairHomologyIso (TopCat.of (X × Z)) (p + 0)).hom.hom _ = _
  rw [emptyPairHomologyIso_cross]
  have h := (rational_relative_homology_cross_product_kunneth X Z ∅ isOpen_empty).2.2.2.2.2.2.2.2.2.2.1
    p ((emptyPairHomologyIso X p).hom.hom a) z
  rw [h]
  have hn := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℚ)).app coefficients).naturality
    (pairMap (X := X) (Y := TopCat.of (X × Z)) ∅ ∅ (insertPoint X Z z) (by simp))
  have hh := congrArg (fun k ↦ HomologicalComplex.homologyMap k p) hn
  simp only [HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (fun k ↦ k.hom a) hh.symm

set_option backward.isDefEq.respectTransparency false in
lemma absoluteCross_point_left (X Z : TopCat.{u}) (q : ℕ) (x : X) (b : homology Z q) :
    (eqToHom (congrArg (homology (TopCat.of (X × Z))) (Nat.zero_add q))).hom
      (absoluteCross X Z 0 q (pointClass X x) b) =
        (homologyMap (insertPointLeft X Z x) q).hom b := by
  apply (emptyPairHomologyIso (TopCat.of (X × Z)) q).toLinearEquiv.injective
  have h := (rational_relative_homology_cross_product_kunneth X Z ∅ isOpen_empty).2.2.2.2.2.2.2.2.2.2.2.1
    q x b
  have hproj := emptyPairHomologyIso_cross X Z 0 q (pointClass X x) b
  have htrans : ∀ {i j : ℕ} (hij : i = j) (a : homology (TopCat.of (X × Z)) i),
      (emptyPairHomologyIso (TopCat.of (X × Z)) j).hom.hom
        ((eqToHom (congrArg (homology (TopCat.of (X × Z))) hij)).hom a) =
      regradeRelative (TopCat.of (X × Z)) ∅ hij
        ((emptyPairHomologyIso (TopCat.of (X × Z)) i).hom.hom a) := by
    intro i j hij a
    subst j
    rfl
  change (emptyPairHomologyIso (TopCat.of (X × Z)) q).hom.hom _ = _
  rw [htrans, hproj]
  exact h
set_option backward.isDefEq.respectTransparency false in
lemma emptyPairHomologyIso_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    homologyMap f n ≫ (emptyPairHomologyIso Y n).hom =
      (emptyPairHomologyIso X n).hom ≫ relativeMap ∅ ∅ f (by simp) n := by
  have hn := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℚ)).app coefficients).naturality
    (pairMap (X := X) (Y := Y) ∅ ∅ f (by simp))
  have hh := congrArg (fun k ↦ HomologicalComplex.homologyMap k n) hn
  simp only [HomologicalComplex.homologyMap_comp] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
lemma absoluteCross_naturality {X Z X' Z' : TopCat.{u}} (f : X ⟶ X') (g : Z ⟶ Z')
    (p q : ℕ) (a : homology X p) (b : homology Z q) :
    (homologyMap (productMap f g) (p + q)).hom (absoluteCross X Z p q a b) =
      absoluteCross X' Z' p q ((homologyMap f p).hom a) ((homologyMap g q).hom b) := by
  apply (emptyPairHomologyIso (TopCat.of (X' × Z')) (p + q)).toLinearEquiv.injective
  have hproj := congrArg (fun k ↦ k.hom (absoluteCross X Z p q a b))
    (emptyPairHomologyIso_naturality (productMap f g) (p + q))
  change (emptyPairHomologyIso (TopCat.of (X' × Z')) (p + q)).hom.hom
    ((homologyMap (productMap f g) (p + q)).hom _) = _
  change (emptyPairHomologyIso (TopCat.of (X' × Z')) (p + q)).hom.hom
    ((homologyMap (productMap f g) (p + q)).hom _) = _ at hproj
  rw [hproj]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [emptyPairHomologyIso_cross]
  have hn := (rational_relative_homology_cross_product_kunneth X Z ∅ isOpen_empty).2.2.2.2.1
    X' Z' ∅ f (by simp) g (p + q)
  have he := congrArg (fun L ↦ L (DirectSum.lof ℚ (bidegree (p + q)) _
    ⟨(p, q), rfl⟩ ((emptyPairHomologyIso X p).hom.hom a ⊗ₜ[ℚ] b))) hn
  simp only [kunnethMap, sourceMap, DirectSum.toModule_lof, LinearMap.comp_apply,
    TensorProduct.map_tmul] at he
  change (targetMap ∅ ∅ f (by simp) g (p + q))
    (cross X Z ∅ p q ((emptyPairHomologyIso X p).hom.hom a) b) =
      cross X' Z' ∅ p q
        ((relativeMap ∅ ∅ f (by simp) p).hom ((emptyPairHomologyIso X p).hom.hom a))
        ((homologyMap g q).hom b) at he
  change (targetMap ∅ ∅ f (by simp) g (p + q))
    (cross X Z ∅ p q ((emptyPairHomologyIso X p).hom.hom a) b) = _
  rw [he]
  have hf := congrArg (fun k ↦ k.hom a) (emptyPairHomologyIso_naturality f p)
  change (emptyPairHomologyIso X' p).hom.hom ((homologyMap f p).hom a) =
    (relativeMap ∅ ∅ f (by simp) p).hom ((emptyPairHomologyIso X p).hom.hom a) at hf
  rw [← hf]
  exact (emptyPairHomologyIso_cross X' Z' p q _ _).symm

set_option backward.isDefEq.respectTransparency false in
lemma pointClass_augmentation (X : TopCat.{u}) (x : X) :
    (X.singularHomology₀ε coefficients).hom (pointClass X x) = ULift.up 1 := by
  let C := chains X
  let σ := SignedShuffle.pointSimplex X x
  let c : cycles C 0 := ⟨SignedShuffle.generator X σ, pointGenerator_cycle X x⟩
  let l := C.liftCycles ((TopCat.toSSet.obj X).ιChainComplex σ) 0 (by simp) (by simp)
  have hc : (C.sc 0).moduleCatCyclesIso.inv c = l (ULift.up 1) := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom (C.sc 0).moduleCatCyclesIso_inv_iCycles c
    have h₂ := ConcreteCategory.congr_hom
      (C.liftCycles_i ((TopCat.toSSet.obj X).ιChainComplex σ) 0 (by simp) (by simp))
      (ULift.up 1)
    exact h₁.trans h₂.symm
  have hh := ConcreteCategory.congr_hom (C.sc 0).moduleCatCyclesIso_inv_π c
  change (C.homologyπ 0) ((C.sc 0).moduleCatCyclesIso.inv c) = pointClass X x at hh
  rw [hc] at hh
  rw [← hh]
  exact ConcreteCategory.congr_hom
    ((TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
      coefficients σ) (ULift.up 1)

def homologyZeroCoordinate (X : TopCat.{u}) [PathConnectedSpace X] :
    homology X 0 ≃ₗ[ℚ] ℚ :=
  (asIso (X.singularHomology₀ε coefficients)).toLinearEquiv.trans
    ULift.moduleEquiv

lemma homologyZeroCoordinate_point (X : TopCat.{u}) [PathConnectedSpace X] (x : X) :
    homologyZeroCoordinate X (pointClass X x) = 1 := by
  exact congrArg ULift.down (pointClass_augmentation X x)

lemma homologyZero_eq_smul_point (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (a : homology X 0) : a = homologyZeroCoordinate X a • pointClass X x := by
  apply (homologyZeroCoordinate X).injective
  rw [map_smul, homologyZeroCoordinate_point, smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
lemma homologyMap_constant {X Y : TopCat.{u}} (y : Y) (q : ℕ) (hq : q ≠ 0) :
    homologyMap (TopCat.ofHom (ContinuousMap.const X y)) q = 0 := by
  let P : TopCat.{u} := TopCat.of PUnit.{u+1}
  let f : X ⟶ P := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : P ⟶ Y := TopCat.ofHom (ContinuousMap.const P y)
  have hz : IsZero (homology P q) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} ℚ) q coefficients P hq
  have he : TopCat.ofHom (ContinuousMap.const X y) = f ≫ g := rfl
  rw [he, homologyMap_comp, hz.eq_zero_of_tgt (homologyMap f q), zero_comp]

lemma homology_regrade_mem_range {X Y : TopCat.{u}} (f : X ⟶ Y)
    {i j : ℕ} (h : i = j) (a : homology Y i) :
    (eqToHom (congrArg (homology Y) h)).hom a ∈ LinearMap.range (homologyMap f j).hom ↔
      a ∈ LinearMap.range (homologyMap f i).hom := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a positive degree below the first nonzero reduced homology, the product
homology is generated by the two factor inclusions. -/
lemma productHomology_factor_span (X Z : TopCat.{u})
    [PathConnectedSpace X] [PathConnectedSpace Z] (x : X) (z : Z)
    (n : ℕ) (hn : 0 < n)
    (hX : ∀ k : ℕ, 0 < k → k < n → IsZero (homology X k)) :
    LinearMap.range (homologyMap (insertPoint X Z z) n).hom ⊔
      LinearMap.range (homologyMap (insertPointLeft X Z x) n).hom = ⊤ := by
  classical
  let P := LinearMap.range (homologyMap (insertPoint X Z z) n).hom ⊔
    LinearMap.range (homologyMap (insertPointLeft X Z x) n).hom
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨t, rfl⟩ := (absoluteKunnethEquiv X Z n).surjective a
  induction t using DirectSum.induction_on with
  | zero => simpa only [map_zero] using P.zero_mem
  | add a b ha hb => simpa only [map_add] using P.add_mem ha hb
  | of pq t =>
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using P.add_mem ha hb
    | tmul a b =>
      rcases pq with ⟨⟨p, q⟩, hpq⟩
      dsimp only at hpq
      subst n
      change absoluteKunnethEquiv X Z (p + q)
        (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b)) ∈ P
      rw [absoluteKunnethEquiv_tmul]
      by_cases hq : q = 0
      · subst q
        rw [homologyZero_eq_smul_point Z z b]
        simp only [absoluteCross, map_smul, TensorProduct.tmul_smul]
        apply P.smul_mem
        exact Submodule.mem_sup_left ⟨a, (absoluteCross_point_right X Z p a z).symm⟩
      · by_cases hp : p = 0
        · subst p
          rw [homologyZero_eq_smul_point X x a]
          simp only [absoluteCross, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
          apply P.smul_mem
          apply Submodule.mem_sup_right
          apply (homology_regrade_mem_range (insertPointLeft X Z x) (Nat.zero_add q)
            (absoluteCross X Z 0 q (pointClass X x) b)).mp
          exact ⟨b, (absoluteCross_point_left X Z q x b).symm⟩
        · have hz := hX p (Nat.pos_of_ne_zero hp) (by omega)
          have ha : a = 0 := (ModuleCat.subsingleton_of_isZero hz).elim _ _
          rw [ha]
          simpa only [absoluteCross, TensorProduct.zero_tmul, map_zero] using P.zero_mem

lemma homologyMap_identity (X : TopCat.{u}) (n : ℕ) :
    homologyMap (𝟙 X) n = 𝟙 (homology X n) := by
  unfold homologyMap
  rw [TopCat.toSSet.map_id, SSet.homologyMap_id]

set_option backward.isDefEq.respectTransparency false in
/-- The two projections recover the two summands in the sphere-degree Künneth
formula. This version only assumes vanishing below the specified degree. -/
lemma productHomology_reconstruct (X Z : TopCat.{u})
    [PathConnectedSpace X] [PathConnectedSpace Z] (x : X) (z : Z)
    (n : ℕ) (hn : 0 < n)
    (hX : ∀ k : ℕ, 0 < k → k < n → IsZero (homology X k))
    (t : homology (TopCat.of (X × Z)) n) :
    t = (homologyMap (insertPoint X Z z) n).hom
      ((homologyMap (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) n).hom t) +
      (homologyMap (insertPointLeft X Z x) n).hom
      ((homologyMap (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) n).hom t) := by
  let f : TopCat.of (X × Z) ⟶ X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let g : TopCat.of (X × Z) ⟶ Z := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  have hfr (a : homology X n) :
      (homologyMap f n).hom ((homologyMap (insertPoint X Z z) n).hom a) = a := by
    change (homologyMap (insertPoint X Z z) n ≫ homologyMap f n).hom a = a
    rw [← homologyMap_comp]
    change (homologyMap (𝟙 X) n).hom a = a
    rw [homologyMap_identity]
    rfl
  have hfl (b : homology Z n) :
      (homologyMap f n).hom ((homologyMap (insertPointLeft X Z x) n).hom b) = 0 := by
    change (homologyMap (insertPointLeft X Z x) n ≫ homologyMap f n).hom b = 0
    rw [← homologyMap_comp]
    change (homologyMap (TopCat.ofHom (ContinuousMap.const Z x)) n).hom b = 0
    rw [homologyMap_constant x n (Nat.ne_of_gt hn)]
    rfl
  have hgr (a : homology X n) :
      (homologyMap g n).hom ((homologyMap (insertPoint X Z z) n).hom a) = 0 := by
    change (homologyMap (insertPoint X Z z) n ≫ homologyMap g n).hom a = 0
    rw [← homologyMap_comp]
    change (homologyMap (TopCat.ofHom (ContinuousMap.const X z)) n).hom a = 0
    rw [homologyMap_constant z n (Nat.ne_of_gt hn)]
    rfl
  have hgl (b : homology Z n) :
      (homologyMap g n).hom ((homologyMap (insertPointLeft X Z x) n).hom b) = b := by
    change (homologyMap (insertPointLeft X Z x) n ≫ homologyMap g n).hom b = b
    rw [← homologyMap_comp]
    change (homologyMap (𝟙 Z) n).hom b = b
    rw [homologyMap_identity]
    rfl
  obtain ⟨a, ⟨a, rfl⟩, b, ⟨b, rfl⟩, ht⟩ :=
    Submodule.mem_sup.mp (show t ∈ _ ⊔ _ by
      rw [productHomology_factor_span X Z x z n hn hX]
      trivial)
  change t = (homologyMap (insertPoint X Z z) n).hom ((homologyMap f n).hom t) +
    (homologyMap (insertPointLeft X Z x) n).hom ((homologyMap g n).hom t)
  rw [← ht]
  simp only [map_add, hfr, hfl, hgr, hgl, add_zero, zero_add]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal of a sphere-degree class is the sum of its two factor classes. -/
lemma homology_diagonal_factor_sum (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (n : ℕ) (hn : 0 < n)
    (hX : ∀ k : ℕ, 0 < k → k < n → IsZero (homology X k)) (a : homology X n) :
    (homologyMap (diagonalMap X) n).hom a =
      (homologyMap (insertPoint X X x) n).hom a +
      (homologyMap (insertPointLeft X X x) n).hom a := by
  have h := productHomology_reconstruct X X x x n hn hX
    ((homologyMap (diagonalMap X) n).hom a)
  have hf : diagonalMap X ≫ TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ = 𝟙 X := rfl
  have hg : diagonalMap X ≫ TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ = 𝟙 X := rfl
  have hf' := congrArg (fun k ↦ k.hom a) (homologyMap_comp (diagonalMap X)
    (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) n)
  have hg' := congrArg (fun k ↦ k.hom a) (homologyMap_comp (diagonalMap X)
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) n)
  rw [hf, homologyMap_identity] at hf'
  rw [hg, homologyMap_identity] at hg'
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hf' hg'
  rw [← hf', ← hg'] at h
  exact h

/-- Positive-dimensional unit spheres are path connected. -/
lemma unitSphere_pathConnected (q : ℕ) (hq : 0 < q) :
    PathConnectedSpace {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1} := by
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (q + 1))) := by
    rw [← Module.finrank_eq_rank]
    simp only [finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < q + 1 by omega)
  have h := isPathConnected_sphere hr (0 : EuclideanSpace ℝ (Fin (q + 1)))
    (show (0 : ℝ) ≤ 1 by norm_num)
  have hs : Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 =
      {x | ‖x‖ = 1} := by ext x; simp
  rw [hs] at h
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-- The actual rational diagonal of a sphere has its two fundamental-class terms. -/
lemma rationalSphere_diagonal (q : ℕ) (hq : 0 < q)
    (x : {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1})
    (a : homology (TopCat.of {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1}) q) :
    let X := TopCat.of {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1}
    (homologyMap (diagonalMap X) q).hom a =
      (homologyMap (insertPoint X X x) q).hom a +
      (homologyMap (insertPointLeft X X x) q).hom a := by
  have := unitSphere_pathConnected q hq
  exact homology_diagonal_factor_sum
    (TopCat.of {x : EuclideanSpace ℝ (Fin (q + 1)) // ‖x‖ = 1}) x q hq
    (fun k hk hkn ↦ rationalSphereHomology_isZero q k hk (Nat.ne_of_lt hkn)) a

set_option backward.isDefEq.respectTransparency false in
/-- Rationalization preserves the determinant-sign action on local homology. -/
lemma rationalLinearLocalAction (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (a : relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ n) :
    let f := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
    let hf : Set.MapsTo f ({0} : Set _)ᶜ ({0} : Set _)ᶜ :=
      fun _x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))
    (relativeMap ({0} : Set _)ᶜ ({0} : Set _)ᶜ f hf n).hom a =
      ((SignType.sign (LinearMap.det L.toLinearMap) : ℤ) : ℚ) • a := by
  dsimp only
  let f := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
  let hf : Set.MapsTo f ({0} : Set _)ᶜ ({0} : Set _)ᶜ :=
    fun x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))
  let F := pairMap ({0} : Set _)ᶜ ({0} : Set _)ᶜ f hf
  have hgen := rationalize_coefficient F n (euclideanPositiveLocalClass n)
    (euclideanPositiveLocalClass n) (SignType.sign (LinearMap.det L.toLinearMap))
    (invertible_real_linear_local_homology_action n L (euclideanPositiveLocalClass n))
  have ha : a = rationalLocalCoordinate n a • rationalPositiveLocalClass n := by
    apply (rationalLocalCoordinate n).injective
    rw [map_smul, rationalLocalCoordinate_positive, smul_eq_mul, mul_one]
  change (relativeMap ({0} : Set _)ᶜ ({0} : Set _)ᶜ f hf n).hom a = _
  rw [ha, map_smul]
  change rationalLocalCoordinate n a •
    (SSetPair.homologyMap F rationalCoefficients n).hom (rationalPositiveLocalClass n) = _
  erw [hgen]
  exact smul_comm _ _ _

/-- All four Koszul and local-reflection signs in Dold's sphere collar cancel. -/
lemma sphereCollar_sign (n q : ℕ) :
    (-1 : ℚ) ^ (q * (n - q) + q * q + q + q * (n - q)) = 1 := by
  have he : Even (q * (n - q) + q * q + q + q * (n - q)) := by
    have h := (even_two.mul_right (q * (n - q))).add (Nat.even_mul_succ_self q)
    convert h using 1; ring
  exact he.neg_one_pow

set_option backward.isDefEq.respectTransparency false in
/-- Contracting the second coordinate identifies a relative diagonal with product
by the ordinary point class. The relative coordinate stays fixed. -/
lemma relative_diagonal_of_contraction (X : TopCat.{u}) (A : Set X) (hA : IsOpen A)
    (c : X) (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X c))
    (n : ℕ) (a : relativeHomology X A n) :
    (relativeMap A (productSubspace X X A) (diagonalMap X) (fun _ hx ↦ hx) n).hom a =
      cross X X A n 0 a (pointClass X c) := by
  let HH := (ContinuousMap.Homotopy.refl (ContinuousMap.id X)).prodMk H
  have he := (relative_singular_homotopy_invariance (ModuleCat.{u} ℚ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy A (productSubspace X X A)
      (diagonalMap X).hom (insertPoint X X c).hom
      (fun _ hx ↦ hx) (fun _ hx ↦ hx) HH (by intro t x hx; exact hx))
    coefficients).2 n
  have hu := (rational_relative_homology_cross_product_kunneth X X A hA).2.2.2.2.2.2.2.2.2.2.1
    n a c
  exact (congrArg (fun k ↦ k.hom a) he).trans hu.symm

/-- Straight-line contraction inside a convex normal ball. -/
def convexContraction {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U : Set W) (hU : Convex ℝ U) (c : U) :
    (ContinuousMap.id U).Homotopy (ContinuousMap.const U c) where
  toFun x := ⟨(1 - (x.1 : ℝ)) • x.2.val + (x.1 : ℝ) • c.val,
    hU x.2.property c.property (sub_nonneg.mpr x.1.property.2)
      x.1.property.1 (sub_add_cancel 1 _)⟩
  continuous_toFun := by fun_prop
  map_zero_left := by intro x; apply Subtype.ext; simp
  map_one_left := by intro x; apply Subtype.ext; simp

/-- The normal-ball factor in a sphere collar contributes just its relative
orientation times the degree-zero point class. -/
lemma relative_diagonal_convex {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U : Set W) (hU : Convex ℝ U) (c : U) (A : Set U) (hA : IsOpen A)
    (n : ℕ) (a : relativeHomology (TopCat.of U) A n) :
    (relativeMap A (productSubspace (TopCat.of U) (TopCat.of U) A)
      (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) n).hom a =
      cross (TopCat.of U) (TopCat.of U) A n 0 a (pointClass (TopCat.of U) c) :=
  relative_diagonal_of_contraction (TopCat.of U) A hA c (convexContraction U hU c) n a

section CollarGeometry

variable {T N E : Type u} [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup N] [NormedAddCommGroup E]

/-- Tangent reflection followed by a collar chart, translated to the chart center. -/
def collarReflection (U : Set T) (V : Set N) (h0U : (0 : T) ∈ U)
    (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U) (h : C(U × V, E)) : C(U × V, E) :=
  ⟨fun x ↦ h (⟨-x.1.val, hneg _ x.1.property⟩, x.2) - h (⟨0, h0U⟩, ⟨0, h0V⟩), by fun_prop⟩

/-- Difference between the normal fiber at the center and the central tangent section. -/
def collarDifference (U : Set T) (V : Set N) (h0U : (0 : T) ∈ U)
    (h0V : (0 : N) ∈ V) (h : C(U × V, E)) : C(U × V, E) :=
  ⟨fun x ↦ h (⟨0, h0U⟩, x.2) - h (x.1, ⟨0, h0V⟩), by fun_prop⟩

/-- Sliding the two tangent arguments in opposite directions compares local
intersection with tangent reflection without differentiating the collar chart. -/
def collarDifferenceHomotopy (U : Set T) (V : Set N) (hU : Convex ℝ U)
    (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) :
    (collarReflection U V h0U h0V hneg h).Homotopy (collarDifference U V h0U h0V h) where
  toFun x :=
    h (⟨(1 - (x.1 : ℝ)) • (-x.2.1.val), by
      simpa only [smul_zero, add_zero] using hU (hneg _ x.2.1.property) h0U
        (sub_nonneg.mpr x.1.property.2) x.1.property.1 (sub_add_cancel 1 _)⟩, x.2.2) -
    h (⟨(x.1 : ℝ) • x.2.1.val, by
      simpa only [smul_zero, zero_add] using hU h0U x.2.1.property
        (sub_nonneg.mpr x.1.property.2) x.1.property.1 (sub_add_cancel 1 _)⟩,
      ⟨0, h0V⟩)
  continuous_toFun := by fun_prop
  map_zero_left := by intro x; simp [collarReflection]
  map_one_left := by intro x; simp [collarDifference]

lemma collarDifferenceHomotopy_nonzero (U : Set T) (V : Set N) (hU : Convex ℝ U)
    (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) (hinj : Function.Injective h) (t : unitInterval)
    (x : U × V) (hx : x ≠ (⟨0, h0U⟩, ⟨0, h0V⟩)) :
    collarDifferenceHomotopy U V hU h0U h0V hneg h (t, x) ≠ 0 := by
  intro hz
  have he := hinj (sub_eq_zero.mp hz)
  have hs := congrArg (fun z : U × V ↦ z.1.val) he
  have hn := congrArg (fun z : U × V ↦ z.2.val) he
  change (1 - (t : ℝ)) • (-x.1.val) = (t : ℝ) • x.1.val at hs
  change x.2.val = 0 at hn
  have ht : x.1.val = 0 := by
    have ha : (-1 : ℝ) • x.1.val = 0 := by
      calc
        (-1 : ℝ) • x.1.val = (1 - (t : ℝ)) • (-x.1.val) - (t : ℝ) • x.1.val := by
          rw [smul_neg, ← neg_smul, ← sub_smul]
          congr 1
          ring
        _ = 0 := sub_eq_zero.mpr hs
    simpa only [neg_one_smul, neg_eq_zero] using ha
  apply hx
  exact Prod.ext (Subtype.ext ht) (Subtype.ext hn)

lemma collarReflection_mapsTo (U : Set T) (V : Set N) (hU : Convex ℝ U)
    (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) (hinj : Function.Injective h) :
    Set.MapsTo (collarReflection U V h0U h0V hneg h)
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ := by
  intro x hx
  have hh := collarDifferenceHomotopy_nonzero U V hU h0U h0V hneg h hinj 0 x hx
  simpa only [ContinuousMap.Homotopy.apply_zero, Set.mem_compl_iff, Set.mem_singleton_iff] using hh

lemma collarDifference_mapsTo (U : Set T) (V : Set N) (hU : Convex ℝ U)
    (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) (hinj : Function.Injective h) :
    Set.MapsTo (collarDifference U V h0U h0V h)
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ := by
  intro x hx
  have hh := collarDifferenceHomotopy_nonzero U V hU h0U h0V hneg h hinj 1 x hx
  simpa only [ContinuousMap.Homotopy.apply_one, Set.mem_compl_iff, Set.mem_singleton_iff] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The local collar intersection map induces the same homology map as tangent
reflection followed by its chart. This is the local comparison in Dold §5 Step 3. -/
lemma collarDifference_homology (U : Set T) (V : Set N) (hU : Convex ℝ U)
    (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) (hinj : Function.Injective h)
    (R : ModuleCat.{u} ℚ) (n : ℕ) :
    SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom (collarReflection U V h0U h0V hneg h))
        ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ
        (collarReflection_mapsTo U V hU h0U h0V hneg h hinj)) R n =
    SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom (collarDifference U V h0U h0V h))
        ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ
        (collarDifference_mapsTo U V hU h0U h0V hneg h hinj)) R n := by
  let H := collarDifferenceHomotopy U V hU h0U h0V hneg h
  let A : Set (U × V) := {(⟨0, h0U⟩, ⟨0, h0V⟩)}ᶜ
  have hH : ∀ (t : unitInterval) (x : U × V), x ∈ A → H (t, x) ∈ ({0} : Set E)ᶜ := by
    intro t x hx
    exact collarDifferenceHomotopy_nonzero U V hU h0U h0V hneg h hinj t x hx
  exact (relative_singular_homotopy_invariance (ModuleCat.{u} ℚ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy A ({0} : Set E)ᶜ
      (collarReflection U V h0U h0V hneg h) (collarDifference U V h0U h0V h)
      (collarReflection_mapsTo U V hU h0U h0V hneg h hinj)
      (collarDifference_mapsTo U V hU h0U h0V hneg h hinj) H hH) R).2 n


end CollarGeometry

def tangentReflection (q m : ℕ) :
    EuclideanSpace ℝ (Fin (q + m)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (q + m)) :=
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := q) (m := m)).toLinearEquiv
  e.trans (((LinearEquiv.neg ℝ : EuclideanSpace ℝ (Fin q) ≃ₗ[ℝ] _).prodCongr
    (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin m)))).trans e.symm)

lemma tangentReflection_det (q m : ℕ) :
    LinearMap.det (tangentReflection q m).toLinearMap = (-1 : ℝ) ^ q := by
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := q) (m := m)).toLinearEquiv
  change LinearMap.det (e.symm.toLinearMap ∘ₗ
    (LinearMap.prodMap (-LinearMap.id) LinearMap.id) ∘ₗ e.toLinearMap) = _
  have hc := LinearMap.det_conj
    (LinearMap.prodMap (-LinearMap.id : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] _)
      (LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _)) e.symm
  simp only [LinearEquiv.symm_symm] at hc
  rw [hc, LinearMap.det_prodMap]
  rw [← neg_one_smul ℝ (LinearMap.id : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] _),
    LinearMap.det_smul]
  simp

lemma tangentReflection_sign (q m : ℕ) :
    ((SignType.sign (LinearMap.det (tangentReflection q m).toLinearMap) : ℤ) : ℚ) =
      (-1 : ℚ) ^ q := by
  rw [tangentReflection_det]
  rcases Nat.even_or_odd q with hq | hq
  · rw [hq.neg_one_pow, hq.neg_one_pow]
    norm_num
  · rw [hq.neg_one_pow, hq.neg_one_pow]
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- A pair map inducing an integral isomorphism also induces a rational one. -/
lemma rationalHomologyMap_isIso_of_integral {P Q : SSetPair.{u}} (f : P ⟶ Q) (n : ℕ)
    [IsIso (SSetPair.homologyMap (C := ModuleCat.{u} ℤ) f integralCoefficients.{u} n)] :
    IsIso (SSetPair.homologyMap (C := ModuleCat.{u} ℚ) f rationalCoefficients.{u} n) := by
  have he : SSetPair.homologyMap (C := ModuleCat.{u} ℚ) f rationalCoefficients.{u} n =
      (rationalRelativeHomologyIso P n).inv ≫
        (ModuleCat.extendScalars.{0, 0, u} (Int.castRingHom ℚ)).map
          (SSetPair.homologyMap (C := ModuleCat.{u} ℤ) f integralCoefficients.{u} n) ≫
        (rationalRelativeHomologyIso Q n).hom := by
    apply (cancel_epi (rationalRelativeHomologyIso P n).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using (rationalRelativeHomologyIso_naturality f n).symm
  have hi : IsIso ((rationalRelativeHomologyIso P n).inv ≫
      (ModuleCat.extendScalars.{0, 0, u} (Int.castRingHom ℚ)).map
        (SSetPair.homologyMap (C := ModuleCat.{u} ℤ) f integralCoefficients.{u} n) ≫
      (rationalRelativeHomologyIso Q n).hom) := inferInstance
  exact he.symm ▸ hi

/-- Point-neighborhood excision for the actual rational complex follows by flat
extension from integral excision. -/
lemma rationalPointExcision_isIso (X : TopCat.{u}) [T1Space X] (x : X) (U : Set X)
    (hx : x ∈ interior U) (n : ℕ) :
    IsIso (SSetPair.homologyMap (singularExcisionInclusion X ({x} : Set X)ᶜ U)
      rationalCoefficients.{u} n) := by
  have := point_neighborhood_excision_isIso X x U hx integralCoefficients.{u} n
  exact rationalHomologyMap_isIso_of_integral
    (singularExcisionInclusion X ({x} : Set X)ᶜ U) n

set_option backward.isDefEq.respectTransparency false in
/-- A linear automorphism preserving an open neighborhood acts on its local group
by the same determinant sign as on the ambient point-local group. -/
lemma rationalRestrictedLinearLocalAction (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (hLU : Set.MapsTo L U U)
    (a : relativeHomology (TopCat.of U) {x : U | x.val ≠ 0} n) :
    let f : TopCat.of U ⟶ TopCat.of U := TopCat.ofHom
      ⟨fun x ↦ ⟨L x.val, hLU x.property⟩,
        (L.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk _⟩
    (relativeMap {x : U | x.val ≠ 0} {x : U | x.val ≠ 0} f
      (fun _x hx hz ↦ hx (L.injective (hz.trans L.map_zero.symm))) n).hom a =
      ((SignType.sign (LinearMap.det L.toLinearMap) : ℤ) : ℚ) • a := by
  dsimp only
  let f : TopCat.of U ⟶ TopCat.of U := TopCat.ofHom
    ⟨fun x ↦ ⟨L x.val, hLU x.property⟩,
      (L.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let g := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
  let j : TopCat.of U ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F := pairMap {x : U | x.val ≠ 0} {x : U | x.val ≠ 0} f
    (fun x hx hz ↦ hx (L.injective (hz.trans L.map_zero.symm)))
  let G := pairMap ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ ({0} : Set _)ᶜ g
    (fun x hx hz ↦ hx (L.injective (hz.trans L.map_zero.symm)))
  let J := pairMap {x : U | x.val ≠ 0} ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ j
    (fun x hx ↦ hx)
  have hJ : J = singularExcisionInclusion (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ U := rfl
  have : IsIso (SSetPair.homologyMap J rationalCoefficients n) := by
    rw [hJ]
    have h0int : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior U := by
      rw [hU.interior_eq]
      exact h0
    exact rationalPointExcision_isIso (TopCat.of (EuclideanSpace ℝ (Fin n))) 0 U h0int n
  have hcomm : F ≫ J = J ≫ G := by
    apply MorphismProperty.Arrow.Hom.ext <;>
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ <;>
      rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp] <;> rfl
  apply (ModuleCat.mono_iff_injective (SSetPair.homologyMap J rationalCoefficients n)).mp inferInstance
  change (SSetPair.homologyMap J rationalCoefficients n).hom
    ((SSetPair.homologyMap F rationalCoefficients n).hom a) = _
  have hh := congrArg (fun k ↦ (SSetPair.homologyMap k rationalCoefficients n).hom a) hcomm
  simp only [SSetPair.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  rw [hh, map_smul]
  exact rationalLinearLocalAction n L _

set_option backward.isDefEq.respectTransparency false in
/-- Actual pair homeomorphisms induce rational homology isomorphisms. -/
lemma rationalPairHomeomorph_isIso {X Y : TopCat.{u}} (h : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (hh : ∀ x, h x ∈ B ↔ x ∈ A) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom ⟨h, h.continuous⟩) A B
        (fun x hx ↦ (hh x).2 hx)) rationalCoefficients.{u} n) := by
  let f := singularSubspacePairMap (TopCat.ofHom ⟨h, h.continuous⟩) A B
    (fun x hx ↦ (hh x).2 hx)
  have hi : Function.Bijective (SSetPair.homologyMap f integralCoefficients.{u} n).hom :=
    singular_subspace_homeomorph_homology_bijective h A B hh integralCoefficients n
  have : IsIso (SSetPair.homologyMap f integralCoefficients.{u} n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hi
  exact rationalHomologyMap_isIso_of_integral f n

set_option backward.isDefEq.respectTransparency false in
/-- An open embedding is an isomorphism on point-local rational homology. -/
lemma rationalOpenEmbedding_isIso {X Y : TopCat.{u}} [T1Space Y]
    (f : X ⟶ Y) (hf : _root_.Topology.IsOpenEmbedding f) (x : X) (y : Y) (hxy : f x = y) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularSubspacePairMap f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ
        (fun _z hz he ↦ hz (hf.injective (he.trans hxy.symm)))) rationalCoefficients.{u} n) := by
  let U := Set.range f
  let e : X ≃ₜ U := hf.isEmbedding.toHomeomorph
  let A : Set U := {z | z.val ≠ y}
  have he : ∀ z : X, e z ∈ A ↔ z ∈ ({x} : Set X)ᶜ := by
    intro z
    change f z ≠ y ↔ z ≠ x
    rw [← hxy]
    exact not_congr hf.injective.eq_iff
  let F : singularSubspacePair X ({x} : Set X)ᶜ ⟶
      singularSubspacePair (TopCat.of U) A := singularSubspacePairMap (TopCat.ofHom ⟨e, e.continuous⟩) ({x} : Set X)ᶜ A
    (fun z hz ↦ (he z).2 hz)
  let J := singularExcisionInclusion Y ({y} : Set Y)ᶜ U
  have : IsIso (SSetPair.homologyMap F rationalCoefficients.{u} n) :=
    rationalPairHomeomorph_isIso (X := X) (Y := TopCat.of U) e ({x} : Set X)ᶜ A he n
  have hfx : y ∈ interior U := by
    rw [hf.isOpen_range.interior_eq]
    exact ⟨x, hxy⟩
  have : IsIso (SSetPair.homologyMap J rationalCoefficients.{u} n) :=
    rationalPointExcision_isIso Y y U hfx n
  have hc : F ≫ J = singularSubspacePairMap f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ
      (fun z hz he ↦ hz (hf.injective (he.trans hxy.symm))) := by
    apply MorphismProperty.Arrow.Hom.ext <;>
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ <;>
      rw [← TopCat.toSSet.map_comp] <;> rfl
  rw [← hc, SSetPair.homologyMap_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Local determinant action transports through any open chart intertwining the
map with its linear model. -/
lemma rationalConjugateLinearLocalAction (n : ℕ) (X : TopCat)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (j : X ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)))
    (hj : _root_.Topology.IsOpenEmbedding j) (c : X) (hc : j c = 0)
    (f : X ⟶ X) (hf : Set.MapsTo f ({c} : Set X)ᶜ ({c} : Set X)ᶜ)
    (hcomm : f ≫ j = j ≫ TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv))
    (a : relativeHomology X ({c} : Set X)ᶜ n) :
    (relativeMap ({c} : Set X)ᶜ ({c} : Set X)ᶜ f hf n).hom a =
      ((SignType.sign (LinearMap.det L.toLinearMap) : ℤ) : ℚ) • a := by
  let F := pairMap ({c} : Set X)ᶜ ({c} : Set X)ᶜ f hf
  let G := pairMap ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ ({0} : Set _)ᶜ
    (TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv))
    (fun x hx hz ↦ hx (L.injective (hz.trans L.map_zero.symm)))
  let J := pairMap ({c} : Set X)ᶜ ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ j
    (fun x hx hz ↦ hx (hj.injective (hz.trans hc.symm)))
  have : IsIso (SSetPair.homologyMap J rationalCoefficients.{0} n) :=
    rationalOpenEmbedding_isIso j hj c 0 hc n
  have hsquare : F ≫ J = J ≫ G := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
      congr 1
      apply TopCat.ext
      intro x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom hcomm x.val
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
      exact congrArg TopCat.toSSet.map hcomm
  apply (ModuleCat.mono_iff_injective (SSetPair.homologyMap J rationalCoefficients.{0} n)).mp inferInstance
  change (SSetPair.homologyMap J rationalCoefficients.{0} n).hom
    ((SSetPair.homologyMap F rationalCoefficients.{0} n).hom a) = _
  have hh := congrArg (fun k ↦ (SSetPair.homologyMap k rationalCoefficients.{0} n).hom a) hsquare
  simp only [SSetPair.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  rw [hh, map_smul]
  exact rationalLinearLocalAction n L _

/-- Tangent reflection on a symmetric product neighborhood. -/
def tangentDomainReflection {T N : Type u} [NormedAddCommGroup T] [TopologicalSpace N]
    (U : Set T) (V : Set N) (hneg : ∀ x ∈ U, -x ∈ U) : C(U × V, U × V) :=
  ⟨fun x ↦ (⟨-x.1.val, hneg _ x.1.property⟩, x.2), by fun_prop⟩

lemma tangentDomainReflection_mapsTo {T N : Type u}
    [NormedAddCommGroup T] [NormedAddCommGroup N]
    (U : Set T) (V : Set N) (h0U : (0 : T) ∈ U) (h0V : (0 : N) ∈ V)
    (hneg : ∀ x ∈ U, -x ∈ U) :
    Set.MapsTo (tangentDomainReflection U V hneg)
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ := by
  intro x hx he
  apply hx
  apply Prod.ext
  · apply Subtype.ext
    exact neg_eq_zero.mp (congrArg (fun z : U × V ↦ z.1.val) he)
  · apply Subtype.ext
    have hn := congrArg (fun z : U × V ↦ z.2.val) he
    exact hn

set_option backward.isDefEq.respectTransparency false in
/-- On an open product of q tangent and m normal coordinates, reflection of the
tangent coordinates acts on top local homology by (-1)^q. -/
lemma rationalProductReflectionAction (q m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin q))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : EuclideanSpace ℝ (Fin q)) ∈ U)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (a : relativeHomology (TopCat.of (U × V))
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ (q + m)) :
    (relativeMap ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ
      (TopCat.ofHom (tangentDomainReflection U V hneg))
      (tangentDomainReflection_mapsTo U V h0U h0V hneg) (q + m)).hom a =
      (-1 : ℚ) ^ q • a := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := q) (m := m)
  let j : TopCat.of (U × V) ⟶ TopCat.of (EuclideanSpace ℝ (Fin (q + m))) :=
    TopCat.ofHom ⟨fun x ↦ e.symm (x.1.val, x.2.val), by fun_prop⟩
  have hj : _root_.Topology.IsOpenEmbedding j :=
    e.symm.toHomeomorph.isOpenEmbedding.comp
      (hU.isOpenEmbedding_subtypeVal.prodMap hV.isOpenEmbedding_subtypeVal)
  let c : U × V := (⟨0, h0U⟩, ⟨0, h0V⟩)
  have hc : j c = 0 := e.symm.map_zero
  have hcomm : TopCat.ofHom (tangentDomainReflection U V hneg) ≫ j =
      j ≫ TopCat.ofHom (toContinuousMap (tangentReflection q m).toContinuousLinearEquiv) := by
    apply TopCat.ext
    intro x
    change e.symm (-x.1.val, x.2.val) =
      e.symm (-(e (e.symm (x.1.val, x.2.val))).1, (e (e.symm (x.1.val, x.2.val))).2)
    rw [e.apply_symm_apply]
  have hh := rationalConjugateLinearLocalAction (q + m) (TopCat.of (U × V))
    (tangentReflection q m) j hj c hc (TopCat.ofHom (tangentDomainReflection U V hneg))
    (tangentDomainReflection_mapsTo U V h0U h0V hneg) hcomm a
  rw [tangentReflection_sign] at hh
  exact hh

/-- A collar chart translated to send its center to zero. -/
def centeredChart {T N E : Type u} [TopologicalSpace T] [TopologicalSpace N]
    [NormedAddCommGroup E] (U : Set T) (V : Set N) (c : U × V) (h : C(U × V, E)) : C(U × V, E) :=
  ⟨fun x ↦ h x - h c, by fun_prop⟩

lemma centeredChart_mapsTo {T N E : Type u} [TopologicalSpace T] [TopologicalSpace N]
    [NormedAddCommGroup E] (U : Set T) (V : Set N) (c : U × V)
    (h : C(U × V, E)) (hinj : Function.Injective h) :
    Set.MapsTo (centeredChart U V c h) ({c} : Set (U × V))ᶜ ({0} : Set E)ᶜ := by
  intro x hx hz
  exact hx (hinj (sub_eq_zero.mp hz))

set_option backward.isDefEq.respectTransparency false in
/-- The local difference between the normal fiber and tangent section is
(-1)^q times the centered chart map. Injectivity of the chart is enough. -/
lemma collarDifference_local_action {E : Type} [NormedAddCommGroup E] (q m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin q))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpen U) (hV : IsOpen V) (hconv : Convex ℝ U)
    (h0U : (0 : EuclideanSpace ℝ (Fin q)) ∈ U)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (h : C(U × V, E)) (hinj : Function.Injective h)
    (a : relativeHomology (TopCat.of (U × V))
      ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ (q + m)) :
    (relativeMap ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ
      (TopCat.ofHom (collarDifference U V h0U h0V h))
      (collarDifference_mapsTo U V hconv h0U h0V hneg h hinj) (q + m)).hom a =
      (-1 : ℚ) ^ q •
        (relativeMap ({(⟨0, h0U⟩, ⟨0, h0V⟩)} : Set (U × V))ᶜ ({0} : Set E)ᶜ
          (TopCat.ofHom (centeredChart U V (⟨0, h0U⟩, ⟨0, h0V⟩) h))
          (centeredChart_mapsTo U V (⟨0, h0U⟩, ⟨0, h0V⟩) h hinj) (q + m)).hom a := by
  let c : U × V := (⟨0, h0U⟩, ⟨0, h0V⟩)
  let F := pairMap ({c} : Set (U × V))ᶜ ({c} : Set (U × V))ᶜ
    (TopCat.ofHom (tangentDomainReflection U V hneg))
    (tangentDomainReflection_mapsTo U V h0U h0V hneg)
  let H := pairMap ({c} : Set (U × V))ᶜ ({0} : Set E)ᶜ
    (TopCat.ofHom (centeredChart U V c h)) (centeredChart_mapsTo U V c h hinj)
  have hcomp : F ≫ H = pairMap ({c} : Set (U × V))ᶜ ({0} : Set E)ᶜ
      (TopCat.ofHom (collarReflection U V h0U h0V hneg h))
      (collarReflection_mapsTo U V hconv h0U h0V hneg h hinj) := by
    apply MorphismProperty.Arrow.Hom.ext <;>
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ <;>
      rw [← TopCat.toSSet.map_comp] <;> rfl
  have hh := congrArg (fun k ↦ k.hom a)
    (collarDifference_homology U V hconv h0U h0V hneg h hinj rationalCoefficients.{0} (q + m))
  change (SSetPair.homologyMap
    (pairMap ({c} : Set (U × V))ᶜ ({0} : Set E)ᶜ
      (TopCat.ofHom (collarReflection U V h0U h0V hneg h))
      (collarReflection_mapsTo U V hconv h0U h0V hneg h hinj))
    rationalCoefficients.{0} (q + m)).hom a = _ at hh
  rw [← hcomp, SSetPair.homologyMap_comp] at hh
  change (SSetPair.homologyMap H rationalCoefficients.{0} (q + m)).hom
    ((SSetPair.homologyMap F rationalCoefficients.{0} (q + m)).hom a) = _ at hh
  have hr := rationalProductReflectionAction q m U V hU hV h0U h0V hneg a
  change (SSetPair.homologyMap F rationalCoefficients.{0} (q + m)).hom a = _ at hr
  rw [hr, map_smul] at hh
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
lemma relativeMap_comp {X Y Z : TopCat.{u}} (A : Set X) (B : Set Y) (C : Set Z)
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (g : Y ⟶ Z) (hg : Set.MapsTo g B C) (n : ℕ) :
    relativeMap A C (f ≫ g) (fun _x hx ↦ hg (hf hx)) n =
      relativeMap A B f hf n ≫ relativeMap B C g hg n := by
  have h : pairMap A C (f ≫ g) (fun x hx ↦ hg (hf hx)) =
      pairMap A B f hf ≫ pairMap B C g hg := by
    apply MorphismProperty.Arrow.Hom.ext <;>
      change TopCat.toSSet.map _ = TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ <;>
      rw [← TopCat.toSSet.map_comp]; rfl
  exact (congrArg (fun k ↦ SSetPair.homologyMap k coefficients.{u} n) h).trans
    (SSetPair.homologyMap_comp _ _ _ _)

/-- The collar diagonal with its second normal coordinate contracted to the center. -/
def normalDiagonalMap (X Z : TopCat.{u}) (c : X) :
    TopCat.of (X × Z) ⟶ TopCat.of ((X × Z) × (X × Z)) :=
  TopCat.ofHom ⟨fun x ↦ (x, (c, x.2)), by fun_prop⟩

/-- Reassemble a normal coordinate and two tangent coordinates. -/
def splitDiagonalMap (X Z : TopCat.{u}) (c : X) :
    TopCat.of (X × (Z × Z)) ⟶ TopCat.of ((X × Z) × (X × Z)) :=
  TopCat.ofHom ⟨fun x ↦ ((x.1, x.2.1), (c, x.2.2)), by fun_prop⟩

/-- Contracting only the second normal coordinate preserves the relative first factor. -/
def normalDiagonalHomotopy (X Z : TopCat.{u}) (c : X)
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X c)) :
    (diagonalMap (TopCat.of (X × Z))).hom.Homotopy (normalDiagonalMap X Z c).hom :=
  (ContinuousMap.Homotopy.refl (ContinuousMap.id (X × Z))).prodMk
    (H.prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id Z)))

set_option backward.isDefEq.respectTransparency false in
lemma relativeDiagonal_contract_normal (X Z : TopCat.{u}) (A : Set X) (c : X)
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X c)) (n : ℕ) :
    relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (diagonalMap (TopCat.of (X × Z))) (fun _ hx ↦ hx) n =
    relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (normalDiagonalMap X Z c) (fun _ hx ↦ hx) n := by
  let HH := normalDiagonalHomotopy X Z c H
  exact (relative_singular_homotopy_invariance (ModuleCat.{u} ℚ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (diagonalMap (TopCat.of (X × Z))).hom (normalDiagonalMap X Z c).hom
      (fun _ hx ↦ hx) (fun _ hx ↦ hx) HH (by intro t x hx; exact hx)) coefficients).2 n

set_option backward.isDefEq.respectTransparency false in
/-- The relative diagonal of a normal cross tangent class reduces to the ordinary
tangent diagonal, followed by the literal reassembly map. -/
lemma relativeDiagonal_cross (X Z : TopCat.{u}) (A : Set X) (hA : IsOpen A) (c : X)
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X c))
    (p q : ℕ) (a : relativeHomology X A p) (b : homology Z q) :
    (relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (diagonalMap (TopCat.of (X × Z))) (fun _ hx ↦ hx) (p + q)).hom
        (cross X Z A p q a b) =
    (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
        (cross X (TopCat.of (Z × Z)) A p q a ((homologyMap (diagonalMap Z) q).hom b)) := by
  rw [relativeDiagonal_contract_normal X Z A c H]
  change (relativeMap (productSubspace X Z A)
    (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
    (productMap (𝟙 X) (diagonalMap Z) ≫ splitDiagonalMap X Z c) (fun _ hx ↦ hx)
    (p + q)).hom (cross X Z A p q a b) = _
  rw [relativeMap_comp (productSubspace X Z A)
    (productSubspace X (TopCat.of (Z × Z)) A)
    (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
    (productMap (𝟙 X) (diagonalMap Z)) (fun _ hx ↦ hx)
    (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)]
  change (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
    (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
    (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
    (targetMap A A (𝟙 X) (fun _ hx ↦ hx) (diagonalMap Z) (p + q)
      (cross X Z A p q a b)) = _
  rw [cross_naturality A hA A (𝟙 X) (fun _ hx ↦ hx) (diagonalMap Z), relativeMap_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma splitDiagonal_cross_insert_right (X Z : TopCat.{u}) (A : Set X) (hA : IsOpen A)
    (c : X) (z : Z) (p q : ℕ) (a : relativeHomology X A p) (b : homology Z q) :
    (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
      (cross X (TopCat.of (Z × Z)) A p q a ((homologyMap (insertPoint Z Z z) q).hom b)) =
    (relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (insertPoint (TopCat.of (X × Z)) (TopCat.of (X × Z)) (c, z))
      (fun _ hx ↦ hx) (p + q)).hom (cross X Z A p q a b) := by
  have hn := cross_naturality A hA A (𝟙 X) (fun _ hx ↦ hx) (insertPoint Z Z z) p q a b
  rw [relativeMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  have hc : relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (insertPoint (TopCat.of (X × Z)) (TopCat.of (X × Z)) (c, z))
      (fun _ hx ↦ hx) (p + q) =
    relativeMap (productSubspace X Z A) (productSubspace X (TopCat.of (Z × Z)) A)
      (productMap (𝟙 X) (insertPoint Z Z z)) (fun _ hx ↦ hx) (p + q) ≫
    relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q) :=
    relativeMap_comp (productSubspace X Z A)
      (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (productMap (𝟙 X) (insertPoint Z Z z)) (fun _ hx ↦ hx)
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)
  rw [hc]
  change _ = (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
    (targetMap A A (𝟙 X) (fun _ hx ↦ hx) (insertPoint Z Z z) (p + q) (cross X Z A p q a b))
  rw [hn]

set_option backward.isDefEq.respectTransparency false in
lemma splitDiagonal_cross_insert_left (X Z : TopCat.{u}) (A : Set X) (hA : IsOpen A)
    (c : X) (z : Z) (p q : ℕ) (a : relativeHomology X A p) (b : homology Z q) :
    (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
      (cross X (TopCat.of (Z × Z)) A p q a ((homologyMap (insertPointLeft Z Z z) q).hom b)) =
    cross (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A) p q
      ((relativeMap A (productSubspace X Z A) (insertPoint X Z z) (fun _ hx ↦ hx) p).hom a)
      ((homologyMap (insertPointLeft X Z c) q).hom b) := by
  have hn := cross_naturality A hA A (𝟙 X) (fun _ hx ↦ hx) (insertPointLeft Z Z z) p q a b
  rw [relativeMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  rw [← hn]
  have hc : relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (productMap (insertPoint X Z z) (insertPointLeft X Z c)) (fun _ hx ↦ hx) (p + q) =
    relativeMap (productSubspace X Z A) (productSubspace X (TopCat.of (Z × Z)) A)
      (productMap (𝟙 X) (insertPointLeft Z Z z)) (fun _ hx ↦ hx) (p + q) ≫
    relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q) :=
    relativeMap_comp (productSubspace X Z A)
      (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (productMap (𝟙 X) (insertPointLeft Z Z z)) (fun _ hx ↦ hx)
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)
  have he := congrArg (fun k ↦ k.hom (cross X Z A p q a b)) hc
  change targetMap A (productSubspace X Z A) (insertPoint X Z z) (fun _ hx ↦ hx)
    (insertPointLeft X Z c) (p + q) (cross X Z A p q a b) = _ at he
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
  change targetMap A (productSubspace X Z A) (insertPoint X Z z) (fun _ hx ↦ hx)
      (insertPointLeft X Z c) (p + q) (cross X Z A p q a b) =
    (relativeMap (productSubspace X (TopCat.of (Z × Z)) A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (splitDiagonalMap X Z c) (fun _ hx ↦ hx) (p + q)).hom
      (targetMap A A (𝟙 X) (fun _ hx ↦ hx) (insertPointLeft Z Z z) (p + q)
        (cross X Z A p q a b)) at he
  rw [← he]
  exact cross_naturality (X := X) (Z := Z) (X' := TopCat.of (X × Z))
    (Z' := TopCat.of (X × Z)) A hA (productSubspace X Z A) (insertPoint X Z z)
    (fun _ hx ↦ hx) (insertPointLeft X Z c) p q a b

set_option backward.isDefEq.respectTransparency false in
/-- Dold's two-term relative diagonal formula on a sphere collar. Taking the normal
factor first makes its sign positive in both terms. -/
lemma relativeSphereCollar_diagonal (X Z : TopCat.{u}) [PathConnectedSpace Z]
    (A : Set X) (hA : IsOpen A) (c : X) (z : Z)
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X c))
    (p q : ℕ) (hq : 0 < q)
    (hZ : ∀ k : ℕ, 0 < k → k < q → IsZero (homology Z k))
    (a : relativeHomology X A p) (b : homology Z q) :
    (relativeMap (productSubspace X Z A)
      (productSubspace (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A))
      (diagonalMap (TopCat.of (X × Z))) (fun _ hx ↦ hx) (p + q)).hom
        (cross X Z A p q a b) =
    cross (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A) (p + q) 0
      (cross X Z A p q a b) (pointClass (TopCat.of (X × Z)) (c, z)) +
    cross (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A) p q
      ((relativeMap A (productSubspace X Z A) (insertPoint X Z z) (fun _ hx ↦ hx) p).hom a)
      ((homologyMap (insertPointLeft X Z c) q).hom b) := by
  rw [relativeDiagonal_cross X Z A hA c H, homology_diagonal_factor_sum Z z q hq hZ b]
  have hadd (u v : homology (TopCat.of (Z × Z)) q) :
      cross X (TopCat.of (Z × Z)) A p q a (u + v) =
        cross X (TopCat.of (Z × Z)) A p q a u + cross X (TopCat.of (Z × Z)) A p q a v := by
    simp only [cross, TensorProduct.tmul_add, map_add]
  rw [hadd, map_add, splitDiagonal_cross_insert_right X Z A hA c z,
    splitDiagonal_cross_insert_left X Z A hA c z]
  have hprod : IsOpen (productSubspace X Z A) := hA.preimage continuous_fst
  have hu := (rational_relative_homology_cross_product_kunneth
    (TopCat.of (X × Z)) (TopCat.of (X × Z)) (productSubspace X Z A) hprod).2.2.2.2.2.2.2.2.2.2.1
    (p + q) (cross X Z A p q a b) (c, z)
  rw [hu]

set_option backward.isDefEq.respectTransparency false in
/-- Swapping two absolute factors of the same degree contributes its Koszul sign. -/
lemma absoluteCross_swap_same_degree (X Z : TopCat.{u}) (q : ℕ)
    (a : homology X q) (b : homology Z q) :
    (homologyMap (swapMap X Z) (q + q)).hom (absoluteCross X Z q q a b) =
      (-1 : ℚ) ^ (q * q) • absoluteCross Z X q q b a := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (chains X) q a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
  simp only [absoluteCross, absoluteCrossTensor, quotientTensor_cycleClass,
    absoluteCycleClasses, LinearMap.compr₂_apply]
  rw [← (cycleClass (chains (TopCat.of (Z × X))) (q + q)).map_smul]
  apply cycleClass_map
  change (SSet.chainComplexMap (TopCat.toSSet.map (swapMap X Z)) coefficients.{u}).f (q + q)
    (SignedShuffle.shuffleBilinear X Z q q a.val b.val) =
      (-1 : ℚ) ^ (q * q) • SignedShuffle.shuffleBilinear Z X q q b.val a.val
  simpa only [SignedShuffle.regrade, LinearMap.id_apply, swapMap, coefficients] using
    SignedShuffle.shuffleBilinear_swap X Z q q a.val b.val

lemma relativeMap_regrade {X Y : TopCat.{u}} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) {i j : ℕ} (h : i = j)
    (a : relativeHomology X A i) :
    (relativeMap A B f hf j).hom (regradeRelative X A h a) =
      regradeRelative Y B h ((relativeMap A B f hf i).hom a) := by
  subst j
  rfl

/-- Transpose the two absolute factors while retaining the first relative factor. -/
def middleSwapMap (X Z W : TopCat.{u}) :
    TopCat.of ((X × Z) × W) ⟶ TopCat.of ((X × W) × Z) :=
  TopCat.ofHom ⟨fun x ↦ ((x.1.1, x.2), x.1.2), by fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
/-- The middle transposition in Dold's support operator has sign (-1)^(q*q). -/
lemma cross_middle_swap_same_degree (X Z W : TopCat.{u}) (A : Set X) (hA : IsOpen A)
    (p q : ℕ) (a : relativeHomology X A p) (b : homology Z q) (c : homology W q) :
    (relativeMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A))
      (productSubspace (TopCat.of (X × W)) Z (productSubspace X W A))
      (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + q)).hom
      (cross (TopCat.of (X × Z)) W (productSubspace X Z A) (p + q) q
        (cross X Z A p q a b) c) =
    (-1 : ℚ) ^ (q * q) •
      cross (TopCat.of (X × W)) Z (productSubspace X W A) (p + q) q
        (cross X W A p q a c) b := by
  let A₁ := productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A)
  let A₂ := productSubspace (TopCat.of (X × W)) Z (productSubspace X W A)
  let B₁ := productSubspace X (TopCat.of (Z × W)) A
  let B₂ := productSubspace X (TopCat.of (W × Z)) A
  let M := relativeMap A₁ A₂ (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + q)
  let J₁ := relativeMap A₁ B₁ (associatorMap X Z W) (fun _ hx ↦ hx) ((p + q) + q)
  let J₂ := relativeMap A₂ B₂ (associatorMap X W Z) (fun _ hx ↦ hx) ((p + q) + q)
  let F := productMap (𝟙 X) (swapMap Z W)
  have : IsIso J₂ := rationalPairHomeomorph_isIso
    (X := TopCat.of ((X × W) × Z)) (Y := TopCat.of (X × (W × Z)))
    (Homeomorph.prodAssoc X W Z) A₂ B₂ (fun _ ↦ Iff.rfl) ((p + q) + q)
  have hcomm : M ≫ J₂ = J₁ ≫ relativeMap B₁ B₂ F (fun _ hx ↦ hx) ((p + q) + q) := by
    rw [← relativeMap_comp A₁ A₂ B₂ (middleSwapMap X Z W) (fun _ hx ↦ hx)
      (associatorMap X W Z) (fun _ hx ↦ hx),
      ← relativeMap_comp A₁ B₁ B₂ (associatorMap X Z W) (fun _ hx ↦ hx) F (fun _ hx ↦ hx)]
    rfl
  have h₁ := (rational_relative_homology_cross_product_kunneth X Z A hA).2.2.2.2.2.2.2.2.2.1
    W p q q a b c
  have h₂ := (rational_relative_homology_cross_product_kunneth X W A hA).2.2.2.2.2.2.2.2.2.1
    Z p q q a c b
  apply (ModuleCat.mono_iff_injective J₂).mp inferInstance
  change J₂.hom (M.hom _) = J₂.hom ((-1 : ℚ) ^ (q * q) • _)
  rw [map_smul]
  change (M ≫ J₂).hom _ = _
  rw [hcomm]
  change (relativeMap B₁ B₂ F (fun _ hx ↦ hx) ((p + q) + q)).hom (J₁.hom _) = _
  change J₁.hom _ = _ at h₁
  change J₂.hom _ = _ at h₂
  rw [h₁, h₂]
  rw [relativeMap_regrade B₁ B₂ F (fun _ hx ↦ hx)]
  have hn := cross_naturality A hA A (𝟙 X) (fun _ hx ↦ hx) (swapMap Z W)
    p (q + q) a (absoluteCross Z W q q b c)
  rw [relativeMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  have hs : (relativeMap B₁ B₂ F (fun _ hx ↦ hx) (p + (q + q))).hom
      (cross X (TopCat.of (Z × W)) A p (q + q) a (absoluteCross Z W q q b c)) =
      (-1 : ℚ) ^ (q * q) • cross X (TopCat.of (W × Z)) A p (q + q) a
        (absoluteCross W Z q q c b) := by
    change targetMap A A (𝟙 X) (fun _ hx ↦ hx) (swapMap Z W) (p + (q + q)) _ = _
    rw [hn, absoluteCross_swap_same_degree]
    simp only [cross, TensorProduct.tmul_smul, map_smul]
  rw [hs, map_smul]

/-- Evaluate the relative first and absolute third factors, retaining the middle factor. -/
def exchangeEvaluationMap {X Z W Y : TopCat.{u}} (d : TopCat.of (X × W) ⟶ Y) :
    TopCat.of ((X × Z) × W) ⟶ TopCat.of (Y × Z) :=
  TopCat.ofHom ⟨fun x ↦ (d (x.1.1, x.2), x.1.2), by fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
/-- After the middle transposition, evaluation of the outer factors is ordinary
cross-product naturality. -/
lemma exchangeEvaluation_cross {X Z W Y : TopCat.{u}} (A : Set X) (hA : IsOpen A)
    (D : Set Y) (d : TopCat.of (X × W) ⟶ Y)
    (hd : Set.MapsTo d (productSubspace X W A) D)
    (p q : ℕ) (a : relativeHomology X A p) (b : homology Z q) (c : homology W q) :
    (relativeMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A))
      (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
      (fun _x hx ↦ hd hx) ((p + q) + q)).hom
      (cross (TopCat.of (X × Z)) W (productSubspace X Z A) (p + q) q
        (cross X Z A p q a b) c) =
    (-1 : ℚ) ^ (q * q) • cross Y Z D (p + q) q
      ((relativeMap (productSubspace X W A) D d hd (p + q)).hom (cross X W A p q a c)) b := by
  let A₁ := productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A)
  let A₂ := productSubspace (TopCat.of (X × W)) Z (productSubspace X W A)
  have hc : relativeMap A₁ (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
      (fun x hx ↦ hd hx) ((p + q) + q) =
    relativeMap A₁ A₂ (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + q) ≫
    relativeMap A₂ (productSubspace Y Z D) (productMap d (𝟙 Z)) (fun x hx ↦ hd hx)
      ((p + q) + q) :=
    relativeMap_comp A₁ A₂ (productSubspace Y Z D) (middleSwapMap X Z W) (fun _ hx ↦ hx)
      (productMap d (𝟙 Z)) (fun x hx ↦ hd hx) ((p + q) + q)
  rw [hc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cross_middle_swap_same_degree X Z W A hA, map_smul]
  have hn := cross_naturality (productSubspace X W A) (hA.preimage continuous_fst) D d hd (𝟙 Z)
    (p + q) q (cross X W A p q a c) b
  rw [homologyMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  exact congrArg ((-1 : ℚ) ^ (q * q) • ·) hn

set_option backward.isDefEq.respectTransparency false in
/-- If the retained middle factor is a point class, evaluation inserts that point
after evaluating the outer factors. -/
lemma exchangeEvaluation_cross_point {X Z W Y : TopCat.{u}} (A : Set X) (hA : IsOpen A)
    (D : Set Y) (d : TopCat.of (X × W) ⟶ Y)
    (hd : Set.MapsTo d (productSubspace X W A) D)
    (p q : ℕ) (a : relativeHomology X A p) (z : Z) (c : homology W q) :
    (relativeMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A))
      (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
      (fun _x hx ↦ hd hx) (p + q)).hom
      (cross (TopCat.of (X × Z)) W (productSubspace X Z A) p q
        (cross X Z A p 0 a (pointClass Z z)) c) =
    (relativeMap D (productSubspace Y Z D) (insertPoint Y Z z) (fun _ hx ↦ hx) (p + q)).hom
      ((relativeMap (productSubspace X W A) D d hd (p + q)).hom (cross X W A p q a c)) := by
  have hu := (rational_relative_homology_cross_product_kunneth X Z A hA).2.2.2.2.2.2.2.2.2.2.1 p a z
  rw [hu]
  have hn := cross_naturality A hA (productSubspace X Z A) (insertPoint X Z z)
    (fun _ hx ↦ hx) (𝟙 W) p q a c
  rw [homologyMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  rw [← hn]
  let B := productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A)
  have hc : relativeMap (productSubspace X W A) B (productMap (insertPoint X Z z) (𝟙 W))
      (fun _ hx ↦ hx) (p + q) ≫
      relativeMap B (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
        (fun x hx ↦ hd hx) (p + q) =
    relativeMap (productSubspace X W A) D d hd (p + q) ≫
      relativeMap D (productSubspace Y Z D) (insertPoint Y Z z) (fun _ hx ↦ hx) (p + q) := by
    rw [← relativeMap_comp (productSubspace X W A) B (productSubspace Y Z D)
      (productMap (insertPoint X Z z) (𝟙 W)) (fun _ hx ↦ hx)
      (exchangeEvaluationMap (Z := Z) d) (fun x hx ↦ hd hx),
      ← relativeMap_comp (productSubspace X W A) D (productSubspace Y Z D) d hd
        (insertPoint Y Z z) (fun _ hx ↦ hx)]
    rfl
  exact congrArg (fun k ↦ k.hom (cross X W A p q a c)) hc

set_option backward.isDefEq.respectTransparency false in
/-- The concrete support map is the diagonal followed by evaluation of the first
and third factors. This connects Dold's tensor expression to the original map. -/
lemma supportValue_diagonal {E : Type} [NormedAddCommGroup E] (U K : Set E)
    (hK : IsClosed K) (p q : ℕ)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (z : homology (TopCat.of K) q) :
    supportValue U K p q a z =
    (relativeMap (X := TopCat.of ((U × U) × K)) (Y := TopCat.of (E × U))
      (productSubspace (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)))
      (productSubspace (TopCat.of E) (TopCat.of U) ({0} : Set E)ᶜ)
      (exchangeEvaluationMap (X := TopCat.of U) (Z := TopCat.of U)
        (W := TopCat.of K) (Y := TopCat.of E) (TopCat.ofHom (difference U K)))
      (fun _ hx ↦ difference_mapsTo U K hx) (p + q)).hom
      (cross (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) p q
        ((relativeMap (X := TopCat.of U) (Y := TopCat.of (U × U)) (supportComplement U K)
          (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
          (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) p).hom a) z) := by
  let A := supportComplement U K
  let B := productSubspace (TopCat.of U) (TopCat.of U) A
  let C := productSubspace (TopCat.of (U × U)) (TopCat.of K) B
  let D := productSubspace (TopCat.of E) (TopCat.of U) ({0} : Set E)ᶜ
  let d := exchangeEvaluationMap (X := TopCat.of U) (Z := TopCat.of U)
        (W := TopCat.of K) (Y := TopCat.of E) (TopCat.ofHom (difference U K))
  have hA : IsOpen A := hK.isOpen_compl.preimage continuous_subtype_val
  have hn := cross_naturality (X := TopCat.of U) (Z := TopCat.of K)
    (X' := TopCat.of (U × U)) (Z' := TopCat.of K) A hA B (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx)
    (𝟙 (TopCat.of K)) p q a z
  rw [homologyMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  have hc : relativeMap (productSubspace (TopCat.of U) (TopCat.of K) A) D
      (TopCat.ofHom (supportMap U K))
      (fun _ hx ↦ difference_mapsTo U K hx) (p + q) =
    relativeMap (productSubspace (TopCat.of U) (TopCat.of K) A) C
      (productMap (diagonalMap (TopCat.of U)) (𝟙 (TopCat.of K))) (fun _ hx ↦ hx) (p + q) ≫
      relativeMap C D d (fun _ hx ↦ difference_mapsTo U K hx) (p + q) :=
    relativeMap_comp (productSubspace (TopCat.of U) (TopCat.of K) A) C D
      (productMap (diagonalMap (TopCat.of U)) (𝟙 (TopCat.of K))) (fun _ hx ↦ hx) d
      (fun _ hx ↦ difference_mapsTo U K hx) (p + q)
  change (relativeMap (productSubspace (TopCat.of U) (TopCat.of K) A) D
      (TopCat.ofHom (supportMap U K))
      (fun _ hx ↦ difference_mapsTo U K hx) (p + q)).hom
        (cross (TopCat.of U) (TopCat.of K) A p q a z) = _
  rw [hc]
  change (relativeMap C D d (fun _ hx ↦ difference_mapsTo U K hx) (p + q)).hom
    (targetMap A B (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) (𝟙 (TopCat.of K))
      (p + q) (cross (TopCat.of U) (TopCat.of K) A p q a z)) = _
  rw [hn]

set_option backward.isDefEq.respectTransparency false in
/-- For a two-term collar diagonal, local homology concentration kills the
point-factor term. The remaining term has the middle-transposition sign. -/
lemma supportValue_of_two_term_diagonal (p q : ℕ) (hq : 0 < q)
    (U K : Set (EuclideanSpace ℝ (Fin (p + q)))) (hK : IsClosed K)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) (p + q))
    (b : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (c : homology (TopCat.of U) q) (u : U)
    (ha : (relativeMap (X := TopCat.of U) (Y := TopCat.of (U × U)) (supportComplement U K)
      (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
      (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) (p + q)).hom a =
      cross (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q) 0 a
        (pointClass (TopCat.of U) u) +
      cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q b c)
    (z : homology (TopCat.of K) q) :
    supportValue U K (p + q) q a z =
    (-1 : ℚ) ^ (q * q) •
      cross (TopCat.of (EuclideanSpace ℝ (Fin (p + q)))) (TopCat.of U)
        ({0} : Set _)ᶜ (p + q) q
        ((relativeMap (X := TopCat.of (U × K))
          (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + q)))) (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
          ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
          (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom
          (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q b z)) c := by
  let A := supportComplement U K
  have hA : IsOpen A := hK.isOpen_compl.preimage continuous_subtype_val
  rw [supportValue_diagonal U K hK, ha]
  simp only [cross, TensorProduct.add_tmul, map_add]
  change _ + _ = _
  have hpoint := exchangeEvaluation_cross_point (X := TopCat.of U) (Z := TopCat.of U)
    (W := TopCat.of K) (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + q)))) A hA
    ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
    (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q) q a u z
  have hzero : (relativeMap (productSubspace (TopCat.of U) (TopCat.of K) A)
      ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) ((p + q) + q)).hom
      (cross (TopCat.of U) (TopCat.of K) A (p + q) q a z) = 0 := by
    have : Subsingleton (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (p + q))))
        ({0} : Set _)ᶜ ((p + q) + q)) := ModuleCat.subsingleton_of_isZero
      (rationalLocalHomology_isZero (p + q) ((p + q) + q) (by omega))
    exact Subsingleton.elim _ _
  rw [hzero, map_zero] at hpoint
  have hsecond := exchangeEvaluation_cross (X := TopCat.of U) (Z := TopCat.of U)
    (W := TopCat.of K) (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + q)))) A hA
    ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
    (TopCat.ofHom (difference U K)) (difference_mapsTo U K) p q b c z
  exact (congrArg₂ (· + ·) hpoint hsecond).trans (zero_add _)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of local homology actions can be checked in any open chart through
that point, since point excision makes the chart map an isomorphism. -/
lemma relativeMap_smul_of_open_chart {X Y Z : TopCat.{u}} [T1Space X]
    (j : Z ⟶ X) (hj : _root_.Topology.IsOpenEmbedding j)
    (z : Z) (x : X) (hz : j z = x) (B : Set Y)
    (f g : X ⟶ Y) (hf : Set.MapsTo f ({x} : Set X)ᶜ B)
    (hg : Set.MapsTo g ({x} : Set X)ᶜ B) (n : ℕ) (s : ℚ)
    (he : ∀ a : relativeHomology Z ({z} : Set Z)ᶜ n,
      (relativeMap ({z} : Set Z)ᶜ B (j ≫ f)
        (hf.comp (fun _t ht h ↦ ht (hj.injective (h.trans hz.symm)))) n).hom a =
      s • (relativeMap ({z} : Set Z)ᶜ B (j ≫ g)
        (hg.comp (fun _t ht h ↦ ht (hj.injective (h.trans hz.symm)))) n).hom a)
    (a : relativeHomology X ({x} : Set X)ᶜ n) :
    (relativeMap ({x} : Set X)ᶜ B f hf n).hom a =
      s • (relativeMap ({x} : Set X)ᶜ B g hg n).hom a := by
  let hjp : Set.MapsTo j ({z} : Set Z)ᶜ ({x} : Set X)ᶜ :=
    fun t ht h ↦ ht (hj.injective (h.trans hz.symm))
  let J := relativeMap ({z} : Set Z)ᶜ ({x} : Set X)ᶜ j hjp n
  have : IsIso J := rationalOpenEmbedding_isIso j hj z x hz n
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective J).mp inferInstance a
  have h := he b
  rw [relativeMap_comp ({z} : Set Z)ᶜ ({x} : Set X)ᶜ B j hjp f hf n,
    relativeMap_comp ({z} : Set Z)ᶜ ({x} : Set X)ᶜ B j hjp g hg n] at h
  exact h

/-- Difference of the normal fiber and the central section of a product collar. -/
def normalFirstDifference {N S E : Type u} [TopologicalSpace N] [TopologicalSpace S]
    [NormedAddCommGroup E] (b : N) (s : S) (h : C(N × S, E)) : C(N × S, E) :=
  ⟨fun x ↦ h (x.1, s) - h (b, x.2), by fun_prop⟩

lemma normalFirstDifference_mapsTo {N S E : Type u}
    [TopologicalSpace N] [TopologicalSpace S] [NormedAddCommGroup E]
    (b : N) (s : S) (h : C(N × S, E)) (hinj : Function.Injective h) :
    Set.MapsTo (normalFirstDifference b s h) ({(b, s)} : Set (N × S))ᶜ ({0} : Set E)ᶜ := by
  intro x hx hz
  have he : (x.1, s) = (b, x.2) := hinj (sub_eq_zero.mp hz)
  have hb := congrArg (fun y : N × S ↦ y.1) he
  have hs := congrArg (fun y : N × S ↦ y.2) he
  exact hx (Prod.ext hb hs.symm)

/-- Translate any chart to send its chosen center to the origin. -/
def centeredMap {X E : Type u} [TopologicalSpace X] [NormedAddCommGroup E]
    (h : C(X, E)) (x : X) : C(X, E) := ⟨fun y ↦ h y - h x, by fun_prop⟩

lemma centeredMap_mapsTo {X E : Type u} [TopologicalSpace X] [NormedAddCommGroup E]
    (h : C(X, E)) (hinj : Function.Injective h) (x : X) :
    Set.MapsTo (centeredMap h x) ({x} : Set X)ᶜ ({0} : Set E)ᶜ := by
  intro y hy hz
  exact hy (hinj (sub_eq_zero.mp hz))

set_option backward.isDefEq.respectTransparency false in
/-- A chart of the central q-dimensional section gives the same local difference
sign throughout a product collar. The normal factor is written first. -/
lemma normalFirstDifference_local_action {S E : Type} [TopologicalSpace S] [T1Space S]
    [NormedAddCommGroup E] (q m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin q))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpen U) (hV : IsOpen V) (hconv : Convex ℝ U)
    (h0U : (0 : EuclideanSpace ℝ (Fin q)) ∈ U)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (φ : C(U, S)) (hφ : _root_.Topology.IsOpenEmbedding φ)
    (h : C(V × S, E)) (hinj : Function.Injective h)
    (a : relativeHomology (TopCat.of (V × S))
      ({(⟨0, h0V⟩, φ ⟨0, h0U⟩)} : Set (V × S))ᶜ (q + m)) :
    (relativeMap (X := TopCat.of (V × S)) (Y := TopCat.of E)
      ({(⟨0, h0V⟩, φ ⟨0, h0U⟩)} : Set (V × S))ᶜ ({0} : Set E)ᶜ
      (TopCat.ofHom (normalFirstDifference ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h))
      (normalFirstDifference_mapsTo ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h hinj) (q + m)).hom a =
      (-1 : ℚ) ^ q •
        (relativeMap (X := TopCat.of (V × S)) (Y := TopCat.of E)
          ({(⟨0, h0V⟩, φ ⟨0, h0U⟩)} : Set (V × S))ᶜ ({0} : Set E)ᶜ
          (TopCat.ofHom (centeredMap h (⟨0, h0V⟩, φ ⟨0, h0U⟩)))
          (centeredMap_mapsTo h hinj _) (q + m)).hom a := by
  let j : TopCat.of (U × V) ⟶ TopCat.of (V × S) :=
    TopCat.ofHom ⟨fun x ↦ (x.2, φ x.1), by fun_prop⟩
  have hj : _root_.Topology.IsOpenEmbedding j :=
    (Homeomorph.prodComm S V).isOpenEmbedding.comp
      (hφ.prodMap (Homeomorph.refl V).isOpenEmbedding)
  let h' : C(U × V, E) := h.comp j.hom
  have hh' : Function.Injective h' := hinj.comp hj.injective
  apply relativeMap_smul_of_open_chart j hj (⟨0, h0U⟩, ⟨0, h0V⟩)
    (⟨0, h0V⟩, φ ⟨0, h0U⟩) rfl ({0} : Set E)ᶜ
    (TopCat.ofHom (normalFirstDifference ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h))
    (TopCat.ofHom (centeredMap h (⟨0, h0V⟩, φ ⟨0, h0U⟩)))
    (normalFirstDifference_mapsTo ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h hinj)
    (centeredMap_mapsTo h hinj _) (q + m) ((-1 : ℚ) ^ q) _ a
  intro b
  exact collarDifference_local_action q m U V hU hV hconv h0U h0V hneg h' hh' b

set_option backward.isDefEq.respectTransparency false in
/-- If the first relative homology is one-dimensional in degree p and zero
elsewhere, every product class is its generator crossed with a class of degree q. -/
lemma relativeCross_surjective_of_concentrated (X Z : TopCat.{u}) (A : Set X)
    (p q : ℕ) (e : relativeHomology X A p ≃ₗ[ℚ] ℚ)
    (hzero : ∀ k, k ≠ p → Subsingleton (relativeHomology X A k))
    (a : kunnethTarget X Z A (p + q)) :
    ∃ b : homology Z q, cross X Z A p q (e.symm 1) b = a := by
  classical
  obtain ⟨t, rfl⟩ := (kunnethMap_bijective X Z A (p + q)).2 a
  induction t using DirectSum.induction_on with
  | zero => exact ⟨0, by simp [cross]⟩
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by simp only [cross, TensorProduct.tmul_add, map_add] at *; rw [ha', hb']⟩
  | of i t =>
    by_cases hi : i.val.1 = p
    · have hiq : i.val.2 = q := by have := i.property; omega
      have hieq : i = ⟨(p, q), rfl⟩ := Subtype.ext (Prod.ext hi hiq)
      subst i
      induction t using TensorProduct.inductionOn with
      | add a b ha hb =>
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        exact ⟨a' + b', by simp only [cross, TensorProduct.tmul_add, map_add] at *; rw [ha', hb']⟩
      | tmul a b =>
        refine ⟨e a • b, ?_⟩
        change cross X Z A p q (e.symm 1) (e a • b) = kunnethMap X Z A (p + q)
          (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b))
        have hc : cross X Z A p q (e.symm 1) (e a • b) = cross X Z A p q a b := by
          have ha : a = e a • e.symm 1 := by apply e.injective; simp
          conv_rhs => rw [ha]
          simp only [cross, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        simpa [kunnethMap, cross, regradeRelative] using hc
    · have := hzero i.val.1 hi
      have ht : t = 0 := Subsingleton.elim _ _
      subst t
      exact ⟨0, by simp [cross]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The point-local collar difference identity already holds on the original
normal-support pair: both maps factor through localization at the chart center. -/
lemma normalFirstDifference_support_action {S E : Type} [TopologicalSpace S] [T1Space S]
    [NormedAddCommGroup E] (q m n : ℕ) (hn : n = q + m)
    (U : Set (EuclideanSpace ℝ (Fin q))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpen U) (hV : IsOpen V) (hconv : Convex ℝ U)
    (h0U : (0 : EuclideanSpace ℝ (Fin q)) ∈ U)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V) (hneg : ∀ x ∈ U, -x ∈ U)
    (φ : C(U, S)) (hφ : _root_.Topology.IsOpenEmbedding φ)
    (h : C(V × S, E)) (hinj : Function.Injective h)
    (A : Set (V × S)) (hA : A ⊆ ({(⟨0, h0V⟩, φ ⟨0, h0U⟩)} : Set (V × S))ᶜ)
    (a : relativeHomology (TopCat.of (V × S)) A n) :
    (relativeMap (X := TopCat.of (V × S)) (Y := TopCat.of E)
      A ({0} : Set E)ᶜ
      (TopCat.ofHom (normalFirstDifference ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h))
      (fun _x hx ↦ normalFirstDifference_mapsTo ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h hinj (hA hx))
      n).hom a =
      (-1 : ℚ) ^ q •
        (relativeMap (X := TopCat.of (V × S)) (Y := TopCat.of E)
          A ({0} : Set E)ᶜ
          (TopCat.ofHom (centeredMap h (⟨0, h0V⟩, φ ⟨0, h0U⟩)))
          (fun _x hx ↦ centeredMap_mapsTo h hinj _ (hA hx)) n).hom a := by
  subst n
  let B : Set (V × S) := ({(⟨0, h0V⟩, φ ⟨0, h0U⟩)} : Set (V × S))ᶜ
  let J := relativeMap (X := TopCat.of (V × S)) (Y := TopCat.of (V × S)) A B (𝟙 (TopCat.of (V × S))) (fun _ hx ↦ hA hx) (q + m)
  have he := normalFirstDifference_local_action q m U V hU hV hconv h0U h0V hneg
    φ hφ h hinj (J.hom a)
  have hc₁ := relativeMap_comp A B ({0} : Set E)ᶜ (𝟙 (TopCat.of (V × S))) (fun _ hx ↦ hA hx)
    (TopCat.ofHom (normalFirstDifference ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h))
    (normalFirstDifference_mapsTo ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h hinj) (q + m)
  have hc₂ := relativeMap_comp A B ({0} : Set E)ᶜ (𝟙 (TopCat.of (V × S))) (fun _ hx ↦ hA hx)
    (TopCat.ofHom (centeredMap h (⟨0, h0V⟩, φ ⟨0, h0U⟩)))
    (centeredMap_mapsTo h hinj _) (q + m)
  change relativeMap A ({0} : Set E)ᶜ
    (TopCat.ofHom (normalFirstDifference ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h))
    (fun x hx ↦ normalFirstDifference_mapsTo ⟨0, h0V⟩ (φ ⟨0, h0U⟩) h hinj (hA hx))
    (q + m) = _ at hc₁
  change relativeMap A ({0} : Set E)ᶜ
    (TopCat.ofHom (centeredMap h (⟨0, h0V⟩, φ ⟨0, h0U⟩)))
    (fun x hx ↦ centeredMap_mapsTo h hinj _ (hA hx)) (q + m) = _ at hc₂
  rw [hc₁, hc₂]
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion of a punctured subspace into the ambient pointed pair. -/
def pointLocalInclusion (X : TopCat.{u}) (U : Set X) (x : U) (k : ℕ) :
    relativeHomology (TopCat.of U) ({x} : Set U)ᶜ k ⟶
      relativeHomology X ({x.val} : Set X)ᶜ k :=
  relativeMap (X := TopCat.of U) (Y := X) ({x} : Set U)ᶜ ({x.val} : Set X)ᶜ
    (TopCat.ofHom ⟨(fun y : U ↦ y.val), continuous_subtype_val⟩)
    (fun _y hy he ↦ hy (Subtype.ext he)) k

lemma pointLocalInclusion_isIso (X : TopCat.{u}) [T1Space X] (U : Set X)
    (hU : IsOpen U) (x : U) (k : ℕ) : IsIso (pointLocalInclusion X U x k) :=
  rationalOpenEmbedding_isIso (X := TopCat.of U) (Y := X)
    (TopCat.ofHom ⟨(fun y : U ↦ y.val), continuous_subtype_val⟩)
    hU.isOpenEmbedding_subtypeVal x x.val rfl k

/-- The inclusion used for the local normal coordinate. -/
abbrev openLocalInclusion (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U) (k : ℕ) :=
  pointLocalInclusion.{0} (TopCat.of (EuclideanSpace ℝ (Fin n))) U ⟨0, h0⟩ k

lemma openLocalInclusion_isIso (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U) (k : ℕ) :
    IsIso (openLocalInclusion n U h0 k) :=
  pointLocalInclusion_isIso (TopCat.of (EuclideanSpace ℝ (Fin n))) U hU ⟨0, h0⟩ k

/-- The positive ambient coordinate, pulled back by point excision. -/
def openLocalCoordinate (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U) :
    relativeHomology (TopCat.of U) ({⟨0, h0⟩} : Set U)ᶜ n ≃ₗ[ℚ] ℚ := by
  have := openLocalInclusion_isIso n U hU h0 n
  exact (asIso (openLocalInclusion n U h0 n)).toLinearEquiv.trans (rationalLocalCoordinate n)

lemma openLocalHomology_isZero (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (k : ℕ) (hk : k ≠ n) :
    IsZero (relativeHomology (TopCat.of U) ({⟨0, h0⟩} : Set U)ᶜ k) := by
  have := openLocalInclusion_isIso n U hU h0 k
  have hz : IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ k) := rationalLocalHomology_isZero n k hk
  exact hz.of_iso (asIso (openLocalInclusion n U h0 k))

set_option backward.isDefEq.respectTransparency false in
/-- The two-term relative diagonal formula is natural under a map of pairs. -/
lemma relativeDiagonal_twoTerm_naturality {X Y : TopCat.{u}}
    (A : Set X) (hA : IsOpen A) (B : Set Y) (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (p q : ℕ) (a : relativeHomology X A (p + q))
    (b : relativeHomology X A p) (c : homology X q) (x : X)
    (ha : (relativeMap A (productSubspace X X A) (diagonalMap X) (fun _ hx ↦ hx)
        (p + q)).hom a =
      cross X X A (p + q) 0 a (pointClass X x) + cross X X A p q b c) :
    (relativeMap B (productSubspace Y Y B) (diagonalMap Y) (fun _ hx ↦ hx)
        (p + q)).hom ((relativeMap A B f hf (p + q)).hom a) =
      cross Y Y B (p + q) 0 ((relativeMap A B f hf (p + q)).hom a) (pointClass Y (f x)) +
        cross Y Y B p q ((relativeMap A B f hf p).hom b) ((homologyMap f q).hom c) := by
  have hc : relativeMap A B f hf (p + q) ≫
      relativeMap B (productSubspace Y Y B) (diagonalMap Y) (fun _ hx ↦ hx) (p + q) =
    relativeMap A (productSubspace X X A) (diagonalMap X) (fun _ hx ↦ hx) (p + q) ≫
      relativeMap (productSubspace X X A) (productSubspace Y Y B)
        (productMap f f) (fun _ hx ↦ hf hx) (p + q) := by
    rw [← relativeMap_comp A B (productSubspace Y Y B) f hf (diagonalMap Y) (fun _ hx ↦ hx),
      ← relativeMap_comp A (productSubspace X X A) (productSubspace Y Y B)
        (diagonalMap X) (fun _ hx ↦ hx) (productMap f f) (fun _ hx ↦ hf hx)]
    rfl
  have he := congrArg (fun m ↦ m.hom a) hc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
  rw [he, ha, map_add]
  have h₁ := cross_naturality (X := X) (Z := X) (X' := Y) (Z' := Y)
    A hA B f hf f (p + q) 0 a (pointClass X x)
  rw [pointClass_naturality] at h₁
  have h₂ := cross_naturality (X := X) (Z := X) (X' := Y) (Z' := Y)
    A hA B f hf f p q b c
  exact congrArg₂ (· + ·) h₁ h₂

set_option backward.isDefEq.respectTransparency false in
/-- With the local collar difference coefficient, the two graded signs cancel
and the support coordinate is exactly the surviving ordinary class. -/
lemma supportCoordinate_of_two_term_diagonal (p q : ℕ) (hq : 0 < q)
    (U K : Set (EuclideanSpace ℝ (Fin (p + q)))) (hK : IsClosed K)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) (p + q))
    (b : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (c : homology (TopCat.of U) q) (u : U)
    (ha : (relativeMap (X := TopCat.of U) (Y := TopCat.of (U × U))
      (supportComplement U K)
      (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
      (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) (p + q)).hom a =
      cross (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q) 0 a
        (pointClass (TopCat.of U) u) +
      cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q b c)
    (z : homology (TopCat.of K) q)
    (hd : (relativeMap (X := TopCat.of (U × K))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + q))))
      (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
      ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom
      (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q b z) =
        (-1 : ℚ) ^ q • rationalPositiveLocalClass (p + q)) :
    localProductCoordinate (p + q) (TopCat.of U) q (supportValue U K (p + q) q a z) = c := by
  rw [supportValue_of_two_term_diagonal p q hq U K hK a b c u ha z,
    map_smul, localProductCoordinate_cross, hd, map_smul, rationalLocalCoordinate_positive,
    smul_eq_mul, mul_one, smul_smul, ← pow_add]
  have he : Even (q * q + q) := by simpa [Nat.mul_add] using Nat.even_mul_succ_self q
  rw [he.neg_one_pow, one_smul]

lemma pointDifferenceMap_support_mapsTo {W : Type} [NormedAddCommGroup W]
    (U K : Set W) (p : W) (hp : p ∈ K) :
    Set.MapsTo (pointDifferenceMap U p) (supportComplement U K) ({0} : Set W)ᶜ := by
  intro x hx hz
  exact hx ((sub_eq_zero.mp hz) ▸ hp)

set_option backward.isDefEq.respectTransparency false in
/-- Translating a compact-support orientation to any point in its support gives
the positive point-local generator. This is localization followed by translation. -/
lemma rationalSupportOrientation_centered (n : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ K) :
    (relativeMap (X := TopCat.of U) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (supportComplement U K) ({0} : Set _)ᶜ (TopCat.ofHom (pointDifferenceMap U p))
      (pointDifferenceMap_support_mapsTo U K p hp) n).hom
      (rationalSupportOrientation n U K hU hK hKU) = rationalPositiveLocalClass n := by
  have hsub : {p} ⊆ K := Set.singleton_subset_iff.mpr hp
  have hc : relativeMap (X := TopCat.of U) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (supportComplement U K) ({0} : Set _)ᶜ (TopCat.ofHom (pointDifferenceMap U p))
      (pointDifferenceMap_support_mapsTo U K p hp) n =
    relativeMap (X := TopCat.of U) (Y := TopCat.of U) (supportComplement U K) (supportComplement U {p}) (𝟙 (TopCat.of U))
      (fun _ hx hk ↦ hx (hsub hk)) n ≫
    relativeMap (X := TopCat.of U) (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) (supportComplement U {p}) ({0} : Set _)ᶜ
      (TopCat.ofHom (pointDifferenceMap U p)) (pointDifferenceMap_mapsTo U p) n :=
    relativeMap_comp (X := TopCat.of U) (Y := TopCat.of U)
      (Z := TopCat.of (EuclideanSpace ℝ (Fin n))) (supportComplement U K) (supportComplement U {p}) ({0} : Set _)ᶜ
      (𝟙 (TopCat.of U)) (fun _ hx hk ↦ hx (hsub hk))
      (TopCat.ofHom (pointDifferenceMap U p)) (pointDifferenceMap_mapsTo U p) n
  rw [hc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [rationalSupportOrientation_support n U {p} K hU isCompact_singleton hK hsub hKU]
  exact rationalSupportOrientation_singleton n U hU p (hKU hp)

/-- A product collar identifies its central section with the support. -/
lemma collar_support_iff {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U K : Set E) (b : N)
    (e : (N × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ z : S, (e (b, z)).val = (s z).val) (x : N × S) :
    (e x).val ∈ K ↔ x.1 = b := by
  constructor
  · intro hx
    let k : K := ⟨(e x).val, hx⟩
    have he : e x = e (b, s.symm k) := by
      apply Subtype.ext
      rw [hcenter, s.apply_symm_apply]
    have hpair := e.injective he
    exact congrArg Prod.fst hpair
  · intro hx
    rw [show x = (b, x.2) from Prod.ext hx rfl, hcenter]
    exact (s x.2).property

/-- The support is automatically inside its product collar domain. -/
lemma collar_support_subset {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U K : Set E) (b : N)
    (e : (N × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ z : S, (e (b, z)).val = (s z).val) : K ⊆ U := by
  intro x hx
  obtain ⟨z, hz⟩ := s.surjective ⟨x, hx⟩
  have he : (e (b, z)).val = x := (hcenter z).trans (congrArg Subtype.val hz)
  exact he ▸ (e (b, z)).property

/-- Every element of a one-dimensional rational space is a multiple of any
nonzero element; the coordinate ratio gives the coefficient. -/
lemma exists_smul_of_rational_coordinate {M : Type u} [AddCommGroup M] [Module ℚ M]
    (e : M ≃ₗ[ℚ] ℚ) (b : M) (hb : b ≠ 0) (z : M) : ∃ r : ℚ, z = r • b := by
  refine ⟨e z / e b, ?_⟩
  apply e.injective
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (by simpa using hb)]

/-- A stereographic inverse supplies a Euclidean chart in every sphere dimension. -/
lemma sphere_chart_exists (q : ℕ) :
    ∃ φ : C(EuclideanSpace ℝ (Fin q),
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1),
      _root_.Topology.IsOpenEmbedding φ := by
  let E := EuclideanSpace ℝ (Fin (q + 1))
  have : Fact (Module.finrank ℝ E = q + 1) := ⟨finrank_euclideanSpace_fin⟩
  have : Nonempty (Metric.sphere (0 : E) 1) := NormedSpace.sphere_nonempty_rclike ℝ (by norm_num)
  let v : Metric.sphere (0 : E) 1 := Classical.ofNonempty
  let e := stereographic' q v
  have he : _root_.Topology.IsOpenEmbedding e.symm := e.symm.isOpenEmbedding (by simp [e])
  exact ⟨⟨e.symm, he.continuous⟩, he⟩

lemma rationalSupportOrientation_ne_zero (n : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ K) :
    rationalSupportOrientation n U K hU hK hKU ≠ 0 := by
  intro hz
  have h := rationalSupportOrientation_centered n U K hU hK hKU p hp
  rw [hz, map_zero] at h
  have he := congrArg (rationalLocalCoordinate n) h
  simp only [map_zero] at he
  exact zero_ne_one (he.trans (rationalLocalCoordinate_positive n))

lemma collarPair_mapsTo {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U K : Set E) (v : N) (e : (N × S) ≃ₜ U)
    (he : ∀ x : N × S, (e x).val ∉ K ↔ x.1 ≠ v) :
    Set.MapsTo (TopCat.ofHom ⟨e, e.continuous⟩)
      (productSubspace (TopCat.of N) (TopCat.of S) ({v} : Set N)ᶜ)
      (supportComplement U K) := by
  intro x hx
  exact (he x).2 hx

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the actual support orientation into a product collar gives a pure
cross product of a normal local class and a central-section class. -/
lemma collarSupportOrientation_cross_exists (m q : ℕ) (N S : TopCat.{0}) (v : N)
    (L : relativeHomology N ({v} : Set N)ᶜ m ≃ₗ[ℚ] ℚ)
    (hz : ∀ k, k ≠ m → Subsingleton (relativeHomology N ({v} : Set N)ᶜ k))
    (U K : Set (EuclideanSpace ℝ (Fin (m + q)))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (e : (N × S) ≃ₜ U)
    (he : ∀ x : N × S, (e x).val ∉ K ↔ x.1 ≠ v) :
    ∃ β : relativeHomology (N) ({v} : Set N)ᶜ m,
      ∃ b : homology S q,
        (relativeMap (X := TopCat.of (N × S)) (Y := TopCat.of U)
          (productSubspace (N) S ({v} : Set N)ᶜ)
          (supportComplement U K) (TopCat.ofHom ⟨e, e.continuous⟩)
          (collarPair_mapsTo U K v e he) (m + q)).hom
          (cross (N) S ({v} : Set N)ᶜ m q β b) =
            rationalSupportOrientation (m + q) U K hU hK hKU := by
  let X := N
  let A : Set X := ({v} : Set N)ᶜ
  let F := relativeMap (X := TopCat.of (N × S)) (Y := TopCat.of U)
    (productSubspace X S A) (supportComplement U K) (TopCat.ofHom ⟨e, e.continuous⟩)
    (collarPair_mapsTo U K v e he) (m + q)
  have : IsIso F := rationalPairHomeomorph_isIso
    (X := TopCat.of (N × S)) (Y := TopCat.of U) e
    (productSubspace X S A) (supportComplement U K) he (m + q)
  let a : kunnethTarget X S A (m + q) := (asIso F).toLinearEquiv.symm
    (rationalSupportOrientation (m + q) U K hU hK hKU)
  obtain ⟨b, hb⟩ := relativeCross_surjective_of_concentrated X S A m q L hz a
  refine ⟨L.symm 1, b, ?_⟩
  change F.hom (cross X S A m q (L.symm 1) b) = _
  rw [hb]
  exact (asIso F).toLinearEquiv.apply_symm_apply _

/-- The ambient map underlying a collar homeomorphism. -/
def collarEmbedding {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U : Set E) (e : (N × S) ≃ₜ U) : C(N × S, E) :=
  ⟨fun x ↦ (e x).val, by fun_prop⟩

lemma collarEmbedding_injective {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U : Set E) (e : (N × S) ≃ₜ U) :
    Function.Injective (collarEmbedding U e) := Subtype.val_injective.comp e.injective

lemma collarNormalFiber_mapsTo {E N S : Type} [TopologicalSpace E] [TopologicalSpace N]
    [TopologicalSpace S] (U K : Set E) (v : N) (z : S)
    (e : (N × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ t : S, (e (v, t)).val = (s t).val) :
    Set.MapsTo (insertPoint (TopCat.of N) (TopCat.of S) z ≫ TopCat.ofHom ⟨e, e.continuous⟩)
      ({v} : Set N)ᶜ (supportComplement U K) := by
  intro x hx hk
  exact hx ((collar_support_iff U K v e s hcenter (x, z)).mp hk)

lemma normalProduct_subset_puncture {N S : Type} [TopologicalSpace N] [TopologicalSpace S]
    (v : N) (z : S) :
    productSubspace (TopCat.of N) (TopCat.of S) ({v} : Set N)ᶜ ⊆ ({(v, z)} : Set (N × S))ᶜ := by
  intro x hx he
  exact hx (congrArg Prod.fst he)

set_option backward.isDefEq.respectTransparency false in
/-- Product naturality identifies the actual difference pairing of a normal
fiber and a support class with the collar's normal-minus-tangent map. -/
lemma difference_normalFiber_cross {E N S : Type} [NormedAddCommGroup E]
    [TopologicalSpace N] [T1Space N] [TopologicalSpace S]
    (U K : Set E) (v : N) (z : S)
    (e : (N × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ t : S, (e (v, t)).val = (s t).val)
    (p q : ℕ) (β : relativeHomology (TopCat.of N) ({v} : Set N)ᶜ p)
    (b : homology (TopCat.of S) q) :
    (relativeMap (X := TopCat.of (U × K)) (Y := TopCat.of E)
      (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K)) ({0} : Set E)ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom
      (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q
        ((relativeMap (X := TopCat.of N) (Y := TopCat.of U) ({v} : Set N)ᶜ
          (supportComplement U K)
          (insertPoint (TopCat.of N) (TopCat.of S) z ≫ TopCat.ofHom ⟨e, e.continuous⟩)
          (collarNormalFiber_mapsTo U K v z e s hcenter) p).hom β)
        ((homologyMap (TopCat.ofHom ⟨s, s.continuous⟩) q).hom b)) =
    (relativeMap (X := TopCat.of (N × S)) (Y := TopCat.of E)
      (productSubspace (TopCat.of N) (TopCat.of S) ({v} : Set N)ᶜ) ({0} : Set E)ᶜ
      (TopCat.ofHom (normalFirstDifference v z (collarEmbedding U e)))
      (fun _x hx ↦ normalFirstDifference_mapsTo v z (collarEmbedding U e)
        (collarEmbedding_injective U e) (normalProduct_subset_puncture v z hx)) (p + q)).hom
      (cross (TopCat.of N) (TopCat.of S) ({v} : Set N)ᶜ p q β b) := by
  let F := insertPoint (TopCat.of N) (TopCat.of S) z ≫ TopCat.ofHom ⟨e, e.continuous⟩
  let G : TopCat.of S ⟶ TopCat.of K := TopCat.ofHom ⟨s, s.continuous⟩
  let A := ({v} : Set N)ᶜ
  let B := supportComplement U K
  have hn := cross_naturality (X := TopCat.of N) (Z := TopCat.of S)
    (X' := TopCat.of U) (Z' := TopCat.of K) A isClosed_singleton.isOpen_compl B F
    (collarNormalFiber_mapsTo U K v z e s hcenter) G p q β b
  rw [← hn]
  have hf : productMap F G ≫ TopCat.ofHom (difference U K) =
      TopCat.ofHom (normalFirstDifference v z (collarEmbedding U e)) := by
    apply TopCat.ext
    intro x
    change (e (x.1, z)).val - (s x.2).val = (e (x.1, z)).val - (e (v, x.2)).val
    rw [hcenter]
  have hc := relativeMap_comp (productSubspace (TopCat.of N) (TopCat.of S) A)
    (productSubspace (TopCat.of U) (TopCat.of K) B) ({0} : Set E)ᶜ
    (productMap F G) (fun x hx ↦ collarNormalFiber_mapsTo U K v z e s hcenter hx)
    (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)
  have hmap : relativeMap (productSubspace (TopCat.of N) (TopCat.of S) A) ({0} : Set E)ᶜ
      (productMap F G ≫ TopCat.ofHom (difference U K))
      (fun x hx ↦ difference_mapsTo U K (collarNormalFiber_mapsTo U K v z e s hcenter hx))
      (p + q) =
    relativeMap (productSubspace (TopCat.of N) (TopCat.of S) A) ({0} : Set E)ᶜ
      (TopCat.ofHom (normalFirstDifference v z (collarEmbedding U e)))
      (fun x hx ↦ normalFirstDifference_mapsTo v z (collarEmbedding U e)
        (collarEmbedding_injective U e) (normalProduct_subset_puncture v z hx)) (p + q) := by
    congr 1
  rw [← hmap, hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The collar's two-term diagonal after mapping into its ambient domain. -/
lemma collarDiagonal_cross (N S Y : TopCat.{u}) [T1Space N] [PathConnectedSpace S]
    (v : N) (z : S) (H : (ContinuousMap.id N).Homotopy (ContinuousMap.const N v))
    (B : Set Y) (F : TopCat.of (N × S) ⟶ Y)
    (hF : Set.MapsTo F (productSubspace N S ({v} : Set N)ᶜ) B)
    (p q : ℕ) (hq : 0 < q)
    (hS : ∀ k : ℕ, 0 < k → k < q → IsZero (homology S k))
    (β : relativeHomology N ({v} : Set N)ᶜ p) (b : homology S q) :
    (relativeMap B (productSubspace Y Y B) (diagonalMap Y) (fun _ hx ↦ hx) (p + q)).hom
      ((relativeMap (productSubspace N S ({v} : Set N)ᶜ) B F hF (p + q)).hom
        (cross N S ({v} : Set N)ᶜ p q β b)) =
    cross Y Y B (p + q) 0
      ((relativeMap (productSubspace N S ({v} : Set N)ᶜ) B F hF (p + q)).hom
        (cross N S ({v} : Set N)ᶜ p q β b)) (pointClass Y (F (v, z))) +
      cross Y Y B p q
        ((relativeMap ({v} : Set N)ᶜ B (insertPoint N S z ≫ F) (fun _ hx ↦ hF hx) p).hom β)
        ((homologyMap (insertPointLeft N S v ≫ F) q).hom b) := by
  let A : Set N := ({v} : Set N)ᶜ
  have hA : IsOpen A := isClosed_singleton.isOpen_compl
  have hd := relativeSphereCollar_diagonal N S A hA v z H p q hq hS β b
  have hn := relativeDiagonal_twoTerm_naturality (X := TopCat.of (N × S)) (Y := Y) (productSubspace N S A)
    (hA.preimage continuous_fst) B F hF p q (cross N S A p q β b)
    ((relativeMap A (productSubspace N S A) (insertPoint N S z) (fun _ hx ↦ hx) p).hom β)
    ((homologyMap (insertPointLeft N S v) q).hom b) (v, z) hd
  rw [relativeMap_comp ({v} : Set N)ᶜ (productSubspace N S ({v} : Set N)ᶜ) B
    (insertPoint N S z) (fun _ hx ↦ hx) F hF p]
  simpa only [homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hn

set_option backward.isDefEq.respectTransparency false in
/-- A collar chart centered at its central section takes the pulled-back support
orientation to the prescribed positive Euclidean local class. -/
lemma collar_centered_orientation (n : ℕ) (N S : TopCat.{0})
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (v : N) (z : S) (e : (N × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ t : S, (e (v, t)).val = (s t).val)
    (a : relativeHomology (TopCat.of (N × S))
      (productSubspace N S ({v} : Set N)ᶜ) n)
    (ha : (relativeMap (X := TopCat.of (N × S)) (Y := TopCat.of U)
      (productSubspace N S ({v} : Set N)ᶜ) (supportComplement U K)
      (TopCat.ofHom ⟨e, e.continuous⟩)
      (collarPair_mapsTo U K v e (fun x ↦ not_congr (collar_support_iff U K v e s hcenter x))) n).hom a =
        rationalSupportOrientation n U K hU hK hKU) :
    (relativeMap (X := TopCat.of (N × S)) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (productSubspace N S ({v} : Set N)ᶜ) ({0} : Set _)ᶜ
      (TopCat.ofHom (centeredMap (collarEmbedding U e) (v, z)))
      (fun _x hx ↦ centeredMap_mapsTo (collarEmbedding U e) (collarEmbedding_injective U e)
        (v, z) (normalProduct_subset_puncture v z hx)) n).hom a = rationalPositiveLocalClass n := by
  let F : TopCat.of (N × S) ⟶ TopCat.of U := TopCat.ofHom ⟨e, e.continuous⟩
  let A := productSubspace N S ({v} : Set N)ᶜ
  let B := supportComplement U K
  have hF : Set.MapsTo F A B := collarPair_mapsTo U K v e
    (fun x ↦ not_congr (collar_support_iff U K v e s hcenter x))
  have hf : F ≫ TopCat.ofHom (pointDifferenceMap U (s z).val) =
      TopCat.ofHom (centeredMap (collarEmbedding U e) (v, z)) := by
    apply TopCat.ext
    intro x
    change (e x).val - (s z).val = (e x).val - (e (v, z)).val
    rw [hcenter]
  have hc := relativeMap_comp (X := TopCat.of (N × S)) (Y := TopCat.of U)
    (Z := TopCat.of (EuclideanSpace ℝ (Fin n))) A B ({0} : Set _)ᶜ F hF
    (TopCat.ofHom (pointDifferenceMap U (s z).val))
    (pointDifferenceMap_support_mapsTo U K (s z).val (s z).property) n
  have hmap : relativeMap A ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
      (F ≫ TopCat.ofHom (pointDifferenceMap U (s z).val))
      (fun x hx ↦ pointDifferenceMap_support_mapsTo U K (s z).val (s z).property (hF hx)) n =
    relativeMap A ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
      (TopCat.ofHom (centeredMap (collarEmbedding U e) (v, z)))
      (fun x hx ↦ centeredMap_mapsTo (collarEmbedding U e) (collarEmbedding_injective U e)
        (v, z) (normalProduct_subset_puncture v z hx)) n := by
    congr 1
  rw [← hmap, hc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ha]
  exact rationalSupportOrientation_centered n U K hU hK hKU (s z).val (s z).property

lemma homologyMap_homeomorph_isIso {X Y : TopCat.{u}} (e : X ≃ₜ Y) (q : ℕ) :
    IsIso (homologyMap (TopCat.ofHom ⟨e, e.continuous⟩) q) := by
  change IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) q).obj
    coefficients).map (TopCat.isoOfHomeo e).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Dold's support operator is inclusion on a product collar with a rational
homology sphere as central section. The proof uses its actual support orientation. -/
lemma supportOperator_collar (m q : ℕ) (hq : 0 < q) (S : TopCat.{0})
    [T1Space S] [PathConnectedSpace S]
    (hS : ∀ k : ℕ, 0 < k → k < q → IsZero (homology S k))
    (eH : homology S q ≃ₗ[ℚ] ℚ)
    (φ : C(EuclideanSpace ℝ (Fin q), S)) (hφ : _root_.Topology.IsOpenEmbedding φ)
    (V : Set (EuclideanSpace ℝ (Fin m))) (hV : IsOpen V) (hconv : Convex ℝ V)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V)
    (U K : Set (EuclideanSpace ℝ (Fin (m + q)))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (e : (V × S) ≃ₜ U) (s : S ≃ₜ K)
    (hcenter : ∀ t : S, (e (⟨0, h0V⟩, t)).val = (s t).val) :
    supportOperator (m + q) U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  let N := TopCat.of V
  let v : N := ⟨0, h0V⟩
  let z : S := φ 0
  let A : Set N := ({v} : Set N)ᶜ
  let B := supportComplement U K
  let F : TopCat.of (N × S) ⟶ TopCat.of U := TopCat.ofHom ⟨e, e.continuous⟩
  let G : S ⟶ TopCat.of K := TopCat.ofHom ⟨s, s.continuous⟩
  let I : TopCat.of K ⟶ TopCat.of U := TopCat.ofHom (ContinuousMap.inclusion hKU)
  have he : ∀ x : N × S, (e x).val ∉ K ↔ x.1 ≠ v :=
    fun x ↦ not_congr (collar_support_iff U K v e s hcenter x)
  have hF : Set.MapsTo F (productSubspace N S A) B := collarPair_mapsTo U K v e he
  have hz : ∀ k, k ≠ m → Subsingleton (relativeHomology N A k) := by
    intro k hk
    exact ModuleCat.subsingleton_of_isZero (openLocalHomology_isZero m V hV h0V k hk)
  let L : relativeHomology N A m ≃ₗ[ℚ] ℚ := openLocalCoordinate m V hV h0V
  obtain ⟨β, b, hab⟩ := collarSupportOrientation_cross_exists m q N S v L hz U K hU hK hKU e he
  have hb : b ≠ 0 := by
    intro hb0
    have ha0 : rationalSupportOrientation (m + q) U K hU hK hKU = 0 := by
      rw [hb0] at hab
      simpa only [cross, TensorProduct.tmul_zero, map_zero] using hab.symm
    exact rationalSupportOrientation_ne_zero (m + q) U K hU hK hKU (s z).val
      (s z).property ha0
  let nf := insertPoint N S z ≫ F
  have hnf : Set.MapsTo nf A B := collarNormalFiber_mapsTo U K v z e s hcenter
  let βU := (relativeMap A B nf hnf m).hom β
  let cU := (homologyMap (insertPointLeft N S v ≫ F) q).hom b
  let zK := (homologyMap G q).hom b
  have hdiag := collarDiagonal_cross N S (TopCat.of U) v z
    (convexContraction V hconv v) B F hF m q hq hS β b
  rw [hab] at hdiag
  have hpair := difference_normalFiber_cross U K v z e s hcenter m q β b
  let h := collarEmbedding U e
  let T : Set (EuclideanSpace ℝ (Fin q)) := Set.univ
  let φ' : C(T, S) := φ.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hφ' : _root_.Topology.IsOpenEmbedding φ' :=
    hφ.comp isOpen_univ.isOpenEmbedding_subtypeVal
  have hlocal := normalFirstDifference_support_action q m (m + q) (Nat.add_comm m q)
    T V isOpen_univ hV convex_univ (Set.mem_univ 0) h0V (fun _ _ ↦ Set.mem_univ _)
    φ' hφ' h (collarEmbedding_injective U e) (productSubspace N S A)
    (normalProduct_subset_puncture v z) (cross N S A m q β b)
  have hpositive := collar_centered_orientation (m + q) N S U K hU hK hKU v z e s hcenter
    (cross N S A m q β b) hab
  have hlocal' := hlocal.trans (congrArg ((-1 : ℚ) ^ q • ·) hpositive)
  have hd : (relativeMap (productSubspace (TopCat.of U) (TopCat.of K) B)
      ({0} : Set (EuclideanSpace ℝ (Fin (m + q))))ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (m + q)).hom
      (cross (TopCat.of U) (TopCat.of K) B m q βU zK) =
      (-1 : ℚ) ^ q • rationalPositiveLocalClass (m + q) := hpair.trans hlocal'
  have hcore := supportCoordinate_of_two_term_diagonal m q hq U K hK.isClosed
    (rationalSupportOrientation (m + q) U K hU hK hKU) βU cU (e (v, z)) hdiag zK hd
  have hsec : insertPointLeft N S v ≫ F = G ≫ I := by
    apply TopCat.ext
    intro t
    exact Subtype.ext (hcenter t)
  have hcoreb : supportOperator (m + q) U K hU hK hKU q zK = (homologyMap I q).hom zK := by
    change localProductCoordinate (m + q) (TopCat.of U) q
      (supportValue U K (m + q) q (rationalSupportOrientation (m + q) U K hU hK hKU) zK) = _
    rw [hcore]
    change (homologyMap (insertPointLeft N S v ≫ F) q).hom b = _
    rw [hsec, homologyMap_comp]
    rfl
  have : IsIso (homologyMap G q) :=
    homologyMap_homeomorph_isIso (X := S) (Y := TopCat.of K) s q
  apply LinearMap.ext
  intro w
  obtain ⟨w', rfl⟩ := (ModuleCat.epi_iff_surjective (homologyMap G q)).mp inferInstance w
  obtain ⟨r, rfl⟩ := exists_smul_of_rational_coordinate eH b hb w'
  simp only [map_smul]
  change r • supportOperator (m + q) U K hU hK hKU q zK = r • (homologyMap I q).hom zK
  exact congrArg (r • ·) hcoreb

lemma metricSphere_pathConnected (q : ℕ) (hq : 0 < q) :
    PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1) := by
  have hs : Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 = {x | ‖x‖ = 1} := by
    ext x
    simp
  rw [hs]
  exact unitSphere_pathConnected q hq

lemma rationalMetricSphereHomology_isZero (q k : ℕ) (hk : 0 < k) (hkq : k ≠ q) :
    IsZero (homology (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1)) k) := by
  have hs : Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 = {x | ‖x‖ = 1} := by
    ext x
    simp
  rw [hs]
  exact rationalSphereHomology_isZero q k hk hkq

/-- Top rational homology of the metric unit sphere, in ordinary homology. -/
def rationalMetricSphereTopCoordinate (q : ℕ) :
    homology (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1 + 1))) 1)) (q + 1)
      ≃ₗ[ℚ] ℚ := by
  have hs : Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1 + 1))) 1 = {x | ‖x‖ = 1} := by
    ext x
    simp
  rw [hs]
  exact (rationalSphereTopIso q).toLinearEquiv.trans (ULift.moduleEquiv : ULift ℚ ≃ₗ[ℚ] ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- The sphere-collar case of Dold's support-operator identity in every positive degree. -/
lemma supportOperator_sphereCollar (m q : ℕ) (hq : 0 < q)
    (V : Set (EuclideanSpace ℝ (Fin m))) (hV : IsOpen V) (hconv : Convex ℝ V)
    (h0V : (0 : EuclideanSpace ℝ (Fin m)) ∈ V)
    (U K : Set (EuclideanSpace ℝ (Fin (m + q)))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U)
    (e : (V × Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1) ≃ₜ U)
    (s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 ≃ₜ K)
    (hcenter : ∀ t, (e (⟨0, h0V⟩, t)).val = (s t).val) :
    supportOperator (m + q) U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have := metricSphere_pathConnected (q + 1) (by omega)
  obtain ⟨φ, hφ⟩ := sphere_chart_exists (q + 1)
  exact supportOperator_collar m (q + 1) (by omega)
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1 + 1))) 1))
    (fun k hk hkq ↦ rationalMetricSphereHomology_isZero (q + 1) k hk (by omega))
    (rationalMetricSphereTopCoordinate q) φ hφ V hV hconv h0V U K hU hK hKU e s hcenter


/-- Removing the harmless universe lift on the rational coefficient module. -/
def ordinaryRationalHomologyIso (X : TopCat.{0}) (q : ℕ) :
    homology X q ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
        (ModuleCat.of ℚ ℚ)).obj X :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).mapIso
    (ULift.moduleEquiv : ULift ℚ ≃ₗ[ℚ] ℚ).toModuleIso).app X

lemma ordinaryRationalHomologyIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) :
    homologyMap f q ≫ (ordinaryRationalHomologyIso Y q).hom =
      (ordinaryRationalHomologyIso X q).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
          (ModuleCat.of ℚ ℚ)).map f :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).mapIso
    (ULift.moduleEquiv : ULift ℚ ≃ₗ[ℚ] ℚ).toModuleIso).hom.naturality f)

/-- A homotopy of actual maps gives equality on the native rational groups. -/
lemma homologyMap_homotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) : homologyMap f q = homologyMap g q :=
  SSet.Homotopy.congr_homologyMap H.toSSet coefficients q

/-- A deformation retraction makes the literal inclusion an isomorphism on homology. -/
lemma homologyMap_deformationInclusion_isIso {X : Type u} [TopologicalSpace X]
    {A U : Set X} (hAU : A ⊆ U) (r : C(U, A))
    (hr : ∀ a : A, r ⟨a.val, hAU a.property⟩ = a)
    (H : (ContinuousMap.id U).HomotopyRel
      ((ContinuousMap.inclusion hAU).comp r) {x : U | x.val ∈ A}) (q : ℕ) :
    IsIso (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hAU)) q) := by
  let i : TopCat.of A ⟶ TopCat.of U := TopCat.ofHom (ContinuousMap.inclusion hAU)
  let R : TopCat.of U ⟶ TopCat.of A := TopCat.ofHom r
  have hiR : i ≫ R = 𝟙 _ := by
    apply TopCat.ext
    exact hr
  have hRi : homologyMap (R ≫ i) q = 𝟙 _ := by
    have h := homologyMap_homotopy (X := TopCat.of U) (Y := TopCat.of U)
      (f := 𝟙 _) (g := R ≫ i) H.toHomotopy q
    simpa only [homologyMap, TopCat.toSSet.map_id, SSet.homologyMap_id] using h.symm
  refine ⟨⟨homologyMap R q, ?_, ?_⟩⟩
  · rw [← homologyMap_comp, hiR]
    simp only [homologyMap, TopCat.toSSet.map_id, SSet.homologyMap_id]
  · rw [← homologyMap_comp, hRi]

/-- Conjugating a linear map by isomorphisms preserves injectivity. -/
lemma injective_of_iso_square {A B C D : ModuleCat.{u} ℚ}
    (e : A ≅ B) (d : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ d.hom = e.hom ≫ g) (hg : Function.Injective g) :
    Function.Injective f := by
  intro x y hxy
  apply e.toLinearEquiv.injective
  apply hg
  have hx := congrArg (fun t : A ⟶ D ↦ t x) h
  have hy := congrArg (fun t : A ⟶ D ↦ t y) h
  exact hx.symm.trans ((congrArg d.hom hxy).trans hy)

/-- Conjugating a linear map by isomorphisms preserves surjectivity. -/
lemma surjective_of_iso_square {A B C D : ModuleCat.{u} ℚ}
    (e : A ≅ B) (d : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ d.hom = e.hom ≫ g) (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro z
  obtain ⟨w, hw⟩ := hg (d.hom z)
  refine ⟨e.inv w, d.toLinearEquiv.injective ?_⟩
  change d.hom (f (e.inv w)) = d.hom z
  have hh := congrArg (fun t : A ⟶ D ↦ t (e.inv w)) h
  change d.hom (f (e.inv w)) = g (e.hom (e.inv w)) at hh
  simpa only [ModuleCat.inv_hom_apply] using hh.trans (by simpa using hw)


/-- The two ambient coordinate conventions and the coefficient lift give naturally
isomorphic homology groups on every literal cubical carrier. -/
def cubicalHomologyIso (N : ℕ) (A : Set (Fin N → ℝ)) (q : ℕ) :
    homology (TopCat.of ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A)) q ≅
      Cubical.rationalSingularHomology A q :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj coefficients).mapIso
    (TopCat.isoOfHomeo ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm.image A).symm) ≪≫
      ordinaryRationalHomologyIso (TopCat.of A) q

lemma cubicalHomologyIso_naturality (N : ℕ) {A B : Set (Fin N → ℝ)}
    (hAB : A ⊆ B) (q : ℕ) :
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion
      (Set.image_mono hAB : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A ⊆
        (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' B))) q ≫
      (cubicalHomologyIso N B q).hom =
    (cubicalHomologyIso N A q).hom ≫ Cubical.rationalSingularHomologyInclusion hAB q := by
  let e := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm
  let a : TopCat.of (e '' A) ⟶ TopCat.of A := (TopCat.isoOfHomeo (e.image A).symm).hom
  let b : TopCat.of (e '' B) ⟶ TopCat.of B := (TopCat.isoOfHomeo (e.image B).symm).hom
  let i : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom (ContinuousMap.inclusion hAB)
  let j : TopCat.of (e '' A) ⟶ TopCat.of (e '' B) :=
    TopCat.ofHom (ContinuousMap.inclusion (Set.image_mono hAB))
  have hsquare : j ≫ b = a ≫ i := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  change homologyMap j q ≫ (homologyMap b q ≫ (ordinaryRationalHomologyIso _ q).hom) =
    (homologyMap a q ≫ (ordinaryRationalHomologyIso _ q).hom) ≫ _
  rw [← Category.assoc, ← homologyMap_comp, hsquare, homologyMap_comp, Category.assoc,
    ordinaryRationalHomologyIso_naturality, Category.assoc]

lemma cubicalHomology_injective (N : ℕ) {A B : Set (Fin N → ℝ)}
    (hAB : A ⊆ B) (q : ℕ)
    (h : Function.Injective (Cubical.rationalSingularHomologyInclusion hAB q)) :
    Function.Injective (homologyMap (TopCat.ofHom (ContinuousMap.inclusion
      (Set.image_mono hAB : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A ⊆
        (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' B))) q).hom :=
  injective_of_iso_square (cubicalHomologyIso N A q) (cubicalHomologyIso N B q) _ _
    (cubicalHomologyIso_naturality N hAB q) h

lemma cubicalHomology_surjective (N : ℕ) {A B : Set (Fin N → ℝ)}
    (hAB : A ⊆ B) (q : ℕ)
    (h : Function.Surjective (Cubical.rationalSingularHomologyInclusion hAB q)) :
    Function.Surjective (homologyMap (TopCat.ofHom (ContinuousMap.inclusion
      (Set.image_mono hAB : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A ⊆
        (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' B))) q).hom :=
  surjective_of_iso_square (cubicalHomologyIso N A q) (cubicalHomologyIso N B q) _ _
    (cubicalHomologyIso_naturality N hAB q) h

/-- Spanning by inclusion images is invariant under natural linear identifications. -/
lemma span_ranges_of_equiv_square {ι : Type} {A B : Type u}
    [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    {X Y : ι → Type u} [∀ i, AddCommGroup (X i)] [∀ i, Module ℚ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ (Y i)]
    (e : A ≃ₗ[ℚ] B) (d : ∀ i, X i ≃ₗ[ℚ] Y i)
    (f : ∀ i, X i →ₗ[ℚ] A) (g : ∀ i, Y i →ₗ[ℚ] B)
    (h : ∀ i x, e (f i x) = g i (d i x))
    (hs : Submodule.span ℚ (⋃ i, Set.range (g i)) = ⊤) :
    Submodule.span ℚ (⋃ i, Set.range (f i)) = ⊤ := by
  apply top_unique
  intro z _
  have hz : e z ∈ Submodule.span ℚ (⋃ i, Set.range (g i)) := by rw [hs]; trivial
  suffices ∀ w ∈ Submodule.span ℚ (⋃ i, Set.range (g i)),
      e.symm w ∈ Submodule.span ℚ (⋃ i, Set.range (f i)) by
    simpa using this (e z) hz
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hw
    have he : e.symm (g i x) = f i ((d i).symm x) := by
      apply e.injective
      simpa using (h i ((d i).symm x)).symm
    rw [he]
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, _, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using SMulMemClass.smul_mem r hx


/-- The central section of a product collar is a homeomorphism onto its actual support. -/
def collarCoreHomeomorph {E S N : Type} [TopologicalSpace E] [TopologicalSpace S]
    [TopologicalSpace N] (U K : Set E) (hKU : K ⊆ U) (v : N) (e : U ≃ₜ S × N)
    (he : e '' {x : U | x.val ∈ K} = Set.univ ×ˢ {v}) : S ≃ₜ K where
  toFun t := ⟨(e.symm (t, v)).val, by
    have h : (t, v) ∈ e '' {x : U | x.val ∈ K} := by rw [he]; exact ⟨Set.mem_univ _, rfl⟩
    obtain ⟨x, hx, heq⟩ := h
    change x.val ∈ K at hx
    simpa only [← heq, e.symm_apply_apply] using hx⟩
  invFun x := (e ⟨x.val, hKU x.property⟩).1
  left_inv t := by simp
  right_inv x := by
    have h : e ⟨x.val, hKU x.property⟩ ∈ Set.univ ×ˢ {v} := by
      rw [← he]
      exact ⟨⟨x.val, hKU x.property⟩, x.property, rfl⟩
    apply Subtype.ext
    have hpair : ((e ⟨x.val, hKU x.property⟩).1, v) = e ⟨x.val, hKU x.property⟩ :=
      Prod.ext rfl h.2.symm
    simp only [hpair, e.symm_apply_apply]
  continuous_toFun := ((continuous_subtype_val.comp e.symm.continuous).comp
    (continuous_id.prodMk continuous_const)).subtype_mk _
  continuous_invFun := (e.continuous.comp
    (continuous_subtype_val.subtype_mk fun x : K ↦ hKU x.property)).fst

/-- A product collar stated with its central-section set has the support identity. -/
lemma supportOperator_of_sphereProductCollar (m q : ℕ) (hq : 0 < q)
    (U K : Set (EuclideanSpace ℝ (Fin (m + q)))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U)
    (e : U ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1))
    (he : e '' {x : U | x.val ∈ K} = Set.univ ×ˢ {⟨0, Metric.mem_ball_self zero_lt_one⟩}) :
    supportOperator (m + q) U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1
  let V := Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1
  let v : V := ⟨0, Metric.mem_ball_self zero_lt_one⟩
  let s := collarCoreHomeomorph U K hKU v e he
  exact supportOperator_sphereCollar m q hq V Metric.isOpen_ball (convex_ball _ _)
    v.property U K hU hK hKU ((Homeomorph.prodComm V S).trans e.symm) s (fun _ ↦ rfl)


lemma transportedCollar_core {E F T : Type} [TopologicalSpace E]
    [TopologicalSpace F] [TopologicalSpace T] (a : E ≃ₜ F) (U K : Set E) (e : U ≃ₜ T) :
    ((a.image U).symm.trans e) '' {x : a '' U | x.val ∈ a '' K} =
      e '' {x : U | x.val ∈ K} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(a.image U).symm x, ?_, rfl⟩
    change a.symm x.val ∈ K
    rw [a.image_eq_preimage_symm K] at hx
    exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨a.image U x, Set.mem_image_of_mem a hx, ?_⟩
    simp

/-- Positive-degree cubical boundary supports satisfy Dold's identity in every
open neighborhood. The collar is shrunk inside that neighborhood before use. -/
lemma supportOperator_cellBoundary (N q : ℕ) (hq : 0 < q) (hqN : q < N)
    (c : Cubical.ClosedCoordinateCell N) (hd : c.dimension = q + 1)
    (O : Set (EuclideanSpace ℝ (Fin N))) (hO : IsOpen O)
    (hKO : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm ''
      {x | x ∈ c.carrier ∧ ∃ i, c.lower i < c.upper i ∧
        (x i = c.lower i ∨ x i = c.upper i)} ⊆ O) :
    ∀ hK : IsCompact ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm ''
      {x | x ∈ c.carrier ∧ ∃ i, c.lower i < c.upper i ∧
        (x i = c.lower i ∨ x i = c.upper i)}),
    supportOperator N O _ hO hK hKO q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKO)) q).hom := by
  obtain ⟨m, hNm⟩ : ∃ m, N = m + q := ⟨N - q, (Nat.sub_add_cancel hqN.le).symm⟩
  subst N
  intro hK
  let a := (PiLp.homeomorph 2 (fun _ : Fin (m + q) ↦ ℝ)).symm
  let K : Set (Fin (m + q) → ℝ) := {x | x ∈ c.carrier ∧ ∃ i,
    c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)}
  have hKaO : K ⊆ a ⁻¹' O := fun x hx ↦ hKO (Set.mem_image_of_mem a hx)
  obtain ⟨V, hV, hVO, hKV, he⟩ :=
    Cubical.cubical_cell_boundary_product_collar (by omega) hqN c hd
      (a ⁻¹' O) (hO.preimage a.continuous) hKaO
  rw [Nat.add_sub_cancel_right] at he
  obtain ⟨e, he⟩ := he
  let U := a '' V
  have hU : IsOpen U := a.isOpenMap V hV
  have hUO : U ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hVO hx
  have hKU : a '' K ⊆ U := Set.image_mono hKV
  have hcore := supportOperator_of_sphereProductCollar m q hq U (a '' K) hU hK hKU
    ((a.image V).symm.trans e) ((transportedCollar_core a V K e).trans he)
  exact supportOperator_identity_enlarge_domain (m + q) U O (a '' K)
    hU hO hK hKU hUO q hcore


lemma cubicalHomology_span (N : ℕ) {ι : Type} (A : ι → Set (Fin N → ℝ))
    (B : Set (Fin N → ℝ)) (hAB : ∀ i, A i ⊆ B) (q : ℕ)
    (hs : Submodule.span ℚ (⋃ i, Set.range (Cubical.rationalSingularHomologyInclusion (hAB i) q)) = ⊤) :
    Submodule.span ℚ (⋃ i, Set.range (homologyMap (TopCat.ofHom (ContinuousMap.inclusion
      (Set.image_mono (hAB i) : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A i ⊆
        (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' B))) q).hom) = ⊤ := by
  apply span_ranges_of_equiv_square (cubicalHomologyIso N B q).toLinearEquiv
    (fun i ↦ (cubicalHomologyIso N (A i) q).toLinearEquiv) _
    (fun i ↦ (Cubical.rationalSingularHomologyInclusion (hAB i) q).hom) _ hs
  intro i x
  exact congrArg (fun t : homology (TopCat.of
    ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A i)) q ⟶
      Cubical.rationalSingularHomology B q ↦ t.hom x)
    (cubicalHomologyIso_naturality N (hAB i) q)

/-- The full cubical q-skeleton satisfies the degree-q support identity. Its
positive-degree generators are the included boundaries of (q+1)-cells. -/
lemma supportOperator_cubicalSkeleton (N : ℕ) (hN : 1 ≤ N)
    (C : Cubical.FiniteRectilinearSubdivision N) (q : ℕ) (hq : q ≤ N)
    (O : Set (EuclideanSpace ℝ (Fin N))) (hO : IsOpen O)
    (hKO : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' C.skeleton q ⊆ O)
    (hK : IsCompact ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' C.skeleton q)) :
    supportOperator N O _ hO hK hKO q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKO)) q).hom := by
  by_cases hq0 : q = 0
  · subst q
    exact supportOperator_zero N O _ hO hK hKO
  by_cases hqN : q = N
  · subst q
    have := Cubical.top_skeleton_homology_subsingleton hN C
    have : Subsingleton (homology (TopCat.of
        ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' C.skeleton N)) N) :=
      (cubicalHomologyIso N (C.skeleton N) N).toLinearEquiv.injective.subsingleton
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  let a := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm
  let I := {c : Cubical.ClosedCoordinateCell N // c ∈ C.cells ∧ c.dimension = q + 1}
  let boundary (c : Cubical.ClosedCoordinateCell N) : Set (Fin N → ℝ) :=
    {x | x ∈ c.carrier ∧ ∃ i, c.lower i < c.upper i ∧
      (x i = c.lower i ∨ x i = c.upper i)}
  let B : I → Set (Fin N → ℝ) := fun c ↦ boundary c.val
  have hBS : ∀ c : I, B c ⊆ C.skeleton q := fun c ↦
    Cubical.cell_boundary_subset_skeleton C q c.val c.property.1 c.property.2
  have hs := Cubical.cubical_positive_boundary_span N hN C q hq (by omega) hqN
  have hs' : Submodule.span ℚ (⋃ c : I,
      Set.range (Cubical.rationalSingularHomologyInclusion (hBS c) q)) = ⊤ := by
    convert hs using 2
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨⟨c, hc, hd⟩, z, hz⟩
      exact ⟨c, hc, hd, z, hz⟩
    · rintro ⟨c, hc, hd, z, hz⟩
      exact ⟨⟨c, hc, hd⟩, z, hz⟩
  have hB : ∀ c : I, IsCompact (a '' B c) := fun c ↦
    (Cubical.coordinate_cell_boundary_compact c.val).image a.continuous
  apply supportOperator_identity_of_spanning N O (a '' C.skeleton q) hO hK hKO q
    (fun c : I ↦ a '' B c) hB (fun c ↦ Set.image_mono (hBS c))
    (cubicalHomology_span N B (C.skeleton q) hBS q hs')
  intro c
  exact supportOperator_cellBoundary N q (by omega) (by omega) c.val c.property.2 O hO
    ((Set.image_mono (hBS c)).trans hKO) (hB c)


lemma cubicalHomology_deformationInclusion_isIso (N : ℕ) {A U : Set (Fin N → ℝ)}
    (hAU : A ⊆ U) (r : C(U, A))
    (hr : ∀ a : A, r ⟨a.val, hAU a.property⟩ = a)
    (H : (ContinuousMap.id U).HomotopyRel
      ((ContinuousMap.inclusion hAU).comp r) {x : U | x.val ∈ A}) (q : ℕ) :
    IsIso (homologyMap (TopCat.ofHom (ContinuousMap.inclusion
      (Set.image_mono hAU : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' A ⊆
        (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' U))) q) := by
  have := homologyMap_deformationInclusion_isIso hAU r hr H q
  have : IsIso (Cubical.rationalSingularHomologyInclusion hAU q) :=
    IsIso.of_isIso_fac_left
      (ordinaryRationalHomologyIso_naturality (TopCat.ofHom (ContinuousMap.inclusion hAU)) q).symm
  exact IsIso.of_isIso_fac_right (cubicalHomologyIso_naturality N hAU q)

/-- Injectivity between retracting neighborhoods follows from injectivity on their
retracts, using the commuting square of literal inclusions. -/
lemma homologyInclusion_injective_of_square {X : Type u} [TopologicalSpace X]
    {A B U V : Set X} (hAU : A ⊆ U) (hAB : A ⊆ B) (hBV : B ⊆ V) (hUV : U ⊆ V) (q : ℕ)
    [IsIso (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hAU)) q)]
    [IsIso (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hBV)) q)]
    (hinj : Function.Injective (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hAB)) q).hom) :
    Function.Injective (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q).hom := by
  let i := homologyMap (TopCat.ofHom (ContinuousMap.inclusion hAU)) q
  let j := homologyMap (TopCat.ofHom (ContinuousMap.inclusion hBV)) q
  let f := homologyMap (TopCat.ofHom (ContinuousMap.inclusion hAB)) q
  let g := homologyMap (TopCat.ofHom (ContinuousMap.inclusion hUV)) q
  have hsquare : i ≫ g = f ≫ j := by
    simp only [i, j, f, g, ← homologyMap_comp]
    rfl
  have hi : Function.Surjective i := (ModuleCat.epi_iff_surjective i).mp inferInstance
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective j).mp inferInstance
  intro x y hxy
  obtain ⟨x', rfl⟩ := hi x
  obtain ⟨y', rfl⟩ := hi y
  apply congrArg i
  apply hinj
  apply hj
  exact (congrArg (fun t : homology (TopCat.of A) q ⟶ homology (TopCat.of V) q ↦ t.hom x') hsquare).symm.trans
    (hxy.trans (congrArg (fun t : homology (TopCat.of A) q ⟶ homology (TopCat.of V) q ↦ t.hom y') hsquare))


lemma cubicalSkeleton_compact (N : ℕ) (C : Cubical.FiniteRectilinearSubdivision N) (q : ℕ) :
    IsCompact (C.skeleton q) := by
  unfold Cubical.FiniteRectilinearSubdivision.skeleton
  apply C.finite_cells.isCompact_biUnion
  intro c hc
  by_cases h : c.dimension ≤ q
  · simp only [h, Set.iUnion_true]
    exact isCompact_Icc
  · simp only [h, Set.iUnion_false]
    exact isCompact_empty

/-- A subcomplex contained in the q-skeleton inherits the degree-q support identity
through nested deformation neighborhoods and the skeleton inclusion's injectivity. -/
lemma supportOperator_cubicalSubcomplex_in_skeleton (N : ℕ) (hN : 1 ≤ N)
    (C : Cubical.FiniteRectilinearSubdivision N) (q : ℕ) (hq : q ≤ N)
    (D : Cubical.CubicalSubcomplex C) (hD : D.carrier ⊆ C.skeleton q)
    (O : Set (EuclideanSpace ℝ (Fin N))) (hO : IsOpen O)
    (hDO : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' D.carrier ⊆ O)
    (hDc : IsCompact ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' D.carrier)) :
    supportOperator N O _ hO hDc hDO q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hDO)) q).hom := by
  let a := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm
  obtain ⟨U, W, hU, hW, hSU, hDW, hWUV, hSr, hDr, _⟩ :=
    Cubical.cubical_skeleton_deformation_neighborhoods N hN C q hq D hD
      (a ⁻¹' O) (hO.preimage a.continuous) (fun x hx ↦ hDO (Set.mem_image_of_mem a hx))
  obtain ⟨hSU', rS, hrS, ⟨HS⟩⟩ := hSr
  obtain ⟨hDW', rD, hrD, ⟨HD⟩⟩ := hDr
  have hWU : W ⊆ U := fun _ hx ↦ (hWUV hx).1
  have hWO : a '' W ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hWUV hx).2
  have hUc : IsOpen (a '' U) := a.isOpenMap U hU
  have hWc : IsOpen (a '' W) := a.isOpenMap W hW
  have hSc : IsCompact (a '' C.skeleton q) := (cubicalSkeleton_compact N C q).image a.continuous
  have hSid := supportOperator_cubicalSkeleton N hN C q hq (a '' U) hUc
    (Set.image_mono hSU) hSc
  have hDid := supportOperator_identity_restrict_support N (a '' U) (a '' D.carrier)
    (a '' C.skeleton q) hUc hDc hSc (Set.image_mono hD) (Set.image_mono hSU) q hSid
  have := cubicalHomology_deformationInclusion_isIso N hSU' rS hrS HS q
  have := cubicalHomology_deformationInclusion_isIso N hDW' rD hrD HD q
  have hDi := (Cubical.cubical_skeleton_homology_comparison N hN C q hq D hD).1
  have hinj := homologyInclusion_injective_of_square (Set.image_mono hDW')
    (Set.image_mono hD) (Set.image_mono hSU') (Set.image_mono hWU) q
    (cubicalHomology_injective N hD q hDi)
  have hWid := supportOperator_identity_of_domain_injective N (a '' W) (a '' U)
    (a '' D.carrier) hWc hUc hDc (Set.image_mono hDW) (Set.image_mono hWU) q hinj hDid
  exact supportOperator_identity_enlarge_domain N (a '' W) O (a '' D.carrier)
    hWc hO hDc (Set.image_mono hDW) hWO q hWid


/-- A surjective inclusion from a compact subsupport transfers the support identity. -/
lemma supportOperator_identity_of_support_surjective (n : ℕ)
    (U K L : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ U) (q : ℕ)
    (hsurj : Function.Surjective (homologyMap
      (TopCat.ofHom (ContinuousMap.inclusion hKL)) q).hom)
    (h : supportOperator n U K hU hK (hKL.trans hLU) q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion (hKL.trans hLU))) q).hom) :
    supportOperator n U L hU hL hLU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hLU)) q).hom := by
  ext z
  obtain ⟨z, rfl⟩ := hsurj z
  rw [supportOperator_support n U K L hU hK hL hKL hLU, h]
  change _ = ((homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKL)) q ≫
    homologyMap (TopCat.ofHom (ContinuousMap.inclusion hLU)) q).hom z)
  rw [← homologyMap_comp]
  rfl

/-- Every finite cubical subcomplex satisfies the support identity in every degree.
In degree q its q-skeleton maps surjectively onto its homology; above the ambient
dimension the homology vanishes. -/
lemma supportOperator_cubicalSubcomplex (N : ℕ)
    (C : Cubical.FiniteRectilinearSubdivision N) (M : Cubical.CubicalSubcomplex C)
    (O : Set (EuclideanSpace ℝ (Fin N))) (hO : IsOpen O)
    (hMO : (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' M.carrier ⊆ O)
    (hMc : IsCompact ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' M.carrier)) (q : ℕ) :
    supportOperator N O _ hO hMc hMO q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hMO)) q).hom := by
  by_cases hq0 : q = 0
  · subst q
    exact supportOperator_zero N O _ hO hMc hMO
  by_cases hq : N < q
  · have := Cubical.cubical_subcomplex_high_degree_homology_subsingleton C M q hq
    have : Subsingleton (homology (TopCat.of
        ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm '' M.carrier)) q) :=
      (cubicalHomologyIso N M.carrier q).toLinearEquiv.injective.subsingleton
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  let a := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm
  let D : Cubical.CubicalSubcomplex C := {
    cells := {c | c ∈ M.cells ∧ c.dimension ≤ q}
    subset_cells := fun _ hc ↦ M.subset_cells hc.1
    faces := fun c hc b hb ↦ ⟨M.faces c hc.1 b hb, hb.dimension_le.trans hc.2⟩ }
  have hDM : D.carrier = M.skeleton q := by
    ext x
    simp only [D, Cubical.CubicalSubcomplex.carrier, Cubical.CubicalSubcomplex.skeleton,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    aesop
  have hD : D.carrier ⊆ C.skeleton q := by
    intro x hx
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Cubical.cell_carrier_subset_skeleton C q c (M.subset_cells hc.1) hc.2 hx
  have hsurj := Cubical.cubical_subcomplex_skeleton_homology_surjective C M q
  rw [← hDM] at hsurj
  obtain ⟨hMS, hsurj⟩ := hsurj
  have hDc : IsCompact (a '' D.carrier) :=
    (Cubical.finiteCellUnion_compact C D.cells D.subset_cells).image a.continuous
  have hDid := supportOperator_cubicalSubcomplex_in_skeleton N (by omega) C q (by omega)
    D hD O hO ((Set.image_mono hMS).trans hMO) hDc
  exact supportOperator_identity_of_support_surjective N O (a '' D.carrier) (a '' M.carrier)
    hO hDc hMc (Set.image_mono hMS) hMO q (cubicalHomology_surjective N hMS q hsurj) hDid


/-- Dold (1965), Lemma (4.2), proved by the §5 sphere-collar and cubical reduction.
The support operator is the map induced by inclusion for every compact support
in every open Euclidean neighborhood, in every nonnegative degree. -/
theorem supportOperator_identity (N : ℕ) (U K : Set (EuclideanSpace ℝ (Fin N)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (q : ℕ) :
    supportOperator N U K hU hK hKU q =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
  let a := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).symm
  have hKa : IsCompact (a.symm '' K) := hK.image a.symm.continuous
  have hKaU : a.symm '' K ⊆ a ⁻¹' U := by
    rintro _ ⟨x, hx, rfl⟩
    change a (a.symm x) ∈ U
    simpa only [a.apply_symm_apply] using hKU hx
  obtain ⟨C, P, hKP, hPU⟩ := Cubical.finite_cubical_compact_neighborhood N
    (a.symm '' K) (a ⁻¹' U) hKa (hU.preimage a.continuous) hKaU
  have hKL : K ⊆ a '' P.carrier := by
    intro x hx
    exact ⟨a.symm x, hKP (Set.mem_image_of_mem a.symm hx), a.apply_symm_apply x⟩
  have hLU : a '' P.carrier ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPU hx
  have hL : IsCompact (a '' P.carrier) :=
    (Cubical.finiteCellUnion_compact C P.cells P.subset_cells).image a.continuous
  exact supportOperator_identity_restrict_support N U K (a '' P.carrier) hU hK hL hKL hLU q
    (supportOperator_cubicalSubcomplex N C P U hU hLU hL q)



end DoldConstruction
end HolomorphicAnosov.FixedPointIndexInterface

