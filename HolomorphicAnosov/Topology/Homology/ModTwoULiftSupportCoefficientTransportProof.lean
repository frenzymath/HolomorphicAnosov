import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftDegree
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftBoundary
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftNaturality
import HolomorphicAnosov.Topology.ChainComplexModTwoIsoHomology
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Grp.Ulift

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov.Topology.Homology
universe u
noncomputable section
noncomputable instance modTwoULiftPreservesColimitsOfShape
    {J : Type} [Category.{0} J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{u,0} (ZMod 2)) := by
  let F := ModuleCat.uliftFunctor.{u,0} (ZMod 2)
  let G : ModuleCat.{u} (ZMod 2) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (ZMod 2)) (AddCommGrpCat.{u})
  let H : ModuleCat.{0} (ZMod 2) ⥤ AddCommGrpCat.{0} :=
    forget₂ (ModuleCat.{0} (ZMod 2)) (AddCommGrpCat.{0})
  let I : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{u} := AddCommGrpCat.uliftFunctor.{u,0}
  let e : F ⋙ G ≅ H ⋙ I := NatIso.ofComponents (fun X => Iso.refl _) (by intros; rfl)
  let : ReflectsColimitsOfShape J G := by
    change ReflectsColimitsOfShape J
      (forget₂ (ModuleCat.{u} (ZMod 2)) (AddCommGrpCat.{u}))
    exact @ModuleCat.reflectsColimitsOfShape.{u, 0, 0, 0} (ZMod 2) inferInstance J inferInstance inferInstance
  let : PreservesColimitsOfShape J (H ⋙ I) := by
    change PreservesColimitsOfShape J
      ((forget₂ (ModuleCat.{0} (ZMod 2)) (AddCommGrpCat.{0})) ⋙
        AddCommGrpCat.uliftFunctor.{u,0})
    infer_instance
  let : PreservesColimitsOfShape J (F ⋙ G) := preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves F G


def liftedPair (X : Type) [TopologicalSpace X] (A : Set X) : SSetPair.{u} :=
  let i : TopCat.of (Aᶜ : Set X) ⟶ TopCat.of X := TopCat.ofHom
    ⟨Subtype.val, continuous_subtype_val⟩
  letI : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  let j := TopCat.uliftFunctor.{u, 0}.map i
  SSetPair.of (TopCat.toSSet.map j)

def actualPair (X : Type) [TopologicalSpace X] (A : Set X) : SSetPair.{u} :=
  singularSubspacePair (ULift.{u} X) (ULift.down ⁻¹' Aᶜ)

def actualLeftIso (X : Type) [TopologicalSpace X] (A : Set X) :
    TopCat.of (↑((ULift.down ⁻¹' A)ᶜ)) ≅
      TopCat.uliftFunctor.{u, 0}.obj (TopCat.of (Aᶜ : Set X)) :=
  TopCat.isoOfHomeo {
    toFun := fun y ↦ ULift.up ⟨y.1.down, y.2⟩
    invFun := fun z ↦ ⟨ULift.up z.down, z.down.property⟩
    left_inv := by intro y; cases y; rfl
    right_inv := by intro z; cases z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

def actualRightIso (X : Type) [TopologicalSpace X] :
    TopCat.of (ULift.{u} X) ≅ TopCat.uliftFunctor.{u, 0}.obj (TopCat.of X) :=
  TopCat.isoOfHomeo (Homeomorph.refl (ULift.{u} X))

def actualPairIso (X : Type) [TopologicalSpace X] (A : Set X) :
    actualPair X A ≅ liftedPair X A := by
  let eL := actualLeftIso X A
  let eR := actualRightIso X
  refine MorphismProperty.Arrow.isoMk (TopCat.toSSet.mapIso eL)
    (TopCat.toSSet.mapIso eR) ?_
  change TopCat.toSSet.map eL.hom ≫ TopCat.toSSet.map
      (TopCat.uliftFunctor.map (TopCat.ofHom _)) = TopCat.toSSet.map _ ≫ TopCat.toSSet.map eR.hom
  rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
  apply congrArg TopCat.toSSet.map
  ext z
  rfl

def absIso (T : TopCat.{0}) :
    (TopCat.toSSet.obj (TopCat.uliftFunctor.{u, 0}.obj T)).chainComplex
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≅
      ((ModuleCat.uliftFunctor.{u, 0} (ZMod 2)).mapHomologicalComplex (.down ℕ)).obj
        ((TopCat.toSSet.obj T).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))) := by
  let Y : TopCat.{u} := TopCat.uliftFunctor.{u, 0}.obj T
  let K : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
    (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
  let L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
    (TopCat.toSSet.obj T).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))
  let e : ∀ n, K.X n ≃ₗ[ZMod 2] L.X n := fun n ↦
    Classical.choose (singular_chains_ulift_modtwo_degree_comparison (X := T) n)
  have hegen : ∀ n (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} (ZMod 2)),
      e n (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a) =
      ((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2))
        (((Y.toSSetObjEquiv (op ⦋n⦌)).trans
          ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
            (Homeomorph.ulift : ULift.{u} T ≃ₜ T)).trans
              (T.toSSetObjEquiv (op ⦋n⦌)).symm)) σ)) a.down := by
    intro n
    exact Classical.choose_spec (singular_chains_ulift_modtwo_degree_comparison (X := T) n)
  have he : ∀ n x, e n (K.d (n + 1) n x) = L.d (n + 1) n (e (n + 1) x) := by
    intro n x
    exact singular_chains_ulift_modtwo_boundary (X := T) (fun n ↦ (e n).toLinearMap)
      hegen n x
  let F := ModuleCat.uliftFunctor.{u, 0} (ZMod 2)
  let LF := F.mapHomologicalComplex (.down ℕ)
  let ei (n : ℕ) : K.X n ≅ (LF.obj L).X n :=
    ((e n).trans (ULift.moduleEquiv.symm : L.X n ≃ₗ[ZMod 2] ULift.{u} (L.X n))).toModuleIso
  have hei : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (ei i).hom ≫ (LF.obj L).d i j = K.d i j ≫ (ei j).hom := by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    ext x
    exact congrArg ULift.up (he j x).symm
  exact HomologicalComplex.Hom.isoOfComponents ei hei

lemma absIso_down (T : TopCat.{0}) (n : ℕ) (x : ((TopCat.toSSet.obj (TopCat.uliftFunctor.{u,0}.obj T)).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).X n) :
    ((absIso T).hom.f n x).down =
      Classical.choose (singular_chains_ulift_modtwo_degree_comparison (X := T) n) x := by
  rfl

def relativeIso (X : Type) [TopologicalSpace X] (A : Set X) :
    (actualPair X A).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≅
      ((ModuleCat.uliftFunctor.{u, 0} (ZMod 2)).mapHomologicalComplex (.down ℕ)).obj
        ((singularSubspacePair X Aᶜ).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))) := by
  let P := singularSubspacePair X Aᶜ
  let R := actualPair X A
  let Q := liftedPair X A
  let pIso : R ≅ Q := actualPairIso X A
  let F := ModuleCat.uliftFunctor.{u, 0} (ZMod 2)
  let G := F.mapHomologicalComplex (.down ℕ)
  let eL := absIso (TopCat.of (Aᶜ : Set X))
  let eR := absIso (TopCat.of X)
  let relIso : R.chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≅
      G.obj (P.chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))) := by
    exact CokernelCofork.mapIsoOfIsColimit
      (R.isColimitCokernelCoforkChainComplex
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))))
      (CokernelCofork.mapIsColimit _
        (P.isColimitCokernelCoforkChainComplex (ModuleCat.of (ZMod 2) (ZMod 2))) G)
      (Arrow.isoMk
        (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso
            (TopCat.toSSet.mapIso (actualLeftIso X A)) ≪≫ eL)
        (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso
            (TopCat.toSSet.mapIso (actualRightIso X)) ≪≫ eR)
        (by
          let fL := ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso
              (TopCat.toSSet.mapIso (actualLeftIso X A))
          let fR := ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso
              (TopCat.toSSet.mapIso (actualRightIso X))
          have hp : fL.hom ≫ SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) =
              SSet.chainComplexMap R.hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≫ fR.hom := by
            let H := (SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
              (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
            change H.map (TopCat.toSSet.map (actualLeftIso X A).hom) ≫
              H.map (TopCat.toSSet.map (TopCat.uliftFunctor.map (TopCat.ofHom _))) =
              H.map (TopCat.toSSet.map _) ≫ H.map (TopCat.toSSet.map (actualRightIso X).hom)
            rw [← H.map_comp, ← H.map_comp]
            exact congrArg
              (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
                (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).map)
              ((actualPairIso X A).hom.w)
          have ha : eL.hom ≫ G.map (SSet.chainComplexMap P.hom (ModuleCat.of (ZMod 2) (ZMod 2))) =
              (SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≫ eR.hom) := by
            let f : C(TopCat.of (Aᶜ : Set X), TopCat.of X) :=
              ⟨Subtype.val, continuous_subtype_val⟩
            ext n x
            let eLX := ULift.moduleEquiv.toLinearMap.comp (eL.hom.f n).hom
            let eRZ := ULift.moduleEquiv.toLinearMap.comp (eR.hom.f n).hom
            have hn := singular_chains_ulift_modtwo_naturality (X := TopCat.of (Aᶜ : Set X))
              (Z := TopCat.of X) f n eLX eRZ
            have hnat := hn (by
              intro σ a
              change (((absIso (TopCat.of (Aᶜ : Set X))).hom.f n)
                (((TopCat.toSSet.obj (TopCat.uliftFunctor.{u,0}.obj (TopCat.of (Aᶜ : Set X)))).ιChainComplex
                  (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ).hom a)).down = _
              rw [absIso_down]
              exact Classical.choose_spec (singular_chains_ulift_modtwo_degree_comparison
                  (X := TopCat.of (Aᶜ : Set X)) n) σ a) (by
              intro σ a
              change (((absIso (TopCat.of X)).hom.f n)
                (((TopCat.toSSet.obj (TopCat.uliftFunctor.{u,0}.obj (TopCat.of X))).ιChainComplex
                  (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ).hom a)).down = _
              rw [absIso_down]
              exact Classical.choose_spec (singular_chains_ulift_modtwo_degree_comparison
                  (X := TopCat.of X) n) σ a) x
            apply ULift.ext
            have hPright : P.right = TopCat.toSSet.obj (TopCat.of X) := by
              dsimp [P, singularSubspacePair]
              rfl
            cases hPright
            have htype :
                (((𝟭 SSet).obj P.right).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).X n =
                  ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).X n := by
              dsimp [P, singularSubspacePair]
              rfl
            cases htype
            change ((ModuleCat.Hom.hom ((eL.hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (SSet.chainComplexMap P.hom (ModuleCat.of (ZMod 2) (ZMod 2)))).f n)) x).down = _
            rw [HomologicalComplex.comp_f]
            simp only [CategoryTheory.comp_apply]
            change (ModuleCat.Hom.hom (F.map ((SSet.chainComplexMap P.hom (ModuleCat.of (ZMod 2) (ZMod 2))).f n)) ((ModuleCat.Hom.hom (eL.hom.f n)) x)).down = _
            rw [ModuleCat.uliftFunctor_map]
            convert hnat using 1 <;> try rfl
            case e'_2 =>
              apply heq_of_eq
              dsimp
              change ((SSet.chainComplexMap P.hom (ModuleCat.of (ZMod 2) (ZMod 2))).f n).hom
                (ULift.moduleEquiv.toLinearMap ((ModuleCat.Hom.hom (eL.hom.f n)) x)) = _
              dsimp [P, singularSubspacePair]
              change (ConcreteCategory.hom
                ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
                  (ModuleCat.of (ZMod 2) (ZMod 2))).f n)) (eLX x) = _
              exact hnat.symm
            case e'_3 =>
              apply heq_of_eq
              dsimp [P, singularSubspacePair, liftedPair, f]
              change eRZ _ = _
              exact hnat
          change (fL ≪≫ eL).hom ≫ G.map (SSet.chainComplexMap P.hom (ModuleCat.of (ZMod 2) (ZMod 2))) =
            SSet.chainComplexMap R.hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) ≫ (fR ≪≫ eR).hom
          rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, ha]
          dsimp [liftedPair] at ⊢
          change (fL.hom ≫ SSet.chainComplexMap (liftedPair X A).hom _ ≫ eR.hom) =
            (SSet.chainComplexMap R.hom _ ≫ fR.hom ≫ eR.hom)
          exact (Category.assoc fL.hom
            (SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))) eR.hom).symm.trans
            ((congrArg (fun t ↦ t ≫ eR.hom) hp).trans
              (Category.assoc (SSet.chainComplexMap R.hom (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))) fR.hom eR.hom))))
  exact relIso

 theorem modTwo_ulift_support_coefficient_transport_proved
    (X : Type) [TopologicalSpace X] (A : Set X) (k : ℕ) :
    Nonempty (modTwoSupportHomology
      (ULift.{u} X) (Set.ofPred (fun y : ULift.{u} X => y.down ∈ A)) k ≃ₗ[ZMod 2]
      modTwoSupportHomology X A k) := by
  let rel := relativeIso X A
  let H := HomologicalComplex.homologyMapIso rel k
  let q := (((singularSubspacePair X Aᶜ).chainComplex
      (ModuleCat.of (ZMod 2) (ZMod 2))).sc k).mapHomologyIso
      (ModuleCat.uliftFunctor.{u,0} (ZMod 2))
  let h := (H ≪≫ q).toLinearEquiv.trans ULift.moduleEquiv
  let coeffIso : ModuleCat.of (ZMod 2) (ZMod 2) ≅
      ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)) :=
    (ULift.moduleEquiv.symm : ZMod 2 ≃ₗ[ZMod 2] ULift.{0} (ZMod 2)).toModuleIso
  let ci := ((SSetPair.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).mapIso coeffIso).app
    (singularSubspacePair X Aᶜ)
  let hi := HomologicalComplex.homologyMapIso ci k
  exact ⟨h.trans hi.toLinearEquiv⟩


end
end HolomorphicAnosov.Topology.Homology
