import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData
import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftComplex

import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftNaturalityG14
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Grp.Ulift

section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov.IntegralTransportG14
open HolomorphicAnosov.Topology.Homology
universe u
noncomputable section

/-- Compose a module equivalence with the exact functorial universe lift.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def liftedLinearIso {R : Type} [Ring R]
    (M : ModuleCat.{u} R) (N : ModuleCat.{0} R) (e : M ≃ₗ[R] N) :
    M ≅ (ModuleCat.uliftFunctor.{u, 0} R).obj N :=
  (e.trans (ULift.moduleEquiv.symm : N ≃ₗ[R] ULift.{u} N)).toModuleIso

local instance integralULiftPreservesColimitsOfShape
    {J : Type} [Category.{0} J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{u,0} ℤ) := by
  let F := ModuleCat.uliftFunctor.{u,0} ℤ
  let G : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} ℤ) (AddCommGrpCat.{u})
  let H : ModuleCat.{0} ℤ ⥤ AddCommGrpCat.{0} :=
    forget₂ (ModuleCat.{0} ℤ) (AddCommGrpCat.{0})
  let I : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{u} := AddCommGrpCat.uliftFunctor.{u,0}
  let e : F ⋙ G ≅ H ⋙ I := NatIso.ofComponents (fun X ↦ Iso.refl _) (by intros; rfl)
  let : ReflectsColimitsOfShape J G := by
    change ReflectsColimitsOfShape J
      (forget₂ (ModuleCat.{u} ℤ) (AddCommGrpCat.{u}))
    exact @ModuleCat.reflectsColimitsOfShape.{u, 0, 0, 0} ℤ inferInstance J inferInstance inferInstance
  let : PreservesColimitsOfShape J (H ⋙ I) := by
    change PreservesColimitsOfShape J
      ((forget₂ (ModuleCat.{0} ℤ) (AddCommGrpCat.{0})) ⋙
        AddCommGrpCat.uliftFunctor.{u,0})
    infer_instance
  let : PreservesColimitsOfShape J (F ⋙ G) := preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves F G


/-- The singular pair of the universe-lifted complement inclusion.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def liftedPair (X : Type) [TopologicalSpace X] (A : Set X) : SSetPair.{u} :=
  let i : TopCat.of (Aᶜ : Set X) ⟶ TopCat.of X := TopCat.ofHom
    ⟨Subtype.val, continuous_subtype_val⟩
  letI : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  let j := TopCat.uliftFunctor.{u, 0}.map i
  SSetPair.of (TopCat.toSSet.map j)

/-- The singular pair of the actual complement of the lifted support.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def actualPair (X : Type) [TopologicalSpace X] (A : Set X) : SSetPair.{u} :=
  HolomorphicAnosov.Topology.Homology.singularSubspacePair (ULift.{u} X) (ULift.down ⁻¹' Aᶜ)

/-- Identify the actual complement with the universe lift of the native complement.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
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

/-- Identify the lifted ambient space with its functorial lift.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def actualRightIso (X : Type) [TopologicalSpace X] :
    TopCat.of (ULift.{u} X) ≅ TopCat.uliftFunctor.{u, 0}.obj (TopCat.of X) :=
  TopCat.isoOfHomeo (Homeomorph.refl (ULift.{u} X))

/-- The complement and ambient identifications commute with inclusion.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
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

/-- Assemble the integral degree comparisons using their boundary compatibility.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def absIso (T : TopCat.{0}) :
    (TopCat.toSSet.obj (TopCat.uliftFunctor.{u, 0}.obj T)).chainComplex
      (ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (.down ℕ)).obj
        ((TopCat.toSSet.obj T).chainComplex (ModuleCat.of ℤ ℤ)) := by
  let Y : TopCat.{u} := TopCat.uliftFunctor.{u, 0}.obj T
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
    (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
  let L : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
    (TopCat.toSSet.obj T).chainComplex (ModuleCat.of ℤ ℤ)
  let e : ∀ n, K.X n ≃ₗ[ℤ] L.X n := fun n ↦
    Classical.choose (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison T n)
  have hegen : ∀ n (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℤ),
      e n (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a) =
      ((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (((Y.toSSetObjEquiv (op ⦋n⦌)).trans
          ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
            (Homeomorph.ulift : ULift.{u} T ≃ₜ T)).trans
              (T.toSSetObjEquiv (op ⦋n⦌)).symm)) σ)) a.down := by
    intro n
    exact Classical.choose_spec (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison T n)
  have he : ∀ n x, e n (K.d (n + 1) n x) = L.d (n + 1) n (e (n + 1) x) := by
    intro n x
    exact HolomorphicAnosov.singular_chains_ulift_integral_boundary (X := T) (fun n ↦ (e n).toLinearMap)
      hegen n x
  let F := ModuleCat.uliftFunctor.{u, 0} ℤ
  let LF := F.mapHomologicalComplex (.down ℕ)
  let ei (n : ℕ) : K.X n ≅ (LF.obj L).X n :=
    liftedLinearIso (K.X n) (L.X n) (e n)
  have hei : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (ei i).hom ≫ (LF.obj L).d i j = K.d i j ≫ (ei j).hom := by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    ext x
    exact congrArg ULift.up (he j x).symm
  exact HomologicalComplex.Hom.isoOfComponents ei hei

/-- The assembled comparison retains the original degreewise down projection.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
lemma absIso_down (T : TopCat.{0}) (n : ℕ) (x : ((TopCat.toSSet.obj (TopCat.uliftFunctor.{u,0}.obj T)).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n) :
    ((absIso T).hom.f n x).down =
      Classical.choose (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison T n) x := by
  rfl

/-- Descend the natural square of absolute chain isomorphisms through relative cokernels.
Source: Hatcher, Algebraic Topology §2.1 pp.108–118; explicit universe adapter. -/
def relativeIso (X : Type) [TopologicalSpace X] (A : Set X) :
    (actualPair X A).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (.down ℕ)).obj
        ((HolomorphicAnosov.Topology.Homology.singularSubspacePair X Aᶜ).chainComplex (ModuleCat.of ℤ ℤ)) := by
  let P := HolomorphicAnosov.Topology.Homology.singularSubspacePair X Aᶜ
  let R := actualPair X A
  let Q := liftedPair X A
  let pIso : R ≅ Q := actualPairIso X A
  let F := ModuleCat.uliftFunctor.{u, 0} ℤ
  let G := F.mapHomologicalComplex (.down ℕ)
  let eL := absIso (TopCat.of (Aᶜ : Set X))
  let eR := absIso (TopCat.of X)
  let relIso : R.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      G.obj (P.chainComplex (ModuleCat.of ℤ ℤ)) := by
    exact CokernelCofork.mapIsoOfIsColimit
      (R.isColimitCokernelCoforkChainComplex
        (ModuleCat.of ℤ (ULift.{u} ℤ)))
      (CokernelCofork.mapIsColimit _
        (P.isColimitCokernelCoforkChainComplex (ModuleCat.of ℤ ℤ)) G)
      (Arrow.isoMk
        (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).mapIso
            (TopCat.toSSet.mapIso (actualLeftIso X A)) ≪≫ eL)
        (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).mapIso
            (TopCat.toSSet.mapIso (actualRightIso X)) ≪≫ eR)
        (by
          let fL := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
            (ModuleCat.of ℤ (ULift.{u} ℤ))).mapIso
              (TopCat.toSSet.mapIso (actualLeftIso X A))
          let fR := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
            (ModuleCat.of ℤ (ULift.{u} ℤ))).mapIso
              (TopCat.toSSet.mapIso (actualRightIso X))
          have hp : fL.hom ≫ SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of ℤ (ULift.{u} ℤ)) =
              SSet.chainComplexMap R.hom (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫ fR.hom := by
            let H := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
              (ModuleCat.of ℤ (ULift.{u} ℤ))
            change H.map (TopCat.toSSet.map (actualLeftIso X A).hom) ≫
              H.map (TopCat.toSSet.map (TopCat.uliftFunctor.map (TopCat.ofHom _))) =
              H.map (TopCat.toSSet.map _) ≫ H.map (TopCat.toSSet.map (actualRightIso X).hom)
            rw [← H.map_comp, ← H.map_comp]
            exact congrArg
              (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
                (ModuleCat.of ℤ (ULift.{u} ℤ))).map)
              ((actualPairIso X A).hom.w)
          have ha : eL.hom ≫ G.map (SSet.chainComplexMap P.hom (ModuleCat.of ℤ ℤ)) =
              (SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫ eR.hom) := by
            let f : C(TopCat.of (Aᶜ : Set X), TopCat.of X) :=
              ⟨Subtype.val, continuous_subtype_val⟩
            ext n x
            let eLX := (Classical.choose (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison.{u} (TopCat.of (Aᶜ : Set X)) n)).toLinearMap
            let eRZ := (Classical.choose (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison.{u} (TopCat.of X) n)).toLinearMap
            have hn := singular_chains_ulift_integral_naturality_g14 (X := TopCat.of (Aᶜ : Set X))
              (Z := TopCat.of X) f n eLX eRZ
            have hnat := hn
              (Classical.choose_spec (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison.{u} (TopCat.of (Aᶜ : Set X)) n))
              (Classical.choose_spec (HolomorphicAnosov.singular_chains_ulift_integral_degree_comparison.{u} (TopCat.of X) n)) x
            apply ULift.ext
            exact hnat.symm
          change (fL ≪≫ eL).hom ≫ G.map (SSet.chainComplexMap P.hom (ModuleCat.of ℤ ℤ)) =
            SSet.chainComplexMap R.hom (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫ (fR ≪≫ eR).hom
          rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, ha]
          dsimp [liftedPair] at ⊢
          change (fL.hom ≫ SSet.chainComplexMap (liftedPair X A).hom _ ≫ eR.hom) =
            (SSet.chainComplexMap R.hom _ ≫ fR.hom ≫ eR.hom)
          exact (Category.assoc fL.hom
            (SSet.chainComplexMap (liftedPair X A).hom (ModuleCat.of ℤ (ULift.{u} ℤ))) eR.hom).symm.trans
            ((congrArg (fun t ↦ t ≫ eR.hom) hp).trans
              (Category.assoc (SSet.chainComplexMap R.hom (ModuleCat.of ℤ (ULift.{u} ℤ))) fR.hom eR.hom))))
  exact relIso


end
end HolomorphicAnosov.IntegralTransportG14

end

/-! # Relative integral support-chain comparison across universes -/
noncomputable section
open CategoryTheory
namespace HolomorphicAnosov
open HolomorphicAnosov.Topology _root_.Topology
universe u

/-- The canonical absolute ULift chain comparisons descend to relative support chains.

Source: Hatcher, Algebraic Topology, §2.1 pp.108–118, particularly relative
quotient chains p.115 and maps of pairs p.118; coefficients p.153.

Proof: Write B = X ∖ A and identify ULift B with the complement of the lifted
support by (up b) ↦ (up b.val), with inverse obtained by lowering the point and
its nonmembership proof. These maps are inverse continuous maps for the induced
subspace topologies. Apply the absolute chain-complex comparison to X and B,
using this homeomorphism to identify the high subspace chain complex. Their
square with the two inclusion chain maps commutes: on each singular-simplex
generator both routes lower the simplex, include its values in X, and lower its
integer coefficient. The coproduct universal property extends this equality to
all chains. Relative chains are the categorical cokernel of the inclusion, so
this commuting square of chain isomorphisms gives an isomorphism of cokernels.
ModuleCat.uliftFunctor preserves finite colimits; its induced functor on chain
complexes therefore preserves this cokernel, identifying the small cokernel's
lift with that of the lifted small inclusion. Compose these isomorphisms. All
maps are chain maps by the proved absolute boundary compatibility; no homology,
excision, compactness, or freeness assertion beyond these chain facts is needed.

Formalization gap: the explicit subspace homeomorphism, the generator square,
and its cokernel comparison remain to be supplied. This is a named provider
for that precise quotient descent. Empty/full supports and degree zero use the
same cokernel construction without exceptions. -/
theorem integral_ulift_support_chain_comparison
    (X : Type) [TopologicalSpace X] (A : Set X) :
    Nonempty (supportSingularChainComplex (TopCat.of (ULift.{u} X))
      {y : ULift.{u} X | y.down ∈ A} (ModuleCat.of ℤ (ULift.{u} ℤ)) ≅
      ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (.down ℕ)).obj
        (supportSingularChainComplex (TopCat.of X) A (ModuleCat.of ℤ ℤ))) := by
  exact ⟨IntegralTransportG14.relativeIso.{u} X A⟩

end HolomorphicAnosov

