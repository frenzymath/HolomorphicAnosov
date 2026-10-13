import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Scalar transport for the existing rational signed shuffle

This concrete construction changes scalars only along the actual ring equivalence
`ULift ℚ ≃+* ℚ`. It copies no shuffle formula and postulates no new chain data.
The lifted ring lives in the same universe as the native module carriers, so Mathlib's
monoidal module category applies. Source: Bredon VI §1 pp.316–320; the rational field
and its universe lift are identified by Mathlib's ring and module equivalences.

The source constructions are Mathlib restrictScalarsEquivalenceOfRingEquiv,
chainComplexFunctorObjCompMapIso, equivOfCompatibleSMul, mapHomologyIso and
CokernelCofork.mapIsoOfIsColimit at revision c32e1ec0d1eb5237ba344eee50162f45d5b0fc76.
All definitions contain actual data; there is no admitted comparison or shuffle law.
DAG node: `algebra.rational_ulift_scalar_transport_g10`.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace HolomorphicAnosov.RationalScalarTransport

/-- The genuine rational field in the module-carrier universe. -/
abbrev LiftQ := ULift.{u} ℚ

/-- The canonical change of scalars retains the module's underlying additive group. -/
abbrev scalarFunctor : ModuleCat.{u} ℚ ⥤ ModuleCat.{u} LiftQ.{u} :=
  ModuleCat.restrictScalars (ULift.ringEquiv : LiftQ.{u} ≃+* ℚ).toRingHom

/-- The same scalar functor has a canonical inverse, with no chosen linearization. -/
def scalarEquivalence : ModuleCat.{u} ℚ ≌ ModuleCat.{u} LiftQ.{u} :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv : LiftQ.{u} ≃+* ℚ)

/-- The native rational coefficient object, with its ordinary rational action. -/
abbrev qCoefficients : ModuleCat.{u} ℚ := ModuleCat.of ℚ LiftQ.{u}

/-- The coefficient object after scalar transport, unchanged as additive data. -/
abbrev liftedCoefficients : ModuleCat.{u} LiftQ.{u} := scalarFunctor.obj qCoefficients

/-- Native rational chains transported to the lifted rational scalar field. -/
abbrev transportedChains (X : SSet.{u}) :=
  (scalarFunctor.mapHomologicalComplex (.down ℕ)).obj (X.chainComplex qCoefficients)

/-- The actual natural chain comparison: scalar change commutes with all simplex coproducts
and with the alternating-face differential. -/
def chainComparison (X : SSet.{u}) :
    transportedChains X ≅ X.chainComplex liftedCoefficients :=
  (SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients).app X

/-- The transported coefficient is canonically the lifted ring's monoidal unit. -/
def coefficientComparison : liftedCoefficients ≅ ModuleCat.of LiftQ.{u} LiftQ.{u} :=
  (show liftedCoefficients ≃ₗ[LiftQ.{u}] LiftQ.{u} from
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }).toModuleIso

/-- Canonical unchanged pure tensors, with the base ring replaced by its universe lift. -/
instance rationalLiftCompatible (M N : ModuleCat.{u} ℚ) :
    TensorProduct.CompatibleSMul ℚ LiftQ.{u} (scalarFunctor.obj M) (scalarFunctor.obj N) where
  smul_tmul r m n := TensorProduct.smul_tmul r.down m n

/-- The reverse compatibility uses the same rational scalar as its lifted representative. -/
instance liftRationalCompatible (M N : ModuleCat.{u} ℚ) :
    TensorProduct.CompatibleSMul LiftQ.{u} ℚ (scalarFunctor.obj M) (scalarFunctor.obj N) where
  smul_tmul r m n := TensorProduct.smul_tmul (ULift.up r : LiftQ.{u}) m n

/-- Canonical unchanged pure tensors, with the base ring replaced by its universe lift. -/
def tensorScalarComparison (M N : ModuleCat.{u} ℚ) :
    scalarFunctor.obj M ⊗[LiftQ.{u}] scalarFunctor.obj N ≃ₗ[LiftQ.{u}]
      scalarFunctor.obj M ⊗[ℚ] scalarFunctor.obj N := by
  letI := rationalLiftCompatible M N
  letI := liftRationalCompatible M N
  let hLL : SMulCommClass LiftQ.{u} LiftQ.{u} (scalarFunctor.obj M) :=
    ⟨fun r s m ↦ smul_comm r.down s.down m⟩
  exact @TensorProduct.equivOfCompatibleSMul ℚ _ LiftQ.{u} LiftQ.{u}
    (scalarFunctor.obj M) (scalarFunctor.obj N) _ _ _ _ _ _ _ _ _ _ _ hLL
    (rationalLiftCompatible M N) (liftRationalCompatible M N)

/-- The actual chain map obtained by scalar transport and the two native chain comparisons. -/
def chainMapTransport {X Y : SSet.{u}}
    (f : X.chainComplex qCoefficients ⟶ Y.chainComplex qCoefficients) :
    X.chainComplex liftedCoefficients ⟶ Y.chainComplex liftedCoefficients :=
  (chainComparison X).inv ≫ (scalarFunctor.mapHomologicalComplex (.down ℕ)).map f ≫
    (chainComparison Y).hom

/-- Homology transports naturally because the ring-equivalence functor preserves kernels
and cokernels; no cycle representatives or arbitrary homology coordinates are selected. -/
def homologyComparison (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (n : ℕ) :
    ((scalarFunctor.mapHomologicalComplex (.down ℕ)).obj C).homology n ≅
      scalarFunctor.obj (C.homology n) :=
  (C.sc n).mapHomologyIso scalarFunctor

/-- The relative chain comparison comes from the original cokernel universal properties
and the natural absolute-chain comparison, not from a supplied relative isomorphism. -/
def relativeChainComparison (P : SSetPair.{u}) :
    (scalarFunctor.mapHomologicalComplex (.down ℕ)).obj (P.chainComplex qCoefficients) ≅
      P.chainComplex liftedCoefficients :=
  CokernelCofork.mapIsoOfIsColimit
    (isColimitCoforkMapOfIsColimit' (scalarFunctor.mapHomologicalComplex (.down ℕ))
      (P.chainComplex_condition qCoefficients) (P.isColimitCokernelCoforkChainComplex qCoefficients))
    (P.isColimitCokernelCoforkChainComplex liftedCoefficients)
    (Arrow.isoMk (chainComparison P.left) (chainComparison P.right)
      ((SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients).hom.naturality P.hom).symm)

/-- Native relative homology uses the same scalar equivalence and actual relative complex. -/
def relativeHomologyComparison (P : SSetPair.{u}) (n : ℕ) :
    scalarFunctor.obj ((P.chainComplex qCoefficients).homology n) ≅
      (P.chainComplex liftedCoefficients).homology n :=
  (homologyComparison (P.chainComplex qCoefficients) n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} LiftQ.{u}) (.down ℕ) n).mapIso
      (relativeChainComparison P)

/-- Transport the actual map induced by a map of pairs on the original relative homology. -/
def relativeHomologyMapTransport {P P' : SSetPair.{u}} (f : P ⟶ P') (n : ℕ) :
    (P.chainComplex liftedCoefficients).homology n ⟶
      (P'.chainComplex liftedCoefficients).homology n :=
  (relativeHomologyComparison P n).inv ≫
    scalarFunctor.map (SSetPair.homologyMap f qCoefficients n) ≫
    (relativeHomologyComparison P' n).hom

/-- The comparison lands in native chains with the lifted ring itself as coefficient unit. -/
def nativeChainComparison (X : SSet.{u}) :
    transportedChains X ≅ X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u}) :=
  chainComparison X ≪≫
    ((SSet.chainComplexFunctor (ModuleCat.{u} LiftQ.{u})).mapIso coefficientComparison).app X

/-- The same coefficient-unit comparison applies to the actual relative cokernel functor. -/
def nativeRelativeChainComparison (P : SSetPair.{u}) :
    (scalarFunctor.mapHomologicalComplex (.down ℕ)).obj (P.chainComplex qCoefficients) ≅
      P.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u}) :=
  relativeChainComparison P ≪≫
    ((SSetPair.chainComplexFunctor (ModuleCat.{u} LiftQ.{u})).mapIso
      coefficientComparison).app P

/-- Lift a prescribed rational tensor map, keeping exactly its existing values.
The adapter changes scalars and conjugates by native chain comparisons; it does not
define a replacement generator formula. A consumer supplies its actual prescribed map. -/
def tensorMapTransport (M N P : ModuleCat.{u} ℚ) (f : M ⊗[ℚ] N →ₗ[ℚ] P) :
    scalarFunctor.obj M ⊗[LiftQ.{u}] scalarFunctor.obj N →ₗ[LiftQ.{u}] scalarFunctor.obj P :=
  ((scalarFunctor.map (ModuleCat.ofHom f)).hom).comp
    (tensorScalarComparison M N).toLinearMap

/-- The exact native degreewise type required of the lifted-ring shuffle component. -/
def nativeShuffleComponent (X Y Z : SSet.{u}) (p q : ℕ)
    (sh : (X.chainComplex qCoefficients).X p ⊗[ℚ]
      (Y.chainComplex qCoefficients).X q →ₗ[ℚ]
      (Z.chainComplex qCoefficients).X (p + q)) :
    (X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X p ⊗[LiftQ.{u}]
      (Y.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X q →ₗ[LiftQ.{u}]
      (Z.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X (p + q) :=
  ((nativeChainComparison Z).hom.f (p + q)).hom.comp
    ((tensorMapTransport _ _ _ sh).comp
      (TensorProduct.map ((nativeChainComparison X).inv.f p).hom
        ((nativeChainComparison Y).inv.f q).hom))

/-- The generic adapter on singular chains has the native product-space target.
For the prescribed signed shuffle its map argument is the actual
`HolomorphicAnosov.SignedShuffle.shuffle` declaration, not independently selected data. -/
def singularShuffleComponent (X Y : TopCat.{u}) (p q : ℕ)
    (sh : ((TopCat.toSSet.obj X).chainComplex qCoefficients).X p ⊗[ℚ]
      ((TopCat.toSSet.obj Y).chainComplex qCoefficients).X q →ₗ[ℚ]
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex qCoefficients).X (p + q)) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X p ⊗[LiftQ.{u}]
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X q →ₗ[LiftQ.{u}]
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
        (ModuleCat.of LiftQ.{u} LiftQ.{u})).X (p + q) :=
  nativeShuffleComponent _ _ _ p q sh

/-- Native tensor-total complexes now have the required universe-compatible monoidal carrier. -/
abbrev nativeTensorTotal (X Y : SSet.{u}) : ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ :=
  HomologicalComplex.tensorObj (X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    (Y.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u}))

/-- The literal original bidegree inclusion into that native tensor-total complex. -/
def nativeTensorEntry (X Y : SSet.{u}) (p q : ℕ) :
    ModuleCat.of LiftQ.{u}
      ((X.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X p ⊗[LiftQ.{u}]
        (Y.chainComplex (ModuleCat.of LiftQ.{u} LiftQ.{u})).X q) ⟶
      (nativeTensorTotal X Y).X (p + q) :=
  HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl


end HolomorphicAnosov.RationalScalarTransport
