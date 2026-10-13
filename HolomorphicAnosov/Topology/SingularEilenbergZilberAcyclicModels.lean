import HolomorphicAnosov.Algebra.Homology.ChainTensorCokernelComparison
import HolomorphicAnosov.Topology.Homology.SingularProductTensorComparison
import HolomorphicAnosov.Topology.Homology.ChainHomotopyCokernelDescent
import HolomorphicAnosov.Topology.Homology.NativeChainComparisonDifferential
import HolomorphicAnosov.Topology.Homology.RationalScalarTransportNaturality
import HolomorphicAnosov.Topology.Homology.NativeShuffleComponentDifferential
import HolomorphicAnosov.Topology.Homology.SingularConvexConeTensorContraction
import HolomorphicAnosov.Topology.SingularAcyclicModelsRemainingUniquenessCases
import HolomorphicAnosov.Topology.Homology.SignedShuffleChainMap
import HolomorphicAnosov.Topology.Homology.RationalScalarTransport
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# The prescribed singular Eilenberg–Zilber equivalence and natural uniqueness

Sources: Bredon, *Topology and Geometry* (1993), IV15.5 pp.219–220,
IV16.1 pp.221–222, VI1.1–1.4 pp.316–318; Barr, *Acyclic Models*,
Chapter5 §5 Proposition5.5 p.116; Hatcher §3.B pp.277–278;
Eilenberg–Mac Lane, *On the Groups H(Π,n), I* (1953), §5 Theorem5.2 pp.66–67.
DAG node: `topo.singular_eilenberg_zilber_acyclic_models_g7`.

The singular and tensor-total functors are actual Mathlib chain complexes.
The specified shuffle is pinned to the unique imported signed staircase data.
Maps and natural homotopies are outputs. Relative complexes are the actual
cokernels of subspace chain inclusions, and their comparison is pinned to the
quotient projections. The rational field is moved only along its canonical universe-lift
ring equivalence, preserving its additive data, literal coefficient1 and pure tensors.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial TensorProduct

noncomputable section

universe u

namespace HolomorphicAnosov.SingularEilenbergZilber

open HolomorphicAnosov.RationalScalarTransport

/-- The actual unnormalized rational singular-chain functor after canonical scalar transport
along ULift.ringEquiv. The lifted rational field supports the native monoidal module category
in the arbitrary carrier universe. Its coefficient unit retains literal rational coefficient1.
Source: Bredon VI§1 pp.316–318; Hatcher §3.B pp.277–278. -/
abbrev chainFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} LiftQ.{u})).obj
    (ModuleCat.of LiftQ.{u} LiftQ.{u})

/-- The singular chains on the original product topology.
Source: Bredon VI Theorem1.2 pp.316–317. -/
abbrev productFunctor : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ :=
  tensor TopCat.{u} ⋙ chainFunctor

/-- The actual signed tensor total complex, whose degree-n summands are indexed
by p+q=n and whose pure-tensor differential is ∂a⊗b+(-1)^p a⊗∂b.
Source: Bredon VI Lemma1.1 p.316; Mathlib's down-ℕ tensor signs. -/
abbrev tensorFunctor : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ :=
  (chainFunctor.prod chainFunctor) ⋙ tensor (ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)

/-- The original subspace inclusion, retaining the induced topology.
Source: Bredon IV16.1 pp.221–222 and VI Corollary1.4 p.318. -/
def subspaceInclusion (X : TopCat.{u}) (B : Set X) : TopCat.of B ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The native degree-n total map, defined by coproduct descent from the published shuffle.
Source: Hatcher pp.277–278, Bredon IV16.1 pp.221–222 and VI§1 pp.316–318.
The summand formula is the existing signed shuffle, and no chain-equivalence data are input. -/
def shuffleDegree (X Y : TopCat.{u}) (n : ℕ) :
    (tensorFunctor.obj (X, Y)).X n ⟶ (productFunctor.obj (X, Y)).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦ by
    have hpq : p + q = n := h
    subst n
    exact ModuleCat.ofHom (singularShuffleComponent X Y p q (SignedShuffle.shuffle X Y p q)))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Coproduct descent of the prescribed signed shuffle commutes with the total differential.
Source: Eilenberg–Mac Lane §5 Theorem5.2 pp.66–67; Hatcher pp.277–278;
the shuffle-chain-map clause of `topo.singular_eilenberg_zilber_acyclic_models_g7`.

Complete natural-language proof: precompose both sides with every (p,q)-summand inclusion
in total degree i. The native tensor differential is the sum of its first boundary term
and its second boundary term multiplied by (-1)^p. The coproduct descent evaluates these
terms by exactly the published shuffle components. The component boundary identity in
`SignedShuffle.signedShuffle_chainMap` therefore gives equality on every pure tensor,
and tensor bilinearity gives equality on each summand. The native coproduct universal
property then gives equality of the degree-i maps. If a factor degree is zero, its
outgoing term is zero; if i,j do not satisfy the chain shape, both differentials are zero.
Changing scalars along the rational ring equivalence and the native chain comparisons
preserves these finite identities and their signs. This certifies already defined maps;
it supplies no unknown shuffle data and assumes no Eilenberg–Zilber equivalence. -/
theorem shuffleDegree_comm (X Y : TopCat.{u}) (i j : ℕ) :
    shuffleDegree X Y i ≫ (productFunctor.obj (X, Y)).d i j =
      (tensorFunctor.obj (X, Y)).d i j ≫ shuffleDegree X Y j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  swap
  · simp only [HomologicalComplex.shape _ _ _ hij, comp_zero, zero_comp]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = i at h
  subst i
  dsimp only [tensorFunctor, productFunctor, Functor.comp_obj]
  simp only [shuffleDegree, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  change _ = _ ≫ (HomologicalComplex.mapBifunctor _ _ _ _).d _ _ ≫ _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hj : j = p + q - 1 := by
    omega
  subst j
  cases p with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp)]
    cases q with
    | zero => simp at h
    | succ q =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 (i₂' := q) (by simp) _ (by simp)]
      simp only [zero_comp, zero_add, Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      dsimp [singularShuffleComponent, nativeShuffleComponent, tensorMapTransport]
      simp only [pow_zero, one_smul]
      have dh (Z : TopCat.{u}) (n m : ℕ) (c : SignedShuffle.Chain Z n) :
          ((chainFunctor.obj Z).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f n).hom c) =
          ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f m).hom
            ((((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom c) := by
        exact congrArg (fun k => k.hom c)
          ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.comm n m)
      have di (Z : TopCat.{u}) (n m : ℕ) (c : (chainFunctor.obj Z).X n) :
          ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f m).hom
            (((chainFunctor.obj Z).d n m).hom c) =
          (((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f n).hom c) := by
        exact (congrArg (fun k => k.hom c)
          ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.comm n m)).symm
      change ((chainFunctor.obj (TopCat.of (X × Y))).d (0 + (q + 1)) (0 + q)).hom
        (((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f (0 + (q + 1))).hom
          (SignedShuffle.shuffle X Y 0 (q + 1)
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f 0).hom a ⊗ₜ[ℚ]
             ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b))) = _
      rw [dh]
      change _ = ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f (0 + q)).hom
        (SignedShuffle.shuffle X Y 0 q
          (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f 0).hom a ⊗ₜ[ℚ]
           ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f q).hom
             (((chainFunctor.obj Y).d (q + 1) q).hom b)))
      rw [di]
      apply congrArg
      simpa [SignedShuffle.firstBoundaryTerm, SignedShuffle.secondBoundaryTerm,
        SignedShuffle.regrade, SignedShuffle.shuffle, SignedShuffle.boundary]
        using (SignedShuffle.signedShuffle_chainMap X Y).2.1 0 (q + 1)
          (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f 0).hom a)
          (((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b)
  | succ p =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (i₁' := p) (by simp) q _ (by simp)]
    cases q with
    | zero =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)]
      simp only [zero_comp, Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      dsimp [singularShuffleComponent, nativeShuffleComponent, tensorMapTransport]
      have dh (Z : TopCat.{u}) (n m : ℕ) (c : SignedShuffle.Chain Z n) :
          ((chainFunctor.obj Z).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f n).hom c) =
          ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f m).hom
            ((((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom c) := by
        exact congrArg (fun k => k.hom c) ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.comm n m)
      have di (Z : TopCat.{u}) (n m : ℕ) (c : (chainFunctor.obj Z).X n) :
          ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f m).hom (((chainFunctor.obj Z).d n m).hom c) =
          (((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f n).hom c) := by
        exact (congrArg (fun k => k.hom c) ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.comm n m)).symm
      change ((chainFunctor.obj (TopCat.of (X × Y))).d (p + 1) p).hom
        (((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f (p + 1)).hom
          (SignedShuffle.shuffle X Y (p + 1) 0
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a ⊗ₜ[ℚ]
             ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f 0).hom b))) = _
      rw [dh]
      change _ = (1 : ℤˣ) •
        ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f p).hom
          (SignedShuffle.shuffle X Y p 0
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f p).hom
              (((chainFunctor.obj X).d (p + 1) p).hom a) ⊗ₜ[ℚ]
             ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f 0).hom b)) + 0
      simp only [one_smul, add_zero]
      rw [di]
      apply congrArg
      simpa [SignedShuffle.firstBoundaryTerm, SignedShuffle.secondBoundaryTerm,
        SignedShuffle.regrade, SignedShuffle.shuffle, SignedShuffle.boundary] using
        (SignedShuffle.signedShuffle_chainMap X Y).2.1 (p + 1) 0
          (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a)
          (((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f 0).hom b)
    | succ q =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1) (i₂' := q) (by simp) _ (by simp)]
      simp only [Linear.units_smul_comp, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      dsimp [singularShuffleComponent, nativeShuffleComponent, tensorMapTransport]
      have dh (Z : TopCat.{u}) (n m : ℕ) (c : SignedShuffle.Chain Z n) :
          ((chainFunctor.obj Z).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f n).hom c) =
          ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f m).hom
            ((((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom c) := by
        exact nativeChainComparison_hom_differential _ n m c
      change ((chainFunctor.obj (TopCat.of (X × Y))).d
        ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom
        (((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f
          ((p + 1) + (q + 1))).hom
          (SignedShuffle.shuffle X Y (p + 1) (q + 1)
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a ⊗ₜ[ℚ]
             ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b))) = _
      rw [dh]
      have di (Z : TopCat.{u}) (n m : ℕ) (c : (chainFunctor.obj Z).X n) :
          ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f m).hom
            (((chainFunctor.obj Z).d n m).hom c) =
          (((TopCat.toSSet.obj Z).chainComplex qCoefficients).d n m).hom
            (((nativeChainComparison (TopCat.toSSet.obj Z)).inv.f n).hom c) := by
        exact (congrArg (fun k ↦ k.hom c)
          ((nativeChainComparison (TopCat.toSSet.obj Z)).inv.comm n m)).symm
      have hb := (SignedShuffle.signedShuffle_chainMap X Y).2.1 (p + 1) (q + 1)
        (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a)
        (((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b)
      rw [show (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex qCoefficients).d
          ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom =
        SignedShuffle.boundary (TopCat.of (X × Y)) ((p + 1) + (q + 1)) from rfl, hb]
      simp only [map_add]
      congr 1
      · simp only [SignedShuffle.firstBoundaryTerm, Nat.succ_ne_zero, dite_false]
        have aux (n : ℕ) (hn : p + (q + 1) = n) :
            ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f n).hom
              (SignedShuffle.regrade (TopCat.of (X × Y)) hn
                (SignedShuffle.shuffle X Y p (q + 1)
                  (SignedShuffle.boundary X (p + 1)
                    (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a)
                    ⊗ₜ[ℚ] ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b))) =
            (show (chainFunctor.obj X).X p ⊗ (chainFunctor.obj Y).X (q + 1) ⟶
                (chainFunctor.obj (TopCat.of (X × Y))).X n from by
              have hpq : p + (q + 1) = n := hn
              subst n
              exact ModuleCat.ofHom
                (singularShuffleComponent X Y p (q + 1) (SignedShuffle.shuffle X Y p (q + 1)))).hom
              ((((chainFunctor.obj X).d (p + 1) p).hom a) ⊗ₜ[LiftQ] b) := by
          subst n
          dsimp [SignedShuffle.regrade, singularShuffleComponent, nativeShuffleComponent,
            tensorMapTransport]
          change _ = ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f
            (p + (q + 1))).hom
            (SignedShuffle.shuffle X Y p (q + 1)
              (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f p).hom
                (((chainFunctor.obj X).d (p + 1) p).hom a) ⊗ₜ[ℚ]
                ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b))
          rw [di]
          rfl
        simp only [one_smul]
        convert! aux (p + 1 + q) (by omega) using 1
      · simp only [SignedShuffle.secondBoundaryTerm, Nat.succ_ne_zero, dite_false]
        dsimp [SignedShuffle.regrade]
        have hs (Z : TopCat.{u}) (n k : ℕ) (c : SignedShuffle.Chain Z n) :
            ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f n).hom
                ((-1 : ℚ)^k • c) =
              ((-1 : ℤˣ)^k) •
                ((nativeChainComparison (TopCat.toSSet.obj Z)).hom.f n).hom c := by
          induction k with
          | zero => simp
          | succ k ih =>
            simp only [pow_succ, mul_smul, neg_one_smul, Units.smul_def,
              Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at ih ⊢
            simpa only [neg_smul, one_smul, smul_neg, map_neg] using congrArg Neg.neg ih
        refine (hs (TopCat.of (X × Y)) (p + 1 + q) (p + 1)
          (SignedShuffle.shuffleBilinear X Y (p + 1) q
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a)
            (SignedShuffle.boundary Y (q + 1)
              (((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f (q + 1)).hom b)))).trans ?_
        congr 1
        change _ = ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f
          (p + 1 + q)).hom
          (SignedShuffle.shuffle X Y (p + 1) q
            (((nativeChainComparison (TopCat.toSSet.obj X)).inv.f (p + 1)).hom a ⊗ₜ[ℚ]
              ((nativeChainComparison (TopCat.toSSet.obj Y)).inv.f q).hom
                (((chainFunctor.obj Y).d (q + 1) q).hom b)))
        rw [di]
        rfl

/-- The actual prescribed total shuffle chain map, with only its commutation proof postponed.
Source: the signed singular product of Hatcher pp.277–278 and Bredon VI§1 pp.316–318. -/
def shuffleChainMap (X Y : TopCat.{u}) : tensorFunctor.obj (X, Y) ⟶ productFunctor.obj (X, Y) :=
  { f := shuffleDegree X Y
    comm' := fun i j _ ↦ shuffleDegree_comm X Y i j }

/-- The already constructed total shuffle is natural under the original continuous maps.
Source: Hatcher pp.277–278 and Bredon VI Theorem1.3 pp.317–318;
the natural-shuffle clause of `topo.singular_eilenberg_zilber_acyclic_models_g7`.

Complete natural-language proof: in each degree precompose the naturality square with
every tensor-total summand inclusion. The tensor functor applies the two original
postcomposition chain maps, while the product functor postcomposes by their product.
The native summand projection formula for shuffleDegree reduces the square to precisely
the naturality clause of the published signed shuffle on pure tensors. Tensor linear
extension and coproduct descent give equality in every degree, hence equality of chain
maps. Scalar restriction and the native chain comparisons are natural, so the same
square holds after the rational universe lift. No naturality of a replacement map is assumed. -/
theorem shuffleChainMap_naturality {xy xy' : TopCat.{u} × TopCat.{u}} (f : xy ⟶ xy') :
    tensorFunctor.map f ≫ shuffleChainMap xy'.1 xy'.2 =
      shuffleChainMap xy.1 xy.2 ≫ productFunctor.map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq' : p + q = n := hpq
  subst n
  change HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl ≫
      ((HomologicalComplex.tensorHom (chainFunctor.map f.1) (chainFunctor.map f.2)).f
        (p + q) ≫ shuffleDegree xy'.1 xy'.2 (p + q)) =
    HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl ≫
      (shuffleDegree xy.1 xy.2 (p + q) ≫ (productFunctor.map f).f (p + q))
  unfold shuffleDegree
  simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  exact (nativeShuffleComponent_naturality
    (TopCat.toSSet.map f.1) (TopCat.toSSet.map f.2)
    (TopCat.toSSet.map ((tensor TopCat).map f)) p q
    (SignedShuffle.shuffle xy.1 xy.2 p q) (SignedShuffle.shuffle xy'.1 xy'.2 p q)
    (SignedShuffle.shuffle_naturality xy.1 xy.2 xy'.1 xy'.2 f.1.hom f.2.hom p q)
    a b).symm

/-- The prescribed natural total shuffle, constructed from its degreewise native coproduct map.
Source: Hatcher pp.277–278, Bredon VI§1 pp.316–318. -/
def shuffle : tensorFunctor ⟶ productFunctor :=
  { app := fun xy ↦ shuffleChainMap xy.1 xy.2
    naturality := fun _ _ f ↦ shuffleChainMap_naturality f }

/-- The literal coefficient-one point chain in the native lifted-rational complex.
Source: Bredon VI§1 pp.316–317, degree-zero point normalization. Its singular simplex is
that of the published signed-shuffle provider and its coefficient is exactly ULift.up 1. -/
def pointChain (X : TopCat.{u}) (x : X) : (chainFunctor.obj X).X 0 :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of LiftQ.{u} LiftQ.{u})
    (SignedShuffle.pointSimplex X x)).hom (ULift.up 1)


/-- The prescribed total shuffle evaluates on each original pure-tensor summand
by its published component. Source: Hatcher §3.B pp.277–278. This is the
coproduct-descent equation defining `shuffleDegree`. -/
theorem shuffle_pure_tensor (X Y : TopCat.{u}) (p q : ℕ)
    (a : (chainFunctor.obj X).X p) (b : (chainFunctor.obj Y).X q) :
    (shuffle.app (X, Y)).f (p + q)
      ((HomologicalComplex.ιTensorObj (chainFunctor.obj X) (chainFunctor.obj Y)
        p q (p + q) rfl) (a ⊗ₜ[LiftQ.{u}] b)) =
      singularShuffleComponent X Y p q (SignedShuffle.shuffle X Y p q)
        (a ⊗ₜ[LiftQ.{u}] b) := by
  change (HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl ≫
    shuffleDegree X Y (p + q)) (a ⊗ₜ[LiftQ.{u}] b) = _
  simp only [shuffleDegree, HomologicalComplex.ι_mapBifunctorDesc]
  rfl

/-- The native scalar comparison preserves each actual simplex coefficient.
Source: the coproduct comparison in Mathlib MapHomologicalComplex; the
coefficient comparison is the identity on the lifted rational carrier. -/
theorem nativeChainComparison_generator (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) (r : LiftQ.{u}) :
    ((nativeChainComparison X).hom.f n).hom
      ((X.ιChainComplex (R := qCoefficients) x).hom r) =
    (X.ιChainComplex (R := ModuleCat.of LiftQ.{u} LiftQ.{u}) x).hom r := by
  have h : scalarFunctor.map (X.ιChainComplex (R := qCoefficients) x) ≫
      (nativeChainComparison X).hom.f n =
      coefficientComparison.hom ≫ X.ιChainComplex x := by
    dsimp only [nativeChainComparison, Iso.trans_hom, HomologicalComplex.comp_f]
    rw [← Category.assoc]
    change (scalarFunctor.map (X.ιChainComplex x) ≫
      ((SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients).hom.app X).f n) ≫ _ = _
    rw [SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f]
    simp [SSet.ιChainComplex, SSet.chainComplexFunctor]
  exact congrArg (fun f ↦ f.hom r) h

/-- The inverse scalar comparison preserves the same simplex coefficients,
by applying its inverse identity to the forward generator equation. -/
theorem nativeChainComparison_inv_generator (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) (r : LiftQ.{u}) :
    ((nativeChainComparison X).inv.f n).hom
      ((X.ιChainComplex (R := ModuleCat.of LiftQ.{u} LiftQ.{u}) x).hom r) =
    (X.ιChainComplex (R := qCoefficients) x).hom r := by
  rw [← nativeChainComparison_generator X x r]
  exact congrArg (fun f ↦ (f.f n).hom ((X.ιChainComplex (R := qCoefficients) x).hom r))
    (nativeChainComparison X).hom_inv_id

/-- The total shuffle sends a tensor of point chains to the point-pair chain.
Source: Hatcher §3.B pp.277–278; the published signed-shuffle point law,
transported by the actual scalar comparison and total-summand inclusion. -/
theorem shuffle_point_chain (X Y : TopCat.{u}) (x : X) (y : Y) :
    (shuffle.app (X, Y)).f 0
      ((HomologicalComplex.ιTensorObj (chainFunctor.obj X) (chainFunctor.obj Y) 0 0 0 rfl)
        (pointChain X x ⊗ₜ[LiftQ.{u}] pointChain Y y)) =
      pointChain (TopCat.of (X × Y)) (x, y) := by
  refine (shuffle_pure_tensor X Y 0 0 (pointChain X x) (pointChain Y y)).trans ?_
  change nativeShuffleComponent _ _ _ 0 0 _ _ = _
  erw [nativeShuffleComponent_tmul]
  simp only [pointChain]
  erw [nativeChainComparison_inv_generator, nativeChainComparison_inv_generator]
  change ((nativeChainComparison (TopCat.toSSet.obj (TopCat.of (X × Y)))).hom.f 0).hom
    (SignedShuffle.shuffle X Y 0 0
      (SignedShuffle.generator X (SignedShuffle.pointSimplex X x) ⊗ₜ[ℚ]
        SignedShuffle.generator Y (SignedShuffle.pointSimplex Y y))) = _
  erw [SignedShuffle.shuffle_point_point]
  exact nativeChainComparison_generator _ _ _


/-- Apply the native cokernel descent theorem to every subspace-inclusion naturality square.
Source: Bredon VI1.4 p.318; this is the functorial specialization of
`chain_homotopy_cokernel_descent`, with the same quotient projections. -/
theorem naturalHomotopy_relative
    (S U : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
    (Φ Ψ : S ⟶ U) (H : ∀ xy, _root_.Homotopy (Φ.app xy) (Ψ.app xy))
    (hH : ∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
      (S.map f).f i ≫ (H xy').hom i j = (H xy).hom i j ≫ (U.map f).f j)
    (X Y : TopCat.{u}) (B : Set X) :
    let inclusion : (TopCat.of B, Y) ⟶ (X, Y) := (subspaceInclusion X B, 𝟙 Y)
    let SR := cokernel (S.map inclusion)
    let UR := cokernel (U.map inclusion)
    let qS := cokernel.π (S.map inclusion)
    let qU := cokernel.π (U.map inclusion)
    ∃ (ΦR ΨR : SR ⟶ UR) (HR : _root_.Homotopy ΦR ΨR),
      qS ≫ ΦR = Φ.app (X, Y) ≫ qU ∧
      qS ≫ ΨR = Ψ.app (X, Y) ≫ qU ∧
      ∀ i j, (H (X, Y)).hom i j ≫ qU.f j = qS.f i ≫ HR.hom i j := by
  dsimp only
  exact chain_homotopy_cokernel_descent _ _ _ _ _ _
    (Φ.naturality _) (Ψ.naturality _) _ _ (hH _ _ _)

/-- Express the three published acyclic-model uniqueness cases using literal
coefficient-one point chains. Source: Barr Chapter5 Proposition5.5 p.116 and
`singular_acyclic_models_remaining_uniqueness_cases`. Linear maps from the
coefficient ring agree exactly when they agree at one; the tensor unit sends
one to the pure tensor of ones. No additional model-filling assertion is used. -/
theorem three_normalized_natural_homotopies :
    let A := productFunctor
    let T := tensorFunctor
    let point : TopCat.{u} := TopCat.of PUnit
    let pp := (point, point)
    let g := pointChain point PUnit.unit
    let gA := pointChain (TopCat.of (point × point)) (PUnit.unit, PUnit.unit)
    let gT := (HomologicalComplex.ιTensorObj (chainFunctor.obj point)
      (chainFunctor.obj point) 0 0 0 rfl) (g ⊗ₜ[LiftQ.{u}] g)
    let NH := fun
      (S U : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
      (Φ Ψ : S ⟶ U) ↦
        ∃ H : ∀ xy, _root_.Homotopy (Φ.app xy) (Ψ.app xy),
          ∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
            (S.map f).f i ≫ (H xy').hom i j = (H xy).hom i j ≫ (U.map f).f j
    (∀ (Φ Ψ : A ⟶ A),
      (Φ.app pp).f 0 gA = gA → (Ψ.app pp).f 0 gA = gA → NH A A Φ Ψ) ∧
    (∀ (Φ Ψ : T ⟶ T),
      (Φ.app pp).f 0 gT = gT → (Ψ.app pp).f 0 gT = gT → NH T T Φ Ψ) ∧
    (∀ (Φ Ψ : T ⟶ A),
      (Φ.app pp).f 0 gT = gA → (Ψ.app pp).f 0 gT = gA → NH T A Φ Ψ) := by
  dsimp only
  obtain ⟨hAA, hTT, hTA⟩ := HolomorphicAnosov.Topology.singular_acyclic_models_remaining_uniqueness_cases.{u}
  refine ⟨?_, ?_, ?_⟩
  · intro Φ Ψ hΦ hΨ
    obtain ⟨H, hn, _⟩ := hAA Φ Ψ (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      exact hΦ) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      exact hΨ)
    exact ⟨H, hn⟩
  · intro Φ Ψ hΦ hΨ
    obtain ⟨H, hn, _⟩ := hTT Φ Ψ (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_inv_leftUnitor, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
      exact hΦ) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_inv_leftUnitor, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
      exact hΨ)
    exact ⟨H, hn⟩
  · intro Φ Ψ hΦ hΨ
    obtain ⟨H, hn, _⟩ := hTA Φ Ψ (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_inv_leftUnitor, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
      exact hΦ) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_inv_leftUnitor, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
      exact hΨ)
    exact ⟨H, hn⟩

/-- Natural inverse homotopies descend to the two actual cokernel maps,
retaining their component projection equations. Source: Bredon VI1.4 p.318.
Define both maps by cokernel descent, apply `chain_homotopy_cokernel_descent`
to each composite and identity, and cancel the epimorphic quotient maps to
identify those descents with the composites of the descended maps. -/
theorem natural_equivalence_cokernel_descent
    (S U : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
    (f : S ⟶ U) (g : U ⟶ S)
    (HS : ∀ xy, _root_.Homotopy ((f ≫ g).app xy) (𝟙 (S.obj xy)))
    (HU : ∀ xy, _root_.Homotopy ((g ≫ f).app xy) (𝟙 (U.obj xy)))
    (hS : ∀ xy xy' (a : xy ⟶ xy') (i j : ℕ),
      (S.map a).f i ≫ (HS xy').hom i j = (HS xy).hom i j ≫ (S.map a).f j)
    (hU : ∀ xy xy' (a : xy ⟶ xy') (i j : ℕ),
      (U.map a).f i ≫ (HU xy').hom i j = (HU xy).hom i j ≫ (U.map a).f j)
    {xy xy' : TopCat.{u} × TopCat.{u}} (a : xy ⟶ xy') :
    ∃ (fR : cokernel (S.map a) ⟶ cokernel (U.map a))
      (gR : cokernel (U.map a) ⟶ cokernel (S.map a))
      (HSR : _root_.Homotopy (fR ≫ gR) (𝟙 _))
      (HUR : _root_.Homotopy (gR ≫ fR) (𝟙 _)),
      cokernel.π (S.map a) ≫ fR = f.app xy' ≫ cokernel.π (U.map a) ∧
      cokernel.π (U.map a) ≫ gR = g.app xy' ≫ cokernel.π (S.map a) ∧
      (∀ i j, (HS xy').hom i j ≫ (cokernel.π (S.map a)).f j =
        (cokernel.π (S.map a)).f i ≫ HSR.hom i j) ∧
      (∀ i j, (HU xy').hom i j ≫ (cokernel.π (U.map a)).f j =
        (cokernel.π (U.map a)).f i ≫ HUR.hom i j) := by
  let fR := cokernel.desc (S.map a) (f.app xy' ≫ cokernel.π (U.map a)) (by
    rw [← Category.assoc, f.naturality, Category.assoc, cokernel.condition, comp_zero])
  let gR := cokernel.desc (U.map a) (g.app xy' ≫ cokernel.π (S.map a)) (by
    rw [← Category.assoc, g.naturality, Category.assoc, cokernel.condition, comp_zero])
  have hf : cokernel.π (S.map a) ≫ fR = f.app xy' ≫ cokernel.π (U.map a) :=
    cokernel.π_desc _ _ _
  have hg : cokernel.π (U.map a) ≫ gR = g.app xy' ≫ cokernel.π (S.map a) :=
    cokernel.π_desc _ _ _
  obtain ⟨uS, vS, HSR, huS, hvS, hpS⟩ := chain_homotopy_cokernel_descent
    (S.map a) (S.map a) ((f ≫ g).app xy) (𝟙 _) ((f ≫ g).app xy') (𝟙 _)
    ((f ≫ g).naturality a) (by simp) (HS xy) (HS xy') (hS xy xy' a)
  have huS' : uS = fR ≫ gR := by
    apply (cancel_epi (cokernel.π (S.map a))).mp
    rw [huS, ← Category.assoc, hf, Category.assoc, hg]
    rfl
  have hvS' : vS = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (S.map a))).mp
    simpa using hvS
  subst uS
  subst vS
  obtain ⟨uU, vU, HUR, huU, hvU, hpU⟩ := chain_homotopy_cokernel_descent
    (U.map a) (U.map a) ((g ≫ f).app xy) (𝟙 _) ((g ≫ f).app xy') (𝟙 _)
    ((g ≫ f).naturality a) (by simp) (HU xy) (HU xy') (hU xy xy' a)
  have huU' : uU = gR ≫ fR := by
    apply (cancel_epi (cokernel.π (U.map a))).mp
    rw [huU, ← Category.assoc, hg, Category.assoc, hf]
    rfl
  have hvU' : vU = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (U.map a))).mp
    simpa using hvU
  subst uU
  subst vU
  exact ⟨fR, gR, HSR, HUR, hf, hg, hpS, hpU⟩


set_option maxHeartbeats 800000 in
/-- **The exact rational singular signed-shuffle Eilenberg–Zilber theorem.**

Sources: Bredon IV15.5 pp.219–220, IV16.1 pp.221–222, VI Lemma1.1 p.316,
Theorem1.2 pp.316–317, Theorem1.3 pp.317–318 and Corollary1.4 p.318;
Barr Chapter5 §5 Proposition5.5 p.116, with the free-model/exact-Hom
hypotheses verified in the named uniqueness dependency; Hatcher pp.277–278
for the specified monotone-grid sum; Eilenberg–Mac Lane §2–§3 pp.56–60,
§5 pp.63–67, especially Theorem5.2 pp.66–67 for its unnormalized boundary law.

Natural statement: for arbitrary spaces X,Y, the signed monotone-grid shuffle
from the rational tensor-total singular chains to singular chains on X×Y is
a natural chain homotopy equivalence. There is a natural reverse chain map θ
and natural homotopies θsh≃id and shθ≃id. Any two natural chain maps between
either source/target functor, normalized on the canonical point generator at
the pair of singleton spaces, are naturally chain homotopic. The maps and
homotopies restrict under every subspace inclusion and descend to the actual
one-relative-factor quotients. No CW, finite-type, separation, nonemptiness,
or contractibility condition on the arbitrary spaces is assumed.

The natural shuffle is constructed before this statement by native coproduct descent of
the imported `SignedShuffle.shuffle`, followed only by the canonical scalar comparison.
The first equation fixes every summand on all pure tensors and its original inclusion.
These generate the actual tensor-total module, so an arbitrary equivalent
replacement shuffle cannot satisfy that specification. The four uniqueness
clauses quantify over actual natural transformations of actual chain functors.
`naturalHomotopy` expands to Mathlib Homotopy data with its all-degree naturality
equation. The relative clause constructs cokernel maps and Homotopy data, fixes
their values under quotient projections, and supplies the canonical tensor
quotient identification. In particular it does not assume relative descent.

Complete natural-language proof relative to the named source prerequisites:

1. On each standard convex model Δʳ×Δˢ, the source cone contraction satisfies
∂D+D∂=id−ε. On Tot(C(Δʳ)⊗C(Δˢ)), the signed tensor contraction satisfies
∂E+E∂=id−ε⊗ε. Thus each positive-degree cycle is filled by D or E, and
an augmentation-zero degree-zero chain is filled by the same formula.
Only these contractible models use cones; no contraction of arbitrary X,Y
is assumed. The signed-shuffle provider's precise finite staircase formula,
unnormalized boundary identity, naturality, and point initialization make
the prescribed degreewise coproduct extension sh a natural chain map.

2. Construct θ by Bredon's written VI1.2 induction. In degree0 send [(x,y)]
to [x]⊗[y]. In degree n>0 use the diagonal simplex dₙ:Δⁿ→Δⁿ×Δⁿ.
The already-defined lower map sends ∂dₙ to a cycle, by ∂²=0 and lower
chain-map commutation. For n=1 its coefficient sum is zero. Fill this model
cycle using E and call the chosen chain cₙ. For σ:Δⁿ→X×Y with coordinate
maps f,g define θₙσ=(f♯⊗g♯)cₙ and extend on the actual free rational basis.
Every σ=(f×g)dₙ, so postcomposition gives naturality. The model boundary
identity and lower naturality give ∂θₙσ=θₙ₋₁∂σ in every degree.

3. Point normalization forces equality in degree0 on all spaces: each
point-pair basis generator is pushed forward from the singleton pair by
the two point inclusions. Thus normalized natural maps agree on those
generators and on all degree-zero chains, including the empty spaces.
For the fully written product-source→tensor-output uniqueness case, start
H₀=0. If H satisfies ∂H+H∂=Φ−Ψ below n>0, evaluate
z=(Φ−Ψ−H∂)(dₙ) on the diagonal model. Its boundary is zero because the
lower homotopy identity cancels the two chain-map terms and ∂²=0.
Fill z by E, and extend the filling through the coordinate maps of each
singular simplex. The boundary is exactly Φ−Ψ−H∂; postcomposition proves
the all-degree naturality of this actual Homotopy.

4. The remaining three source/target choices are the named Barr comparison
provider. Each product-source degree is one free model-representable module
at (Δⁿ,Δⁿ); each tensor-source degree is the finite direct sum of free
model-representable modules at (Δᵖ,Δᑫ), p+q=n. Evaluation at the identity
generator identifies natural maps out of each summand with target chains
on that model, with inverse obtained by pushforward and free linear extension.
Cone/tensor model contractions make these augmented Hom complexes exact.
Barr's induction fills the residual natural transformation Φₙ−Ψₙ−Hₙ₋₁∂
on each model and extends it by that inverse. This gives natural Homotopy
data in all three cases. Together with step3 it gives all four uniqueness
clauses. Apply tensor-endomorphism uniqueness to sh followed by θ and the
identity, and product-endomorphism uniqueness to θ followed by sh and the
identity. Their point normalizations agree, so these are the required two
natural inverse homotopies for the specified sh.

5. For every inclusion B↪X, naturality of sh, θ, and each Homotopy sends
the image of the corresponding B-subcomplex into the corresponding target
image. Singular inclusion is injective on the actual free generators, so
these images are precisely the subspace-supported chain modules. Descend
the maps and degree-one homotopy components through the native cokernels.
Their chain-map and homotopy identities follow after the quotient projection;
the displayed projection equations record these very descents. The tensor
quotient is canonically Tot((C(X)/C(B))⊗C(Y)): free simplex bases identify
the first-factor quotient with the complementary generators, and tensor
and degreewise coproduct universal properties identify its pure tensors.
The final quotient-map equation fixes that canonical comparison. No excision
or openness is used. Empty X or Y gives zero complexes, B=∅ gives the
absolute quotients, and B=X gives zero relative complexes; every case remains
in the same native statements. The same descent is explicitly required of every uniqueness
homotopy, with its two induced maps and their quotient-projection equations, so all four
comparison cases retain these relative laws. Canonical restriction of scalars along
ULift.ringEquiv and the natural absolute-chain and tensor comparisons preserve coefficient1,
the actual shuffle, all differential signs and all projection identities. Thus the native
lifted-rational carriers state these same rational constructions for every universe u.
-/
theorem singular_eilenberg_zilber_acyclic_models :
    let C := chainFunctor
    let A := productFunctor
    let T := tensorFunctor
    let point : TopCat.{u} := TopCat.of PUnit
    let pp := (point, point)
    let g := pointChain point PUnit.unit
    let gA := pointChain (TopCat.of (point × point)) (PUnit.unit, PUnit.unit)
    let gT := (HomologicalComplex.ιTensorObj (C.obj point) (C.obj point) 0 0 0 rfl)
      (g ⊗ₜ[LiftQ.{u}] g)
    let sh : T ⟶ A := shuffle
    let naturalHomotopy := fun
      (S U : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
      (Φ Ψ : S ⟶ U) ↦
        ∃ H : ∀ xy, _root_.Homotopy (Φ.app xy) (Ψ.app xy),
          (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
            (S.map f).f i ≫ (H xy').hom i j = (H xy).hom i j ≫ (U.map f).f j) ∧
          (∀ (X Y : TopCat.{u}) (B : Set X),
            let inclusion : (TopCat.of B, Y) ⟶ (X, Y) := (subspaceInclusion X B, 𝟙 Y)
            let SR := cokernel (S.map inclusion)
            let UR := cokernel (U.map inclusion)
            let qS := cokernel.π (S.map inclusion)
            let qU := cokernel.π (U.map inclusion)
            ∃ (ΦR ΨR : SR ⟶ UR) (HR : _root_.Homotopy ΦR ΨR),
              qS ≫ ΦR = Φ.app (X, Y) ≫ qU ∧
              qS ≫ ΨR = Ψ.app (X, Y) ≫ qU ∧
              ∀ i j, (H (X, Y)).hom i j ≫ qU.f j = qS.f i ≫ HR.hom i j)
    ∃ (θ : A ⟶ T)
      (HT : ∀ xy, _root_.Homotopy ((sh ≫ θ).app xy) (𝟙 (T.obj xy)))
      (HA : ∀ xy, _root_.Homotopy ((θ ≫ sh).app xy) (𝟙 (A.obj xy))),
      (∀ (X Y : TopCat.{u}) (p q : ℕ) (a : (C.obj X).X p)
        (b : (C.obj Y).X q),
        (sh.app (X, Y)).f (p + q)
          ((HomologicalComplex.ιTensorObj (C.obj X) (C.obj Y) p q (p + q) rfl)
            (a ⊗ₜ[LiftQ.{u}] b)) = singularShuffleComponent X Y p q (SignedShuffle.shuffle X Y p q)
              (a ⊗ₜ[LiftQ.{u}] b)) ∧
      (θ.app pp).f 0 gA = gT ∧
      (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
        (T.map f).f i ≫ (HT xy').hom i j = (HT xy).hom i j ≫ (T.map f).f j) ∧
      (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
        (A.map f).f i ≫ (HA xy').hom i j = (HA xy).hom i j ≫ (A.map f).f j) ∧
      (∀ (Φ Ψ : A ⟶ A),
        (Φ.app pp).f 0 gA = gA → (Ψ.app pp).f 0 gA = gA → naturalHomotopy A A Φ Ψ) ∧
      (∀ (Φ Ψ : T ⟶ T),
        (Φ.app pp).f 0 gT = gT → (Ψ.app pp).f 0 gT = gT → naturalHomotopy T T Φ Ψ) ∧
      (∀ (Φ Ψ : T ⟶ A),
        (Φ.app pp).f 0 gT = gA → (Ψ.app pp).f 0 gT = gA → naturalHomotopy T A Φ Ψ) ∧
      (∀ (Φ Ψ : A ⟶ T),
        (Φ.app pp).f 0 gA = gT → (Ψ.app pp).f 0 gA = gT → naturalHomotopy A T Φ Ψ) ∧
      (∀ (X Y : TopCat.{u}) (B : Set X),
        let i := subspaceInclusion X B
        let pairInclusion : (TopCat.of B, Y) ⟶ (X, Y) := (i, 𝟙 Y)
        let AR := cokernel (A.map pairInclusion)
        let TR := cokernel (T.map pairInclusion)
        let qA := cokernel.π (A.map pairInclusion)
        let qT := cokernel.π (T.map pairInclusion)
        ∃ (shR : TR ⟶ AR) (θR : AR ⟶ TR)
          (HTR : _root_.Homotopy (shR ≫ θR) (𝟙 TR))
          (HAR : _root_.Homotopy (θR ≫ shR) (𝟙 AR)),
          qT ≫ shR = sh.app (X, Y) ≫ qA ∧
          qA ≫ θR = θ.app (X, Y) ≫ qT ∧
          (∀ i j, (HT (X, Y)).hom i j ≫ qT.f j = qT.f i ≫ HTR.hom i j) ∧
          (∀ i j, (HA (X, Y)).hom i j ≫ qA.f j = qA.f i ≫ HAR.hom i j) ∧
          ∃ e : TR ≅ HomologicalComplex.tensorObj (cokernel (C.map i)) (C.obj Y),
            qT ≫ e.hom =
              HomologicalComplex.tensorHom (cokernel.π (C.map i)) (𝟙 (C.obj Y))) := by
    let C := chainFunctor
    let A := productFunctor
    let T := tensorFunctor
    let point : TopCat.{u} := TopCat.of PUnit
    let pp := (point, point)
    let g := pointChain point PUnit.unit
    let gA := pointChain (TopCat.of (point × point)) (PUnit.unit, PUnit.unit)
    let gT := (HomologicalComplex.ιTensorObj (C.obj point) (C.obj point) 0 0 0 rfl)
      (g ⊗ₜ[LiftQ.{u}] g)
    let sh : T ⟶ A := shuffle
    let naturalHomotopy := fun
      (S U : TopCat.{u} × TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} LiftQ.{u}) ℕ)
      (Φ Ψ : S ⟶ U) ↦
        ∃ H : ∀ xy, _root_.Homotopy (Φ.app xy) (Ψ.app xy),
          (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
            (S.map f).f i ≫ (H xy').hom i j = (H xy).hom i j ≫ (U.map f).f j) ∧
          (∀ (X Y : TopCat.{u}) (B : Set X),
            let inclusion : (TopCat.of B, Y) ⟶ (X, Y) := (subspaceInclusion X B, 𝟙 Y)
            let SR := cokernel (S.map inclusion)
            let UR := cokernel (U.map inclusion)
            let qS := cokernel.π (S.map inclusion)
            let qU := cokernel.π (U.map inclusion)
            ∃ (ΦR ΨR : SR ⟶ UR) (HR : _root_.Homotopy ΦR ΨR),
              qS ≫ ΦR = Φ.app (X, Y) ≫ qU ∧
              qS ≫ ΨR = Ψ.app (X, Y) ≫ qU ∧
              ∀ i j, (H (X, Y)).hom i j ≫ qU.f j = qS.f i ≫ HR.hom i j)
    change ∃ (θ : A ⟶ T)
      (HT : ∀ xy, _root_.Homotopy ((sh ≫ θ).app xy) (𝟙 (T.obj xy)))
      (HA : ∀ xy, _root_.Homotopy ((θ ≫ sh).app xy) (𝟙 (A.obj xy))),
      (∀ (X Y : TopCat.{u}) (p q : ℕ) (a : (C.obj X).X p)
        (b : (C.obj Y).X q),
        (sh.app (X, Y)).f (p + q)
          ((HomologicalComplex.ιTensorObj (C.obj X) (C.obj Y) p q (p + q) rfl)
            (a ⊗ₜ[LiftQ.{u}] b)) = singularShuffleComponent X Y p q (SignedShuffle.shuffle X Y p q)
              (a ⊗ₜ[LiftQ.{u}] b)) ∧
      (θ.app pp).f 0 gA = gT ∧
      (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
        (T.map f).f i ≫ (HT xy').hom i j = (HT xy).hom i j ≫ (T.map f).f j) ∧
      (∀ xy xy' (f : xy ⟶ xy') (i j : ℕ),
        (A.map f).f i ≫ (HA xy').hom i j = (HA xy).hom i j ≫ (A.map f).f j) ∧
      (∀ (Φ Ψ : A ⟶ A),
        (Φ.app pp).f 0 gA = gA → (Ψ.app pp).f 0 gA = gA → naturalHomotopy A A Φ Ψ) ∧
      (∀ (Φ Ψ : T ⟶ T),
        (Φ.app pp).f 0 gT = gT → (Ψ.app pp).f 0 gT = gT → naturalHomotopy T T Φ Ψ) ∧
      (∀ (Φ Ψ : T ⟶ A),
        (Φ.app pp).f 0 gT = gA → (Ψ.app pp).f 0 gT = gA → naturalHomotopy T A Φ Ψ) ∧
      (∀ (Φ Ψ : A ⟶ T),
        (Φ.app pp).f 0 gA = gT → (Ψ.app pp).f 0 gA = gT → naturalHomotopy A T Φ Ψ) ∧
      (∀ (X Y : TopCat.{u}) (B : Set X),
        let i := subspaceInclusion X B
        let pairInclusion : (TopCat.of B, Y) ⟶ (X, Y) := (i, 𝟙 Y)
        let AR := cokernel (A.map pairInclusion)
        let TR := cokernel (T.map pairInclusion)
        let qA := cokernel.π (A.map pairInclusion)
        let qT := cokernel.π (T.map pairInclusion)
        ∃ (shR : TR ⟶ AR) (θR : AR ⟶ TR)
          (HTR : _root_.Homotopy (shR ≫ θR) (𝟙 TR))
          (HAR : _root_.Homotopy (θR ≫ shR) (𝟙 AR)),
          qT ≫ shR = sh.app (X, Y) ≫ qA ∧
          qA ≫ θR = θ.app (X, Y) ≫ qT ∧
          (∀ i j, (HT (X, Y)).hom i j ≫ qT.f j = qT.f i ≫ HTR.hom i j) ∧
          (∀ i j, (HA (X, Y)).hom i j ≫ qA.f j = qA.f i ≫ HAR.hom i j) ∧
          ∃ e : TR ≅ HomologicalComplex.tensorObj (cokernel (C.map i)) (C.obj Y),
            qT ≫ e.hom =
              HomologicalComplex.tensorHom (cokernel.π (C.map i)) (𝟙 (C.obj Y)))
    obtain ⟨⟨θ, hθ⟩, hAT⟩ := HolomorphicAnosov.Topology.singular_product_tensor_comparison.{u}
    obtain ⟨hAA, hTT, hTA⟩ := three_normalized_natural_homotopies.{u}
    have hsh : (sh.app pp).f 0 gT = gA := shuffle_point_chain point point _ _
    obtain ⟨HT, hHT⟩ := hTT (sh ≫ θ) (𝟙 T) (by
      change (θ.app pp).f 0 ((sh.app pp).f 0 gT) = gT
      rw [hsh]
      exact hθ) (by rfl)
    obtain ⟨HA, hHA⟩ := hAA (θ ≫ sh) (𝟙 A) (by
      change (sh.app pp).f 0 ((θ.app pp).f 0 gA) = gA
      erw [hθ]
      exact hsh) (by rfl)
    refine ⟨θ, HT, HA, shuffle_pure_tensor, hθ, hHT, hHA, ?_, ?_, ?_, ?_, ?_⟩
    · intro Φ Ψ hΦ hΨ
      obtain ⟨H, hn⟩ := hAA Φ Ψ hΦ hΨ
      exact ⟨H, hn, fun X Y B ↦ naturalHomotopy_relative _ _ _ _ H hn X Y B⟩
    · intro Φ Ψ hΦ hΨ
      obtain ⟨H, hn⟩ := hTT Φ Ψ hΦ hΨ
      exact ⟨H, hn, fun X Y B ↦ naturalHomotopy_relative _ _ _ _ H hn X Y B⟩
    · intro Φ Ψ hΦ hΨ
      obtain ⟨H, hn⟩ := hTA Φ Ψ hΦ hΨ
      exact ⟨H, hn, fun X Y B ↦ naturalHomotopy_relative _ _ _ _ H hn X Y B⟩
    · intro Φ Ψ hΦ hΨ
      obtain ⟨H, hn, _⟩ := hAT Φ Ψ hΦ hΨ
      exact ⟨H, hn, fun X Y B ↦ naturalHomotopy_relative _ _ _ _ H hn X Y B⟩
    · intro X Y B
      dsimp only
      obtain ⟨shR, θR, HTR, HAR, hshR, hθR, hHTR, hHAR⟩ :=
        natural_equivalence_cokernel_descent T A sh θ HT HA hHT hHA
          (xy := (TopCat.of B, Y)) (xy' := (X, Y)) (subspaceInclusion X B, 𝟙 Y)
      refine ⟨shR, θR, HTR, HAR, hshR, hθR, hHTR, hHAR, ?_⟩
      have hmap : T.map ((subspaceInclusion X B, 𝟙 Y) : (TopCat.of B, Y) ⟶ (X, Y)) =
          HomologicalComplex.tensorHom (C.map (subspaceInclusion X B)) (𝟙 (C.obj Y)) := by
        change HomologicalComplex.tensorHom (C.map (subspaceInclusion X B))
          (C.map (𝟙 Y)) = _
        rw [CategoryTheory.Functor.map_id]
      rw [hmap]
      exact chain_tensor_cokernel_comparison (C.map (subspaceInclusion X B)) (C.obj Y)

end HolomorphicAnosov.SingularEilenbergZilber




