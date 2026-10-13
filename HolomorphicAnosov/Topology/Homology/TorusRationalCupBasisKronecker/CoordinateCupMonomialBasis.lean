import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AbsoluteCupData
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditiveCircleNormalizedBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditiveCircleProfile
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditiveCircleUnitBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoop
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.BasisFromSuccessorSubsets
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleCrossProductBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleCrossProductBasisSuccessor
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateCupMonomialBasisZero
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateProjection
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EmptySubsetIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.MonomialPullback
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.PullbackOneCochain
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackComp
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackHomeomorph
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupAssocUnit
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorSubsetMonomialInl
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorSubsetMonomialInr
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.TorusSplitHomeomorph
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.ZeroCircleTensorIndex
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual finite-CW Künneth induction constructs the increasing coordinate cup basis.

Source: Hatcher, *Algebraic Topology*, Theorem 3.15 and Example 3.16, pp.216--218,
with cup representatives from pp.206--212 and the native finite coordinate CW structure.
DAG node: `topo.torus_public_coordinate_cup_monomial_basis_g17`.

The inputs are the actual native cocycle/cycle carriers, literal positive-chain
normalization, universal cup representative formula and the constant-one representative.
No cohomology basis, rank, exterior algebra or Künneth isomorphism is an input.
The source theorem supplies those consequences; the guards only pin which original
operation and which positive generator are being used.

Complete natural-language proof:

1. The source circle cocycle transported through the orientation-fixed AddCircle
homeomorphism evaluates to 1 on the literal positive loop. The normalized class of a
is therefore that same circle basis vector, by the source uniqueness clause. Its
constant-one degree-zero cocycle is the source circle unit: they agree on every
singular zero-simplex generator. The source circle profile thus gives singleton bases
in degrees 0 and 1 and the zero module in degrees at least 2.

2. The quotient maps from cocycles to cohomology are surjective. Hence two bilinear
products satisfying the universal representative equation agree on every pair of
cohomology classes. Likewise two units represented by the literal constant-one cochain
agree. This identifies the supplied cup and one with the source cup-law and Künneth
products; it also transfers their associativity and unit equations, with the exact
degree casts. It does not select an arbitrary ring on the cohomology groups.

3. For n=0 the original empty-coordinate function space is homeomorphic to the one-point
space. The source point calculation gives a singleton degree-zero basis represented by
the constant-one cocycle and zero cohomology in positive degrees. The empty subset is
the unique degree-zero index and its sorted list is empty; the specified monomial is
one. There are no positive-cardinality subsets, so the source zero modules have exactly
the empty bases required by the statement.

4. For n+1 split the SAME original torus by x↦(Fin.init x, x(Fin.last n)), with inverse
Fin.snoc. The coordinate equations prove the two inverses and continuity in the product
topology. The native coordinate CW theorem supplies finite CW structures on the two
factors (the circle is the one-coordinate torus). Both spaces are Hausdorff in their
original topology. The circle profile in step 1 proves its cohomology free and finite
in every degree, so the native finite-CW Künneth theorem applies without a dimension or
connectivity premise supplied to this constituent.

5. In degree k, the actual Künneth degree-domain is the direct sum indexed by p+q=k of
H^p(T^n) tensor H^q(circle). Only q=0 and q=1 survive. Tensor the induction bases with
the actual circle unit or positive generator and apply the original Künneth map. These
are bases because the tensor and direct-sum basis constructors transport along genuine
linear equivalences; the summands with q≥2 are zero. The q=0 indices are exactly the
k-subsets of the first n coordinates, and for k>0 the q=1 indices are exactly the
(k-1)-subsets with the last coordinate adjoined. The two cases give a bijection with
all original k-subsets of Fin(n+1), including k=0 and the empty cases.

6. The actual cup cross-product equation and coordinate pullback functoriality identify
the transported basis vectors with the increasing coordinate monomials. Subsets omitting
the last coordinate use the circle unit; those containing it append its positive class.
Associativity converts this to the theorem's recursive head-first product, without a
permutation sign since the appended coordinate is greatest. Sorting and subset-cardinality
casts are exactly the displayed native casts, so this is the required equality of basis
vectors, not merely an abstract isomorphism or rank calculation. Induction proves every n.

The induction below proves the native coordinate-basis assertion in every degree,
including the empty coordinate set and the degree-zero unit branch. Its circle,
cup-law and finite-CW Künneth dependencies retain their separate proof obligations.
-/
theorem coordinate_cup_monomial_basis (n : ℕ) :
    let X : TopCat := TopCat.of (UnitAddTorus (Fin n))
    let circleSpace : TopCat := TopCat.of UnitAddCircle
    ∀ (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
        SingularCochain.cohomology ℚ X q →ₗ[ℚ]
          SingularCochain.cohomology ℚ X (p + q))
      (one : SingularCochain.cohomology ℚ X 0)
      (a : SingularCochain.cycles ℚ (SingularCochain.complex ℚ circleSpace) 1)
      (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj circleSpace).sc 1).g.hom),
      z.val = ((TopCat.toSSet.obj circleSpace).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) (TopCat.toSSetObj₁Equiv.symm additivePositiveLoop)) 1 →
      (show ((SingularCochain.chainFunctor ℚ).obj circleSpace).X 1 ⟶
        ModuleCat.of ℚ ℚ from a.val) z.val = 1 →
      (∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
          (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
        ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
            SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
          cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
              (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
            SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
              ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩) →
      (∃ hu : SingularCochain.oneCochain ℚ X ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
        one = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
          ⟨SingularCochain.oneCochain ℚ X, hu⟩) →
      let α := fun i : Fin n ↦
        (SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ circleSpace) 1 a)
      let monomial : ∀ l : List (Fin n), SingularCochain.cohomology ℚ X l.length :=
        fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length) one
          (fun i l v ↦ cast (congrArg
            (fun d ↦ (SingularCochain.cohomology ℚ X d : Type)) (Nat.add_comm 1 l.length))
              (cup 1 l.length (α i) v)) l
      ∀ k : ℕ,
        ∃ B : Module.Basis {S : Finset (Fin n) // S.card = k} ℚ
            (SingularCochain.cohomology ℚ X k),
          ∀ S, B S = cast (congrArg
            (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
            ((S.val.length_sort (· ≤ ·)).trans S.property))
            (monomial (S.val.sort (· ≤ ·))) := by
  classical
  induction n with
  | zero =>
    dsimp only
    intro cup one a z hz hnorm hrep hunit
    exact coordinate_cup_monomial_basis_zero a cup one hunit
  | succ n ih =>
    dsimp only
    intro cup one a z hz hnorm hrep hunit
    obtain ⟨cupX, oneX, hrepX, hunitX, _, _, _⟩ :=
      absolute_cup_data (TopCat.of (UnitAddTorus (Fin n)))
    have hBasisX := ih cupX oneX a z hz hnorm hrepX hunitX
    choose BX hBX using hBasisX
    obtain ⟨B₁, hB₁⟩ := additive_circle_normalized_basis a z hz hnorm
    obtain ⟨B₀, hunitCircle, hB₀⟩ := additive_circle_unit_basis
    obtain ⟨_, _, hzeroCircle⟩ := additive_circle_profile
    obtain ⟨_, cwX, hcwX⟩ := real_torus_coordinate_cw_structure n
    let := cwX
    let := hcwX.1
    obtain ⟨_, cwY, hcwY⟩ := real_torus_coordinate_cw_structure 1
    let := cwY
    let := hcwY.1
    let X : TopCat := TopCat.of (UnitAddTorus (Fin n))
    let Y : TopCat := TopCat.of (UnitAddTorus (Fin 1))
    let eY : Y ≃ₜ TopCat.of UnitAddCircle := Homeomorph.funUnique (Fin 1) UnitAddCircle
    let EY := fun q ↦ singularPullbackHomeomorph eY q
    let B₀Y := B₀.map (EY 0)
    let B₁Y := B₁.map (EY 1)
    have hzeroY : ∀ q, 2 ≤ q → Subsingleton (SingularCochain.cohomology ℚ Y q) := by
      intro q hq
      let := hzeroCircle q hq
      exact ⟨fun x y ↦ (EY q).symm.injective (Subsingleton.elim _ _)⟩
    obtain ⟨cupP, oneP, hrepP, hunitP, _, _, _⟩ :=
      absolute_cup_data (SingularCochain.crossProductSpace X Y)
    have hproductBasis := circle_cross_product_basis n X Y BX B₀Y B₁Y hzeroY cupP hrepP
    let splitY : TopCat.of (UnitAddTorus (Fin (n + 1))) ≃ₜ
        SingularCochain.crossProductSpace X Y :=
      (torusSplitHomeomorph n).trans ((Homeomorph.refl _).prodCongr eY.symm)
    have hlastMap : (TopCat.isoOfHomeo splitY).hom ≫
        SingularCochain.crossProductSnd X Y ≫ (TopCat.isoOfHomeo eY).hom =
        coordinateProjection (n + 1) (Fin.last n) := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      rfl
    have hlast : (SingularCochain.cohomologyPullback ℚ
        (TopCat.isoOfHomeo splitY).hom 1).hom
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductSnd X Y) 1).hom (B₁Y ())) =
        (SingularCochain.cohomologyPullback ℚ
          (coordinateProjection (n + 1) (Fin.last n)) 1).hom
          (SingularCochain.cocycleClass ℚ
            (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a) := by
      have hmaps := congrArg (fun f ↦ SingularCochain.cohomologyPullback ℚ f 1) hlastMap
      rw [singularPullback_comp, singularPullback_comp] at hmaps
      have happ := congrArg (fun f ↦ f.hom (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)) hmaps
      dsimp only [B₁Y]
      rw [Module.Basis.map_apply, hB₁]
      exact happ
    have hearlierMap : ∀ i : Fin n, (TopCat.isoOfHomeo splitY).hom ≫
        SingularCochain.crossProductFst X Y ≫ coordinateProjection n i =
        coordinateProjection (n + 1) i.castSucc := by
      intro i
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      rfl
    have hearlier : ∀ i : Fin n,
        (SingularCochain.cohomologyPullback ℚ
          (TopCat.isoOfHomeo splitY).hom 1).hom
          ((SingularCochain.cohomologyPullback ℚ
            (SingularCochain.crossProductFst X Y) 1).hom
            ((SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1).hom
              (SingularCochain.cocycleClass ℚ
                (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a))) =
        (SingularCochain.cohomologyPullback ℚ
          (coordinateProjection (n + 1) i.castSucc) 1).hom
          (SingularCochain.cocycleClass ℚ
            (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a) := by
      intro i
      have hmaps := congrArg (fun f ↦ SingularCochain.cohomologyPullback ℚ f 1)
        (hearlierMap i)
      rw [singularPullback_comp, singularPullback_comp] at hmaps
      exact congrArg (fun f ↦ f.hom (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)) hmaps
    have hfirstUnit : (SingularCochain.cohomologyPullback ℚ
        ((TopCat.isoOfHomeo splitY).hom ≫ SingularCochain.crossProductFst X Y) 0).hom
        oneX = one := by
      obtain ⟨huX, huXeq⟩ := hunitX
      obtain ⟨huN, huNeq⟩ := hunit
      rw [huXeq, huNeq]
      exact quotient_map_representative
        (SingularCochain.pullback ℚ
          ((TopCat.isoOfHomeo splitY).hom ≫ SingularCochain.crossProductFst X Y)) 0
        ⟨_, huX⟩ ⟨_, huN⟩ (pullback_oneCochain _)
    have hlastUnit : (SingularCochain.cohomologyPullback ℚ
        (TopCat.isoOfHomeo splitY).hom 0).hom
        ((SingularCochain.cohomologyPullback ℚ
          (SingularCochain.crossProductSnd X Y) 0).hom (B₀Y ())) = one := by
      obtain ⟨huN, huNeq⟩ := hunit
      have hmap := quotient_map_representative
        (SingularCochain.pullback ℚ
          ((TopCat.isoOfHomeo splitY).hom ≫ SingularCochain.crossProductSnd X Y ≫
            (TopCat.isoOfHomeo eY).hom)) 0
        ⟨_, hunitCircle⟩ ⟨_, huN⟩ (pullback_oneCochain _)
      change (SingularCochain.cohomologyPullback ℚ _ 0).hom _ = _ at hmap
      rw [singularPullback_comp, singularPullback_comp] at hmap
      dsimp only [B₀Y]
      rw [Module.Basis.map_apply, hB₀, huNeq]
      exact hmap
    have hproductPullback := specified_cup_naturality
      (TopCat.isoOfHomeo splitY).hom cup cupP hrep hrepP
    let alphaX := fun i : Fin n ↦
      (SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1).hom
        (SingularCochain.cocycleClass ℚ
          (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)
    let alphaN := fun i : Fin (n + 1) ↦
      (SingularCochain.cohomologyPullback ℚ (coordinateProjection (n + 1) i) 1).hom
        (SingularCochain.cocycleClass ℚ
          (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)
    let Z : TopCat := TopCat.of (UnitAddTorus (Fin (n + 1)))
    let f : Z ⟶ X :=
      (TopCat.isoOfHomeo splitY).hom ≫ SingularCochain.crossProductFst X Y
    let mX : ∀ l : List (Fin n), SingularCochain.cohomology ℚ X l.length :=
      fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length)
        oneX (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          (Nat.add_comm 1 l.length)) (cupX 1 l.length (alphaX i) v)) l
    let mN : ∀ l : List (Fin (n + 1)), SingularCochain.cohomology ℚ Z l.length :=
      fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ Z l.length)
        one (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ Z d : Type))
          (Nat.add_comm 1 l.length)) (cup 1 l.length (alphaN i) v)) l
    have hlist : ∀ l : List (Fin n),
        HEq ((SingularCochain.cohomologyPullback ℚ f l.length).hom (mX l))
          (mN (l.map Fin.castSucc)) := by
      exact monomial_pullback f cup cupX hrep hrepX one oneX alphaN alphaX
        Fin.castSucc hfirstUnit (by
          intro i
          dsimp only [f]
          rw [singularPullback_comp]
          exact hearlier i)
    have hfirstPull : ∀ q (b : SingularCochain.cohomology ℚ X q),
        (SingularCochain.cohomologyPullback ℚ (TopCat.isoOfHomeo splitY).hom q).hom
          ((SingularCochain.cohomologyPullback ℚ
            (SingularCochain.crossProductFst X Y) q).hom b) =
        (SingularCochain.cohomologyPullback ℚ f q).hom b := by
      intro q b
      dsimp only [f]
      rw [singularPullback_comp]
      rfl
    have hpullBX : ∀ k (S : {S : Finset (Fin n) // S.card = k}),
        (SingularCochain.cohomologyPullback ℚ f k).hom (BX k S) =
        cast (congrArg (fun d ↦ (SingularCochain.cohomology ℚ Z d : Type))
          ((by simp : ((S.val.sort (· ≤ ·)).map Fin.castSucc).length =
              (S.val.sort (· ≤ ·)).length).trans
            ((S.val.length_sort (· ≤ ·)).trans S.property)))
          (mN ((S.val.sort (· ≤ ·)).map Fin.castSucc)) := by
      intro k S
      rw [hBX]
      apply eq_of_heq
      exact (((by
          intro X Y f p q h a
          cases h
          rfl) : ∀ {X Y : TopCat} (f : X ⟶ Y) {p q : ℕ} (h : p = q)
    (a : SingularCochain.cohomology ℚ Y p),
    HEq ((SingularCochain.cohomologyPullback ℚ f q).hom
      (cast (congrArg (fun d ↦
        (SingularCochain.cohomology ℚ Y d : Type)) h) a))
      (cast (congrArg (fun d ↦
        (SingularCochain.cohomology ℚ X d : Type)) h)
        ((SingularCochain.cohomologyPullback ℚ f p).hom a))) f
        ((S.val.length_sort (· ≤ ·)).trans S.property) _).trans
        ((cast_heq _ _).trans ((hlist _).trans (cast_heq _ _).symm))
    intro k
    cases k with
    | zero =>
      obtain ⟨B, hB⟩ := hproductBasis 0
      let E := singularPullbackHomeomorph splitY 0
      let e := (zeroCircleTensorIndex n).symm.trans
        ((emptySubsetIndex n).symm.trans (emptySubsetIndex (n + 1)))
      refine ⟨(B.map E).reindex e, ?_⟩
      intro S
      have hS : S = ⟨∅, rfl⟩ := Subtype.ext (Finset.card_eq_zero.mp S.property)
      subst S
      rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
      change E (B ⟨⟨(0, 0), rfl⟩, ⟨∅, rfl⟩, ()⟩) = _
      rw [hB ⟨(0, 0), rfl⟩ ⟨∅, rfl⟩ ()]
      change (SingularCochain.cohomologyPullback ℚ
        (TopCat.isoOfHomeo splitY).hom 0).hom
        (cupP 0 0
          ((SingularCochain.cohomologyPullback ℚ
            (SingularCochain.crossProductFst X Y) 0).hom (BX 0 ⟨∅, rfl⟩))
          ((SingularCochain.cohomologyPullback ℚ
            (SingularCochain.crossProductSnd X Y) 0).hom (B₀Y ()))) = _
      rw [hproductPullback 0 0, hlastUnit, hfirstPull]
      have hBXzero : BX 0 ⟨∅, rfl⟩ = oneX := by
        rw [hBX]
        apply eq_of_heq
        refine (cast_heq _ _).trans ?_
        dsimp only [Subtype.coe_mk]
        rw [Finset.sort_empty]
      rw [hBXzero, hfirstUnit]
      have hu := (specified_cup_assoc_unit Z cup one hrep hunit).2 0 one
      refine (eq_of_heq hu.2).trans ?_
      apply eq_of_heq
      refine HEq.trans ?_ (cast_heq _ _).symm
      dsimp only [Subtype.coe_mk]
      rw [Finset.sort_empty]
    | succ k =>
      obtain ⟨B, hBinl, hBinr⟩ :=
        circle_cross_product_basis_successor n X Y BX B₀Y B₁Y hzeroY cupP hrepP k
      let E := singularPullbackHomeomorph splitY (k + 1)
      let v := fun S : {S : Finset (Fin (n + 1)) // S.card = k + 1} ↦
        cast (congrArg (fun d ↦ (SingularCochain.cohomology ℚ Z d : Type))
          ((S.val.length_sort (· ≤ ·)).trans S.property)) (mN (S.val.sort (· ≤ ·)))
      change ∃ D : Module.Basis _ ℚ (SingularCochain.cohomology ℚ Z (k + 1)),
        ∀ S, D S = v S
      apply basis_from_successor_subsets n k v (B.map E)
      · intro S
        rw [Module.Basis.map_apply, hBinl]
        change (SingularCochain.cohomologyPullback ℚ
          (TopCat.isoOfHomeo splitY).hom (k + 1)).hom _ = _
        rw [hproductPullback (k + 1) 0, hlastUnit, hfirstPull]
        have hrightUnit := (specified_cup_assoc_unit Z cup one hrep hunit).2
          (k + 1) ((SingularCochain.cohomologyPullback ℚ f (k + 1)).hom (BX (k + 1) S))
        have hv := successor_subset_monomial_inl n Z cup one alphaN k S
        change cup (k + 1) 0
          ((SingularCochain.cohomologyPullback ℚ f (k + 1)).hom (BX (k + 1) S)) one = _
        exact (eq_of_heq hrightUnit.2).trans ((hpullBX (k + 1) S).trans hv.symm)
      · intro S
        rw [Module.Basis.map_apply, hBinr]
        change (SingularCochain.cohomologyPullback ℚ
          (TopCat.isoOfHomeo splitY).hom (k + 1)).hom _ = _
        rw [hproductPullback k 1, hlast, hfirstPull]
        change cup k 1 ((SingularCochain.cohomologyPullback ℚ f k).hom (BX k S))
          (alphaN (Fin.last n)) = _
        rw [hpullBX]
        exact (successor_subset_monomial_inr n Z cup one alphaN hrep hunit k S).symm

end HolomorphicAnosov.TorusRationalCupBasisKronecker
