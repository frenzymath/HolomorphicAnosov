import HolomorphicAnosov.Topology.Homology.SignedShuffleAssociativity
import HolomorphicAnosov.Topology.Homology.SignedShuffleTransposition
import HolomorphicAnosov.Topology.Homology.RationalRelativeTensorRepresentative
import HolomorphicAnosov.Topology.Homology.RationalRelativeTensorComparison
import HolomorphicAnosov.Topology.Homology.NativeRelativeShuffleComparison
import HolomorphicAnosov.Topology.ModuleCatCycleClassNaturality
import HolomorphicAnosov.Algebra.Homology.ModuleCatHomologyClassBoundary
import HolomorphicAnosov.Algebra.Homology.ModuleCatBoundaryWitness
import HolomorphicAnosov.Algebra.Homology.FieldTensorHomologyKunneth
import HolomorphicAnosov.Topology.SingularEilenbergZilberAcyclicModels
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import HolomorphicAnosov.Topology.Homology.SignedShuffleChainMap
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.DirectSum.Module

/-!
# Rational relative singular homology and its shuffle Künneth map

Source: Bredon, *Topology and Geometry* (1993), IV Theorem 16.1 pp.220–222,
VI Lemma 1.1 and Theorems 1.2–1.3 pp.316–318, Corollary 1.4 p.318,
Theorem 1.5 pp.318–320, the one-relative-factor proof following Theorem 1.6 p.320,
and VI §3 pp.324–325. Hatcher, *Algebraic Topology*, pp.277–278 specifies the
signed staircase chain map. DAG node: `topo.rational_relative_homology_cross_product_kunneth_g7`.

The coefficient object below is the genuine rank-one rational module. Universe lifting
changes no coefficients. Pairs and relative chain complexes use Mathlib's actual singular
subspace inclusion and cokernel, with the original product and subspace topologies.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace HolomorphicAnosov.RationalRelativeKunneth

/-- The rational coefficient object, Bredon VI §1 p.320. -/
abbrev coefficients : ModuleCat.{u} ℚ := ModuleCat.of ℚ (ULift.{u} ℚ)

/-- The genuine singular pair `(X,B)`, Bredon p.320 and Hatcher pp.115–118. -/
abbrev pair (X : TopCat.{u}) (B : Set X) : SSetPair.{u} :=
  HolomorphicAnosov.Topology.Homology.singularSubspacePair X B

/-- Unnormalized rational singular chains, Bredon VI §1 pp.316–320. -/
abbrev chains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℚ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex coefficients

/-- The original rational relative quotient chain complex, Bredon p.320. -/
abbrev relativeChains (X : TopCat.{u}) (B : Set X) :
    ChainComplex (ModuleCat.{u} ℚ) ℕ :=
  (pair X B).chainComplex coefficients

/-- Ordinary rational homology of the specified singular quotient, Bredon p.320. -/
abbrev relativeHomology (X : TopCat.{u}) (B : Set X) (n : ℕ) : ModuleCat.{u} ℚ :=
  (pair X B).homology coefficients n

/-- Ordinary absolute rational homology, Bredon VI §1 pp.316–320. -/
abbrev homology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℚ :=
  (TopCat.toSSet.obj X).homology coefficients n

/-- The quotient chain map of the actual singular subspace inclusion, Bredon p.320. -/
abbrev chainProjection (X : TopCat.{u}) (B : Set X) :
    chains X ⟶ relativeChains X B :=
  (pair X B).chainComplexπ coefficients

/-- A continuous map of pairs acts on the original singular pair, Hatcher p.118. -/
def pairMap {X Y : TopCat.{u}} (B : Set X) (D : Set Y) (f : X ⟶ Y)
    (hf : Set.MapsTo f B D) : pair X B ⟶ pair Y D :=
  SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom
      ⟨fun b ↦ ⟨f b, hf b.property⟩, f.hom.continuous.comp continuous_subtype_val |>.subtype_mk _⟩))
    (TopCat.toSSet.map f) (by simp only [pair, Topology.Homology.singularSubspacePair]; rfl)

/-- The actual map induced on relative rational homology, Hatcher p.118. -/
def relativeMap {X Y : TopCat.{u}} (B : Set X) (D : Set Y) (f : X ⟶ Y)
    (hf : Set.MapsTo f B D) (n : ℕ) :
    relativeHomology X B n ⟶ relativeHomology Y D n :=
  SSetPair.homologyMap (pairMap B D f hf) coefficients n

/-- Absolute singular rational homology functoriality, Bredon VI §1 p.316. -/
def homologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    homology X n ⟶ homology Y n :=
  SSet.homologyMap (TopCat.toSSet.map f) coefficients n

/-- The literal product subspace `B × Z`, Bredon VI §1 p.320. -/
def productSubspace (X Z : TopCat.{u}) (B : Set X) : Set (X × Z) :=
  {w | w.1 ∈ B}

/-- The finite total-degree index, with no boundedness assumption on the chain complexes.
Source: Bredon algebraic Künneth Theorem 1.5 pp.318–320. -/
abbrev bidegree (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The actual direct sum of rational tensor products in the claimed source.
Source: Bredon VI Theorem 1.5, field specialization p.320. -/
abbrev kunnethSource (X Z : TopCat.{u}) (B : Set X) (n : ℕ) : Type u :=
  DirectSum (bidegree n) (fun pq ↦
    TensorProduct ℚ (relativeHomology X B pq.val.1) (homology Z pq.val.2))

/-- The actual target relative homology, with ordinary product/subspace topology.
Source: Bredon p.320. -/
abbrev kunnethTarget (X Z : TopCat.{u}) (B : Set X) (n : ℕ) : ModuleCat.{u} ℚ :=
  relativeHomology (TopCat.of (X × Z)) (productSubspace X Z B) n

/-- A product map of genuine pairs on the original point carriers.
Source: Bredon product naturality, VI pp.316–320. -/
def productMap {X X' Z Z' : TopCat.{u}} (f : X ⟶ X') (g : Z ⟶ Z') :
    TopCat.of (X × Z) ⟶ TopCat.of (X' × Z') :=
  TopCat.ofHom ⟨fun w ↦ (f w.1, g w.2),
    (f.hom.continuous.comp continuous_fst).prodMk (g.hom.continuous.comp continuous_snd)⟩

/-- The cycle submodule of a native rational complex in a natural-number degree.
The zero outgoing differential at degree zero uses Mathlib's chain-shape convention.
Source: Bredon VI §1 pp.318–320. -/
abbrev cycles (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (n : ℕ) :=
  LinearMap.ker (C.dFrom n).hom

/-- Evaluate Mathlib's outgoing-differential comparison after transporting its
codomain with `xNextIso`. This is the native chain-shape adapter used in the
cycle calculation of Bredon VI p.320; the proof is an API specialization. -/
theorem dFrom_xNextIso_apply (C : ChainComplex (ModuleCat.{u} ℚ) ℕ)
    {n m : ℕ} (h : (ComplexShape.down ℕ).Rel n m) (a : C.X n) :
    (C.xNextIso h).hom ((C.dFrom n).hom a) = (C.d n m).hom a := by
  exact congrArg (fun f ↦ f.hom a) (C.dFrom_comp_xNextIso h)

/-- The outgoing cycle condition may be checked with any explicit adjacent
differential. The inverse comparison proves the reverse implication without
rewriting a dependent codomain. -/
theorem dFrom_apply_eq_zero_iff_d (C : ChainComplex (ModuleCat.{u} ℚ) ℕ)
    {n m : ℕ} (h : (ComplexShape.down ℕ).Rel n m) (a : C.X n) :
    (C.dFrom n).hom a = 0 ↔ (C.d n m).hom a = 0 := by
  constructor
  · intro ha
    rw [← dFrom_xNextIso_apply C h a, ha]
    exact map_zero _
  · intro ha
    rw [C.dFrom_eq h]
    change (C.xNextIso h).inv ((C.d n m).hom a) = 0
    rw [ha]
    exact map_zero _

/-- The predecessor differential detects cycles in every natural-number degree,
including zero, where both outgoing differentials vanish by the chain shape. -/
theorem dFrom_apply_eq_zero_iff_pred (C : ChainComplex (ModuleCat.{u} ℚ) ℕ)
    (n : ℕ) (a : C.X n) :
    (C.dFrom n).hom a = 0 ↔ (C.d n (n - 1)).hom a = 0 := by
  cases n with
  | zero => simp [HomologicalComplex.dFrom, ComplexShape.down_Rel]
  | succ n => exact dFrom_apply_eq_zero_iff_d C (by simp) a

/-- An absolute cycle has zero boundary in the exact convention of the shuffle
Leibniz identity, also in degree zero. -/
theorem signedShuffle_boundary_cycle (X : TopCat.{u}) (n : ℕ)
    (a : cycles (chains X) n) : SignedShuffle.boundary X n a = 0 := by
  exact (dFrom_apply_eq_zero_iff_pred (chains X) n a).mp a.property

/-- The native class of a genuine cycle in ordinary module homology.
Source: Bredon pp.318–320. The proved module homology isomorphism identifies the
kernel/image quotient with Mathlib's existing homology, so no new homology is assumed. -/
def cycleClass (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (n : ℕ) :
    cycles C n →ₗ[ℚ] C.homology n :=
  ((C.sc n).moduleCatHomologyIso.inv).hom.comp (C.sc n).moduleCatLeftHomologyData.π.hom

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity of the native quotient presentation of homology.
Source: Bredon VI §1 pp.318–320; this specializes the quotient API. -/
theorem cycleClass_surjective (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (n : ℕ) :
    Function.Surjective (cycleClass C n) := by
  intro a
  obtain ⟨c, hc⟩ := ((C.sc n).moduleCatToCycles.range).mkQ_surjective
    ((C.sc n).moduleCatHomologyIso.hom a)
  refine ⟨c, ?_⟩
  change (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ c) = a
  rw [hc]
  exact Iso.hom_inv_id_apply _ a

set_option backward.isDefEq.respectTransparency false in
/-- Native homology-map naturality in the explicit cycle presentation.
Source: Hatcher p.111; this transports the existing short-complex naturality theorem. -/
theorem cycleClass_map {C D : ChainComplex (ModuleCat.{u} ℚ) ℕ}
    (f : C ⟶ D) (n : ℕ) (a : cycles C n) (b : cycles D n)
    (h : (f.f n).hom a.val = b.val) :
    (HomologicalComplex.homologyMap f n).hom (cycleClass C n a) = cycleClass D n b := by
  have hC := ConcreteCategory.congr_hom (C.sc n).moduleCatCyclesIso_inv_π a
  have hD := ConcreteCategory.congr_hom (D.sc n).moduleCatCyclesIso_inv_π b
  change (C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv a) = cycleClass C n a at hC
  change (D.sc n).homologyπ ((D.sc n).moduleCatCyclesIso.inv b) = cycleClass D n b at hD
  rw [← hC, ← hD]
  exact Topology.moduleCat_cycleClass_naturality (R := ℚ)
    (S := C.sc n) (T := D.sc n)
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map f) a b h

/-- Boundaries in the genuine cycle module, Bredon VI Theorem1.5 pp.318–320. -/
abbrev boundaries (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (n : ℕ) :=
  LinearMap.range (C.sc n).moduleCatToCycles

/-- The original shuffle followed by the actual product-pair quotient. No data are
selected by Eilenberg–Zilber or Künneth. Source: Bredon VI p.320. -/
def projectedShuffle (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :=
  (SignedShuffle.shuffleBilinear X Z p q).compr₂
    ((chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)).hom

/-- The shuffle of a chain supported in B is zero in the product relative quotient.
Source: Bredon IV16.1 pp.220–222, VI p.320; Hatcher pp.277–278.
Proof: on each singular simplex in B and each simplex in Z, every affine staircase
has its first coordinate in B. Its inclusion in X×Z therefore factors through B×Z,
and the cokernel projection annihilates it. Extend over the two free singular bases
by rational bilinearity. This applies to arbitrary B, not only open B. -/
theorem relativeShuffle_subspace_vanish (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :
    (SSet.chainComplexMap (pair X B).hom coefficients).f p ≫
      ModuleCat.ofHom (projectedShuffle X Z B p q) = 0 := by
  let inc : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(B × Z, productSubspace X Z B) :=
    ⟨fun w ↦ ⟨(w.1.val, w.2), w.1.property⟩,
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩
  have hf : TopCat.ofHom (inc.prodMap (ContinuousMap.id Z)) =
      TopCat.ofHom j ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
    ext w : 1
    rfl
  have hz (c : (chains (TopCat.of (B × Z))).X (p + q)) :
      (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
        (SignedShuffle.pushforward (inc.prodMap (ContinuousMap.id Z)) (p + q) c) = 0 := by
    have h := (pair (TopCat.of (X × Z)) (productSubspace X Z B)).chainComplex_condition_f
      coefficients (p + q)
    have hh := congrArg (fun f ↦ f.hom
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j))
        coefficients).f (p + q) c)) h
    change ((pair (TopCat.of (X × Z)) (productSubspace X Z B)).chainComplexπ
      coefficients).f (p + q)
        ((SSet.chainComplexMap (pair (TopCat.of (X × Z))
          (productSubspace X Z B)).hom coefficients).f (p + q)
          ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j))
            coefficients).f (p + q) c)) = 0 at hh
    have hc : SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (inc.prodMap (ContinuousMap.id Z))))
        coefficients =
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j)) coefficients ≫
          SSet.chainComplexMap (TopCat.toSSet.map
            (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
              C(productSubspace X Z B, X × Z)))) coefficients := by
      dsimp only [SSet.chainComplexMap]
      rw [hf, Functor.map_comp, Functor.map_comp]
    change (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (inc.prodMap (ContinuousMap.id Z))))
        coefficients).f (p + q) c) = 0
    rw [hc]
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    exact hh
  ext a b
  change (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
    (SignedShuffle.shuffleBilinear X Z p q (SignedShuffle.pushforward inc p a) b) = 0
  have hn := (SignedShuffle.signedShuffle_chainMap (TopCat.of B) Z).2.2.1
    X Z inc (ContinuousMap.id Z) p q a b
  have hid : SignedShuffle.pushforward (ContinuousMap.id Z) q b = b := by
    simp [SignedShuffle.pushforward, SSet.chainComplexMap]
  rw [hid] at hn
  change SignedShuffle.pushforward (inc.prodMap (ContinuousMap.id Z)) (p + q)
      (SignedShuffle.shuffleBilinear (TopCat.of B) Z p q a b) =
    SignedShuffle.shuffleBilinear X Z p q (SignedShuffle.pushforward inc p a) b at hn
  rw [← hn]
  exact hz _

/-- The concrete first descent is through the native relative CHAIN quotient.
Source: Bredon VI p.320. A relative cycle is not assumed to lift to an absolute cycle. -/
def relativeShuffle (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :
    (relativeChains X B).X p →ₗ[ℚ] (chains Z).X q →ₗ[ℚ]
      (relativeChains (TopCat.of (X × Z)) (productSubspace X Z B)).X (p + q) :=
  (CokernelCofork.IsColimit.desc'
    ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)
    (ModuleCat.ofHom (projectedShuffle X Z B p q))
    (relativeShuffle_subspace_vanish X Z B p q)).val.hom

/-- The cokernel descent evaluates on the original quotient projection.
This is its native universal-property equation, Bredon VI p.320. -/
@[simp] theorem relativeShuffle_projection (X Z : TopCat.{u}) (B : Set X) (p q : ℕ)
    (a : (chains X).X p) (b : (chains Z).X q) :
    relativeShuffle X Z B p q ((chainProjection X B).f p a) b =
      (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
        (SignedShuffle.shuffleBilinear X Z p q a b) := by
  have h := (CokernelCofork.IsColimit.desc'
    ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)
    (ModuleCat.ofHom (projectedShuffle X Z B p q))
    (relativeShuffle_subspace_vanish X Z B p q)).property
  exact congrArg (fun f ↦ f.hom a b) h

/-- Regrading preserves vanishing in the relative quotient. Equality induction
avoids rewriting inside the dependent target chain group. -/
theorem chainProjection_regrade_eq_zero (X : TopCat.{u}) (B : Set X)
    {n m : ℕ} (h : n = m) (c : (chains X).X n)
    (hc : (chainProjection X B).f n c = 0) :
    (chainProjection X B).f m (SignedShuffle.regrade X h c) = 0 := by
  subst m
  exact hc

/-- The descended shuffle carries genuine relative/absolute cycles to cycles.
Source: Bredon VI p.320 and the published signedShuffle_chainMap Leibniz equation.
Proof: lift the relative chain degreewise through the surjective native cokernel.
Its differential has image zero in the relative quotient, so it is a chain from B.
Shuffle that differential with the absolute cycle: its image lies in B×Z and vanishes
by the preceding certificate; the other Leibniz term is zero. Projection commutes
with the differential. Degree zero has zero outgoing differential, with no negative
chain group or extra cycle hypothesis. -/
theorem relativeShuffle_cycle (X Z : TopCat.{u}) (B : Set X) (p q : ℕ)
    (a : cycles (relativeChains X B) p) (b : cycles (chains Z) q) :
    ((relativeChains (TopCat.of (X × Z)) (productSubspace X Z B)).dFrom (p + q)).hom
      (relativeShuffle X Z B p q a b) = 0 := by
  apply (dFrom_apply_eq_zero_iff_pred _ (p + q) _).mpr
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
    (Cofork.IsColimit.epi
      ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p))
    (a : (relativeChains X B).X p)
  have hda : (chainProjection X B).f (p - 1) (SignedShuffle.boundary X p c) = 0 := by
    have hcomm := congrArg (fun f ↦ f.hom c) ((chainProjection X B).comm p (p - 1))
    change (relativeChains X B).d p (p - 1) ((chainProjection X B).f p c) =
      (chainProjection X B).f (p - 1) (SignedShuffle.boundary X p c) at hcomm
    rw [← hcomm, hc]
    exact (dFrom_apply_eq_zero_iff_pred (relativeChains X B) p a).mp a.property
  have hfirst :
      (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q - 1)
        (SignedShuffle.firstBoundaryTerm X Z p q c b) = 0 := by
    unfold SignedShuffle.firstBoundaryTerm
    split_ifs with hp
    · exact map_zero _
    · apply chainProjection_regrade_eq_zero
      rw [← relativeShuffle_projection, hda]
      simp
  have hsecond : SignedShuffle.secondBoundaryTerm X Z p q c b = 0 := by
    simp [SignedShuffle.secondBoundaryTerm, signedShuffle_boundary_cycle Z q b]
  have hLeibniz := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p q c b
  change SignedShuffle.boundary (TopCat.of (X × Z)) (p + q)
      (SignedShuffle.shuffleBilinear X Z p q c b) =
    SignedShuffle.firstBoundaryTerm X Z p q c b +
      (-1 : ℚ) ^ p • SignedShuffle.secondBoundaryTerm X Z p q c b at hLeibniz
  rw [← hc, relativeShuffle_projection]
  have hcomm := congrArg (fun f ↦ f.hom (SignedShuffle.shuffleBilinear X Z p q c b))
    ((chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).comm
      (p + q) (p + q - 1))
  change (relativeChains (TopCat.of (X × Z)) (productSubspace X Z B)).d
      (p + q) (p + q - 1)
      ((chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
        (SignedShuffle.shuffleBilinear X Z p q c b)) =
    (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q - 1)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q)
        (SignedShuffle.shuffleBilinear X Z p q c b)) at hcomm
  rw [hcomm, hLeibniz, hsecond, smul_zero, add_zero]
  exact hfirst

/-- Actual cycle-valued relative shuffle, constructed from the preceding chain data.
Source: Bredon VI pp.318–320. Only its cycle certificate is postponed. -/
def relativeCycleShuffle (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :
    cycles (relativeChains X B) p →ₗ[ℚ] cycles (chains Z) q →ₗ[ℚ]
      cycles (relativeChains (TopCat.of (X × Z)) (productSubspace X Z B)) (p + q) :=
  LinearMap.mk₂ ℚ (fun a b ↦ ⟨relativeShuffle X Z B p q a b,
    relativeShuffle_cycle X Z B p q a b⟩)
    (fun a a' b ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
    (fun a b b' ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))

/-- The actual class-valued shuffle before dividing the two cycle modules by boundaries.
Source: Bredon VI Theorem1.5 pp.318–320. -/
def relativeCycleClasses (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :=
  (relativeCycleShuffle X Z B p q).compr₂
    (cycleClass (relativeChains (TopCat.of (X × Z)) (productSubspace X Z B)) (p + q))

set_option backward.isDefEq.respectTransparency false in
/-- Boundaries in either input give zero product class. Source: Bredon VI pp.318–320.
Proof: for a first boundary dα and a cycle z, the Leibniz rule expresses their product
as d(α×z). For a second boundary dζ and relative cycle c, use the witness
(-1)^p(c×ζ); the remaining first-boundary term is zero in the relative quotient.
Thus both values lie in the native target boundary submodule and have zero class.
The degree-(p+1,q) and (p,q+1) witnesses exist also for p=0 or q=0; no negative
indices are used. Extend linearly to each boundary submodule. -/
theorem relativeShuffle_boundaries (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :
    boundaries (relativeChains X B) p ≤ (relativeCycleClasses X Z B p q).ker ∧
    boundaries (chains Z) q ≤ (relativeCycleClasses X Z B p q).flip.ker := by
  have hzero (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (k : ℕ)
      (c : cycles C k) (x : C.X (k + 1)) (hx : (C.d (k + 1) k).hom x = c.val) :
      cycleClass C k c = 0 :=
    moduleCatHomologyClass_eq_zero_of_boundary C (k + 1) k rfl c ⟨x, hx⟩
  have hcompose (W : TopCat.{u}) {i j k : ℕ} (hij : i = j) (hjk : j = k)
      (c : SignedShuffle.Chain W i) :
      SignedShuffle.regrade W hjk (SignedShuffle.regrade W hij c) =
        SignedShuffle.regrade W (hij.trans hjk) c := by
    subst j
    subst k
    rfl
  have hcomm (W : TopCat.{u}) (D : Set W) (i j : ℕ) (c : (chains W).X i) :
      (relativeChains W D).d i j ((chainProjection W D).f i c) =
        (chainProjection W D).f j ((chains W).d i j c) :=
    ConcreteCategory.congr_hom ((chainProjection W D).comm i j) c
  constructor
  · intro a ha
    apply LinearMap.mem_ker.mpr
    ext b
    obtain ⟨x, hx⟩ := moduleCatBoundary_exists_successor (relativeChains X B) p a ha
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f (p + 1))).mp
      (Cofork.IsColimit.epi
        ((pair X B).isColimitCokernelCoforkChainComplexX coefficients (p + 1))) x
    change cycleClass _ _ (relativeCycleShuffle X Z B p q a b) = 0
    let w := SignedShuffle.regrade (TopCat.of (X × Z))
      (by omega : p + 1 + q = p + q + 1)
      (SignedShuffle.shuffleBilinear X Z (p + 1) q c b)
    apply hzero _ _ _ ((chainProjection _ _).f (p + q + 1) w)
    rw [hcomm]
    have h := (SignedShuffle.signedShuffle_chainMap X Z).2.1 (p + 1) q c b
    have hb := signedShuffle_boundary_cycle Z q b
    simp only [SignedShuffle.shuffle, TensorProduct.lift.tmul] at h
    have hz : SignedShuffle.secondBoundaryTerm X Z (p + 1) q c b = 0 := by
      simp [SignedShuffle.secondBoundaryTerm, hb]
    rw [hz, smul_zero, add_zero] at h
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q + 1) w) = _
    rw [SignedShuffle.boundary_regrade, h]
    simp only [SignedShuffle.firstBoundaryTerm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceDIte]
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.regrade (TopCat.of (X × Z)) _
        (SignedShuffle.regrade (TopCat.of (X × Z)) _
          (SignedShuffle.shuffleBilinear X Z p q ((chains X).d (p + 1) p c) b))) = _
    rw [hcompose]
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.shuffleBilinear X Z p q ((chains X).d (p + 1) p c) b) = _
    rw [← relativeShuffle_projection, ← hcomm, hc, hx]
    rfl
  · intro b hb
    apply LinearMap.mem_ker.mpr
    ext a
    obtain ⟨x, hx⟩ := moduleCatBoundary_exists_successor (chains Z) q b hb
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
      (Cofork.IsColimit.epi
        ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
    have hda : (chainProjection X B).f (p - 1) (SignedShuffle.boundary X p c) = 0 := by
      rw [SignedShuffle.boundary, ← hcomm, hc]
      exact (dFrom_apply_eq_zero_iff_pred (relativeChains X B) p a).mp a.property
    change cycleClass _ _ (relativeCycleShuffle X Z B p q a b) = 0
    let w := SignedShuffle.regrade (TopCat.of (X × Z))
      (by omega : p + (q + 1) = p + q + 1)
      (SignedShuffle.shuffleBilinear X Z p (q + 1) c x)
    apply hzero _ _ _ ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q + 1) w)
    rw [map_smul, hcomm]
    have h := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p (q + 1) c x
    simp only [SignedShuffle.shuffle, TensorProduct.lift.tmul] at h
    change (-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q + 1) w) = _
    rw [SignedShuffle.boundary_regrade, h, map_add, map_smul, map_add, map_smul]
    have hz : (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
        (SignedShuffle.regrade (TopCat.of (X × Z))
          (by omega : p + (q + 1) - 1 = p + q)
          (SignedShuffle.firstBoundaryTerm X Z p (q + 1) c x)) = 0 := by
      apply chainProjection_regrade_eq_zero
      unfold SignedShuffle.firstBoundaryTerm
      split_ifs with hp
      · exact map_zero _
      · apply chainProjection_regrade_eq_zero
        rw [← relativeShuffle_projection, hda]
        simp
    erw [hz, zero_add]
    simp only [SignedShuffle.secondBoundaryTerm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceDIte]
    change (-1 : ℚ) ^ p • ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.regrade (TopCat.of (X × Z)) _
        (SignedShuffle.regrade (TopCat.of (X × Z)) _
          (SignedShuffle.shuffleBilinear X Z p q c ((chains Z).d (q + 1) q x))))) = _
    rw [hcompose]
    change (-1 : ℚ) ^ p • ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.shuffleBilinear X Z p q c ((chains Z).d (q + 1) q x))) = _
    rw [hx, smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul]
    rw [← relativeShuffle_projection, hc]
    rfl

/-- Descent through both native homology quotients and the tensor universal property.
Source: Bredon VI Theorem1.5 pp.318–320. This is a real data construction, not an
unspecified map whose invertibility is assumed. -/
def quotientTensor (C D E : ChainComplex (ModuleCat.{u} ℚ) ℕ) (p q n : ℕ)
    (b : cycles C p →ₗ[ℚ] cycles D q →ₗ[ℚ] E.homology n)
    (hC : boundaries C p ≤ b.ker) (hD : boundaries D q ≤ b.flip.ker) :
    TensorProduct ℚ (C.homology p) (D.homology q) →ₗ[ℚ] E.homology n :=
  TensorProduct.lift ((b.liftQ₂ (boundaries C p) (boundaries D q) hC hD).compl₁₂
    ((C.sc p).moduleCatHomologyIso.hom).hom ((D.sc q).moduleCatHomologyIso.hom).hom)

/-- Evaluation of the two quotient lifts on cycle representatives.
Source: Bredon VI §1 pp.318–320; both quotient lifts evaluate on their representatives. -/
theorem quotientTensor_cycleClass (C D E : ChainComplex (ModuleCat.{u} ℚ) ℕ)
    (p q n : ℕ) (b : cycles C p →ₗ[ℚ] cycles D q →ₗ[ℚ] E.homology n)
    (hC : boundaries C p ≤ b.ker) (hD : boundaries D q ≤ b.flip.ker)
    (a : cycles C p) (d : cycles D q) :
    quotientTensor C D E p q n b hC hD (cycleClass C p a ⊗ₜ[ℚ] cycleClass D q d) =
      b a d := by
  simp only [quotientTensor, TensorProduct.lift.tmul, cycleClass]
  change b.liftQ₂ _ _ hC hD
    ((C.sc p).moduleCatHomologyIso.hom ((C.sc p).moduleCatHomologyIso.inv
      ((C.sc p).moduleCatLeftHomologyData.π a)))
    ((D.sc q).moduleCatHomologyIso.hom ((D.sc q).moduleCatHomologyIso.inv
      ((D.sc q).moduleCatLeftHomologyData.π d))) = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  rfl

/-- The canonical relative homology cross product of the PUBLISHED signed shuffle.
Source: Bredon VI pp.318–320. Its data depend only on the named descent proof laws. -/
def crossTensor (X Z : TopCat.{u}) (B : Set X) (p q : ℕ) :
    TensorProduct ℚ (relativeHomology X B p) (homology Z q) →ₗ[ℚ]
      kunnethTarget X Z B (p + q) :=
  quotientTensor _ _ _ p q (p + q) (relativeCycleClasses X Z B p q)
    (relativeShuffle_boundaries X Z B p q).1 (relativeShuffle_boundaries X Z B p q).2

/-- Pure-class notation for the same canonical relative shuffle, Bredon VI p.320. -/
def cross (X Z : TopCat.{u}) (B : Set X) (p q : ℕ)
    (a : relativeHomology X B p) (b : homology Z q) : kunnethTarget X Z B (p + q) :=
  crossTensor X Z B p q (a ⊗ₜ[ℚ] b)

/-- Reindex a homology degree by a proved equality; no homology class is changed.
Source: the total-degree convention in Bredon VI Theorem1.5. -/
def regradeRelative (X : TopCat.{u}) (B : Set X) {n m : ℕ} (h : n = m) :
    relativeHomology X B n →ₗ[ℚ] relativeHomology X B m := by
  subst m
  exact LinearMap.id

/-- Degree transport of a cycle-class naturality equation. -/
theorem regradeRelative_cycleClass_map (X : TopCat.{u}) (B : Set X)
    {C : ChainComplex (ModuleCat.{u} ℚ) ℕ} (f : C ⟶ relativeChains X B)
    {n m : ℕ} (h : n = m) (a : cycles C m) (b : cycles (relativeChains X B) n)
    (hb : HEq b.val ((f.f m).hom a.val)) :
    regradeRelative X B h (cycleClass (relativeChains X B) n b) =
      (HomologicalComplex.homologyMap f m).hom (cycleClass C m a) := by
  subst m
  exact (cycleClass_map f n a b (eq_of_heq hb).symm).symm

/-- Chain projection respects a change of degree index. -/
theorem chainProjection_regrade_heq (X : TopCat.{u}) (B : Set X)
    {n m : ℕ} (h : n = m) (a : (chains X).X n) :
    HEq ((chainProjection X B).f m (SignedShuffle.regrade X h a))
      ((chainProjection X B).f n a) := by
  subst m
  rfl

/-- The full total-degree canonical Künneth map, Bredon VI Theorem1.5 p.320. -/
def kunnethMap (X Z : TopCat.{u}) (B : Set X) (n : ℕ) :
    kunnethSource X Z B n →ₗ[ℚ] kunnethTarget X Z B n :=
  DirectSum.toModule ℚ (bidegree n) _ (fun pq ↦
    (regradeRelative (TopCat.of (X × Z)) (productSubspace X Z B) pq.property).comp
      (crossTensor X Z B pq.val.1 pq.val.2))

/-- Absolute shuffle sends cycles to cycles, Bredon VI pp.316–318.
Proof: apply the published shuffle Leibniz equation to two zero differentials.
In degree zero the native outgoing differential is zero. -/
theorem absoluteShuffle_cycle (X Z : TopCat.{u}) (p q : ℕ)
    (a : cycles (chains X) p) (b : cycles (chains Z) q) :
    ((chains (TopCat.of (X × Z))).dFrom (p + q)).hom
      (SignedShuffle.shuffleBilinear X Z p q a b) = 0 := by
  have hnext (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n <;> simp
  have ha : SignedShuffle.boundary X p a = 0 := by
    change ((chains X).d p (p - 1)).hom a = 0
    rw [← hnext p]
    exact a.property
  have hb : SignedShuffle.boundary Z q b = 0 := by
    change ((chains Z).d q (q - 1)).hom b = 0
    rw [← hnext q]
    exact b.property
  have h := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p q a b
  have hfirst : SignedShuffle.firstBoundaryTerm X Z p q a b = 0 := by
    unfold SignedShuffle.firstBoundaryTerm
    split_ifs <;> simp [ha]
  have hsecond : SignedShuffle.secondBoundaryTerm X Z p q a b = 0 := by
    unfold SignedShuffle.secondBoundaryTerm
    split_ifs <;> simp [hb]
  change ((chains (TopCat.of (X × Z))).d (p + q)
    ((ComplexShape.down ℕ).next (p + q))).hom _ = 0
  rw [hnext]
  simpa only [SignedShuffle.boundary,
    SignedShuffle.shuffle, TensorProduct.lift.tmul, hfirst, hsecond, smul_zero,
    add_zero] using h

/-- The same prescribed shuffle on absolute cycles, Bredon VI pp.316–318. -/
def absoluteCycleShuffle (X Z : TopCat.{u}) (p q : ℕ) :
    cycles (chains X) p →ₗ[ℚ] cycles (chains Z) q →ₗ[ℚ]
      cycles (chains (TopCat.of (X × Z))) (p + q) :=
  LinearMap.mk₂ ℚ (fun a b ↦ ⟨SignedShuffle.shuffleBilinear X Z p q a b,
    absoluteShuffle_cycle X Z p q a b⟩)
    (fun a a' b ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
    (fun a b b' ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))

/-- Absolute cycle classes of the prescribed shuffle, Bredon VI pp.316–318. -/
def absoluteCycleClasses (X Z : TopCat.{u}) (p q : ℕ) :=
  (absoluteCycleShuffle X Z p q).compr₂ (cycleClass (chains (TopCat.of (X × Z))) (p + q))

/-- Absolute boundaries give zero class in either variable, Bredon VI pp.318–320.
Proof: the Leibniz witnesses are α×z and (-1)^p c×ζ, as for the relative law,
now without the quotient-supported term. Their target classes are zero by the
native kernel/image quotient. -/
theorem absoluteShuffle_boundaries (X Z : TopCat.{u}) (p q : ℕ) :
    boundaries (chains X) p ≤ (absoluteCycleClasses X Z p q).ker ∧
    boundaries (chains Z) q ≤ (absoluteCycleClasses X Z p q).flip.ker := by
  constructor
  · intro a ha
    obtain ⟨c, rfl⟩ := ha
    ext b
    let α := ((chains X).xPrevIso (show (ComplexShape.down ℕ).Rel (p + 1) p by simp)).hom c
    have hα : SignedShuffle.boundary X (p + 1) α =
        (((chains X).sc p).moduleCatToCycles c).val := by
      change ((chains X).d (p + 1) p).hom α = ((chains X).dTo p).hom c
      exact (congrArg (fun f ↦ f.hom c)
        ((chains X).dTo_eq (show (ComplexShape.down ℕ).Rel (p + 1) p by simp))).symm
    have hb := signedShuffle_boundary_cycle Z q b
    have hL := (SignedShuffle.signedShuffle_chainMap X Z).2.1 (p + 1) q α b
    have hsecond : SignedShuffle.secondBoundaryTerm X Z (p + 1) q α b = 0 := by
      unfold SignedShuffle.secondBoundaryTerm
      split_ifs <;> simp [hb]
    rw [hsecond, smul_zero, add_zero] at hL
    change cycleClass (chains (TopCat.of (X × Z))) (p + q)
      (absoluteCycleShuffle X Z p q (((chains X).sc p).moduleCatToCycles c) b) = 0
    unfold cycleClass
    change ((chains (TopCat.of (X × Z))).sc (p + q)).moduleCatHomologyIso.inv
      ((boundaries (chains (TopCat.of (X × Z))) (p + q)).mkQ _) = 0
    suffices hz : (boundaries (chains (TopCat.of (X × Z))) (p + q)).mkQ
        (absoluteCycleShuffle X Z p q (((chains X).sc p).moduleCatToCycles c) b) = 0 by
      rw [hz]
      exact map_zero _
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨((chains (TopCat.of (X × Z))).xPrevIso
      (show (ComplexShape.down ℕ).Rel ((p + 1) + q) (p + q) by simp; omega)).inv
        (SignedShuffle.shuffleBilinear X Z (p + 1) q α b), ?_⟩
    apply Subtype.ext
    change ((chains (TopCat.of (X × Z))).dTo (p + q)).hom _ = _
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    simp only [SignedShuffle.firstBoundaryTerm, Nat.add_one_ne_zero, dite_false,
      hα] at hL
    let C := chains (TopCat.of (X × Z))
    have hdeg : p + q = p + 1 + q - 1 := by omega
    let e : C.X (p + 1 + q - 1) ⟶ C.X (p + q) :=
      eqToHom (congrArg C.X hdeg.symm)
    have hd : C.d (p + 1 + q) (p + 1 + q - 1) ≫ e =
        C.d (p + 1 + q) (p + q) :=
      C.d_comp_eqToHom (by simp; omega) (by simp; omega)
    have ht := congrArg (fun v ↦ e.hom v) hL
    change e.hom ((C.d (p + 1 + q) (p + 1 + q - 1)).hom
      (SignedShuffle.shuffleBilinear X Z (p + 1) q α b)) = _ at ht
    rw [← ModuleCat.comp_apply, hd] at ht
    refine ht.trans ?_
    change e.hom (SignedShuffle.regrade (TopCat.of (X × Z)) hdeg
      (SignedShuffle.shuffleBilinear X Z p q
        (((chains X).sc p).moduleCatToCycles c).val b)) = _
    dsimp only [e]
    clear ht hd e
    generalize hm : p + 1 + q - 1 = m at hdeg ⊢
    clear hm
    subst m
    rfl
  · intro b hb
    obtain ⟨c, rfl⟩ := hb
    ext a
    let β := ((chains Z).xPrevIso (show (ComplexShape.down ℕ).Rel (q + 1) q by simp)).hom c
    have hβ : SignedShuffle.boundary Z (q + 1) β =
        (((chains Z).sc q).moduleCatToCycles c).val := by
      change ((chains Z).d (q + 1) q).hom β = ((chains Z).dTo q).hom c
      exact (congrArg (fun f ↦ f.hom c)
        ((chains Z).dTo_eq (show (ComplexShape.down ℕ).Rel (q + 1) q by simp))).symm
    have ha := signedShuffle_boundary_cycle X p a
    have hL := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p (q + 1) a β
    have hfirst : SignedShuffle.firstBoundaryTerm X Z p (q + 1) a β = 0 := by
      unfold SignedShuffle.firstBoundaryTerm
      split_ifs <;> simp [ha]
    rw [hfirst, zero_add] at hL
    change cycleClass (chains (TopCat.of (X × Z))) (p + q)
      (absoluteCycleShuffle X Z p q a (((chains Z).sc q).moduleCatToCycles c)) = 0
    unfold cycleClass
    change ((chains (TopCat.of (X × Z))).sc (p + q)).moduleCatHomologyIso.inv
      ((boundaries (chains (TopCat.of (X × Z))) (p + q)).mkQ _) = 0
    suffices hz : (boundaries (chains (TopCat.of (X × Z))) (p + q)).mkQ
        (absoluteCycleShuffle X Z p q a (((chains Z).sc q).moduleCatToCycles c)) = 0 by
      rw [hz]
      exact map_zero _
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨((chains (TopCat.of (X × Z))).xPrevIso
      (show (ComplexShape.down ℕ).Rel (p + (q + 1)) (p + q) by simp; omega)).inv
        ((-1 : ℚ) ^ p • SignedShuffle.shuffleBilinear X Z p (q + 1) a β), ?_⟩
    apply Subtype.ext
    change ((chains (TopCat.of (X × Z))).dTo (p + q)).hom _ = _
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo, map_smul]
    simp only [SignedShuffle.secondBoundaryTerm, Nat.add_one_ne_zero, dite_false, hβ] at hL
    let C := chains (TopCat.of (X × Z))
    have hdeg : p + q = p + (q + 1) - 1 := by omega
    let e : C.X (p + (q + 1) - 1) ⟶ C.X (p + q) :=
      eqToHom (congrArg C.X hdeg.symm)
    have hd : C.d (p + (q + 1)) (p + (q + 1) - 1) ≫ e =
        C.d (p + (q + 1)) (p + q) :=
      C.d_comp_eqToHom (by simp; omega) (by simp; omega)
    have ht := congrArg (fun v ↦ e.hom v) hL
    change e.hom ((C.d (p + (q + 1)) (p + (q + 1) - 1)).hom
      (SignedShuffle.shuffleBilinear X Z p (q + 1) a β)) = _ at ht
    rw [← ModuleCat.comp_apply, hd] at ht
    rw [ht, map_smul, smul_smul]
    simp only [← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    change e.hom (SignedShuffle.regrade (TopCat.of (X × Z)) hdeg
      (SignedShuffle.shuffleBilinear X Z p q a
        (((chains Z).sc q).moduleCatToCycles c).val)) = _
    dsimp only [e]
    clear ht hd e
    generalize hm : p + (q + 1) - 1 = m at hdeg ⊢
    clear hm
    subst m
    rfl

/-- The actual canonical absolute rational cross product, Bredon VI pp.316–320. -/
def absoluteCrossTensor (X Z : TopCat.{u}) (p q : ℕ) :
    TensorProduct ℚ (homology X p) (homology Z q) →ₗ[ℚ]
      homology (TopCat.of (X × Z)) (p + q) :=
  quotientTensor _ _ _ p q (p + q) (absoluteCycleClasses X Z p q)
    (absoluteShuffle_boundaries X Z p q).1 (absoluteShuffle_boundaries X Z p q).2

/-- Pure absolute classes for the same prescribed product, Bredon VI pp.316–320. -/
def absoluteCross (X Z : TopCat.{u}) (p q : ℕ) (a : homology X p) (b : homology Z q) :
    homology (TopCat.of (X × Z)) (p + q) :=
  absoluteCrossTensor X Z p q (a ⊗ₜ[ℚ] b)

/-- The actual absolute-to-relative diagonal map, induced by the quotient chain map.
Source: Bredon IV16.1 and VI p.320. -/
def homologyProjection (X : TopCat.{u}) (B : Set X) (n : ℕ) :
    homology X n →ₗ[ℚ] relativeHomology X B n :=
  (HomologicalComplex.homologyMap (chainProjection X B) n).hom

/-- The literal second-factor relative product subspace, Bredon VI §3 pp.324–325. -/
def rightProductSubspace (X Z : TopCat.{u}) (B : Set Z) : Set (X × Z) := {w | w.2 ∈ B}

/-- The prescribed shuffle projected onto the second-factor relative target and flipped
solely to apply the native cokernel in its first input. Source: Bredon VI p.320. -/
def rightProjectedFlip (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :=
  ((SignedShuffle.shuffleBilinear X Z p q).compr₂
    ((chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)).hom).flip

/-- Second-factor support vanishes in the actual product quotient, Bredon IV16.1/VI p.320.
Proof: every simplex in each signed staircase has second coordinate in B if its
second input simplex is in B. The target cokernel annihilates its inclusion. Extend
on both rational free bases. No open-subspace assumption is needed for this law. -/
theorem rightShuffle_subspace_vanish (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :
    (SSet.chainComplexMap (pair Z B).hom coefficients).f q ≫
      ModuleCat.ofHom (rightProjectedFlip X Z B p q) = 0 := by
  let inc : C(B, Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(X × B, rightProductSubspace X Z B) :=
    ⟨fun w ↦ ⟨(w.1, w.2.val), w.2.property⟩,
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hf : TopCat.ofHom ((ContinuousMap.id X).prodMap inc) =
      TopCat.ofHom j ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
    ext w : 1
    rfl
  have hz (c : (chains (TopCat.of (X × B))).X (p + q)) :
      (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
        (SignedShuffle.pushforward ((ContinuousMap.id X).prodMap inc) (p + q) c) = 0 := by
    have h := (pair (TopCat.of (X × Z)) (rightProductSubspace X Z B)).chainComplex_condition_f
      coefficients (p + q)
    have hh := congrArg (fun f ↦ f.hom
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j))
        coefficients).f (p + q) c)) h
    change ((pair (TopCat.of (X × Z)) (rightProductSubspace X Z B)).chainComplexπ
      coefficients).f (p + q)
        ((SSet.chainComplexMap (pair (TopCat.of (X × Z))
          (rightProductSubspace X Z B)).hom coefficients).f (p + q)
          ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j))
            coefficients).f (p + q) c)) = 0 at hh
    have hc : SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ((ContinuousMap.id X).prodMap inc)))
        coefficients =
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom j)) coefficients ≫
          SSet.chainComplexMap (TopCat.toSSet.map
            (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
              C(rightProductSubspace X Z B, X × Z)))) coefficients := by
      dsimp only [SSet.chainComplexMap]
      rw [hf, Functor.map_comp, Functor.map_comp]
    change (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ((ContinuousMap.id X).prodMap inc)))
        coefficients).f (p + q) c) = 0
    rw [hc]
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    exact hh
  ext b a
  change (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
    (SignedShuffle.shuffleBilinear X Z p q a (SignedShuffle.pushforward inc q b)) = 0
  have hn := (SignedShuffle.signedShuffle_chainMap X (TopCat.of B)).2.2.1
    X Z (ContinuousMap.id X) inc p q a b
  have hid : SignedShuffle.pushforward (ContinuousMap.id X) p a = a := by
    simp [SignedShuffle.pushforward, SSet.chainComplexMap]
  rw [hid] at hn
  change SignedShuffle.pushforward ((ContinuousMap.id X).prodMap inc) (p + q)
      (SignedShuffle.shuffleBilinear X (TopCat.of B) p q a b) =
    SignedShuffle.shuffleBilinear X Z p q a (SignedShuffle.pushforward inc q b) at hn
  rw [← hn]
  exact hz _

/-- Concrete CHAIN quotient descent in the second factor, Bredon VI p.320. -/
def rightShuffle (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :
    (chains X).X p →ₗ[ℚ] (relativeChains Z B).X q →ₗ[ℚ]
      (relativeChains (TopCat.of (X × Z)) (rightProductSubspace X Z B)).X (p + q) :=
  ((CokernelCofork.IsColimit.desc'
    ((pair Z B).isColimitCokernelCoforkChainComplexX coefficients q)
    (ModuleCat.ofHom (rightProjectedFlip X Z B p q))
    (rightShuffle_subspace_vanish X Z B p q)).val.hom).flip

/-- The second-factor cokernel descent evaluates on the original projection.
Source: the native cokernel universal property, Bredon VI p.320. -/
@[simp] theorem rightShuffle_projection (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ)
    (a : (chains X).X p) (b : (chains Z).X q) :
    rightShuffle X Z B p q a ((chainProjection Z B).f q b) =
      (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
        (SignedShuffle.shuffleBilinear X Z p q a b) := by
  have h := (CokernelCofork.IsColimit.desc'
    ((pair Z B).isColimitCokernelCoforkChainComplexX coefficients q)
    (ModuleCat.ofHom (rightProjectedFlip X Z B p q))
    (rightShuffle_subspace_vanish X Z B p q)).property
  exact congrArg (fun f ↦ f.hom b a) h

/-- The second-factor descended chain product sends cycles to cycles, Bredon VI p.320.
Proof: choose an absolute chain representative of the second relative cycle; its
boundary comes from B. The signed Leibniz second term is then supported in X×B,
and the first term vanishes because its input is an absolute cycle. Pass through
the actual quotient chain map. At degree zero the outgoing native differential is zero. -/
theorem rightShuffle_cycle (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ)
    (a : cycles (chains X) p) (b : cycles (relativeChains Z B) q) :
    ((relativeChains (TopCat.of (X × Z)) (rightProductSubspace X Z B)).dFrom (p + q)).hom
      (rightShuffle X Z B p q a b) = 0 := by
  apply (dFrom_apply_eq_zero_iff_pred _ (p + q) _).mpr
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection Z B).f q)).mp
    (Cofork.IsColimit.epi
      ((pair Z B).isColimitCokernelCoforkChainComplexX coefficients q))
    (b : (relativeChains Z B).X q)
  have hdb : (chainProjection Z B).f (q - 1) (SignedShuffle.boundary Z q c) = 0 := by
    have hcomm := congrArg (fun f ↦ f.hom c) ((chainProjection Z B).comm q (q - 1))
    change (relativeChains Z B).d q (q - 1) ((chainProjection Z B).f q c) =
      (chainProjection Z B).f (q - 1) (SignedShuffle.boundary Z q c) at hcomm
    rw [← hcomm, hc]
    exact (dFrom_apply_eq_zero_iff_pred (relativeChains Z B) q b).mp b.property
  have hfirst : SignedShuffle.firstBoundaryTerm X Z p q a c = 0 := by
    simp [SignedShuffle.firstBoundaryTerm, signedShuffle_boundary_cycle X p a]
  have hsecond :
      (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q - 1)
        (SignedShuffle.secondBoundaryTerm X Z p q a c) = 0 := by
    unfold SignedShuffle.secondBoundaryTerm
    split_ifs with hq
    · exact map_zero _
    · apply chainProjection_regrade_eq_zero
      rw [← rightShuffle_projection, hdb]
      simp
  have hLeibniz := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p q a c
  change SignedShuffle.boundary (TopCat.of (X × Z)) (p + q)
      (SignedShuffle.shuffleBilinear X Z p q a c) =
    SignedShuffle.firstBoundaryTerm X Z p q a c +
      (-1 : ℚ) ^ p • SignedShuffle.secondBoundaryTerm X Z p q a c at hLeibniz
  rw [← hc, rightShuffle_projection]
  have hcomm := congrArg (fun f ↦ f.hom (SignedShuffle.shuffleBilinear X Z p q a c))
    ((chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).comm
      (p + q) (p + q - 1))
  change (relativeChains (TopCat.of (X × Z)) (rightProductSubspace X Z B)).d
      (p + q) (p + q - 1)
      ((chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
        (SignedShuffle.shuffleBilinear X Z p q a c)) =
    (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q - 1)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q)
        (SignedShuffle.shuffleBilinear X Z p q a c)) at hcomm
  rw [hcomm, hLeibniz, hfirst, zero_add, map_smul, hsecond, smul_zero]

/-- Cycle-valued shuffle with the second input relative, Bredon VI pp.320,324–325. -/
def rightCycleShuffle (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :
    cycles (chains X) p →ₗ[ℚ] cycles (relativeChains Z B) q →ₗ[ℚ]
      cycles (relativeChains (TopCat.of (X × Z)) (rightProductSubspace X Z B)) (p + q) :=
  LinearMap.mk₂ ℚ (fun a b ↦ ⟨rightShuffle X Z B p q a b,
    rightShuffle_cycle X Z B p q a b⟩)
    (fun a a' b ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
    (fun a b b' ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))

/-- Actual second-relative cycle classes, Bredon VI p.320. -/
def rightCycleClasses (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :=
  (rightCycleShuffle X Z B p q).compr₂
    (cycleClass (relativeChains (TopCat.of (X × Z)) (rightProductSubspace X Z B)) (p + q))

set_option backward.isDefEq.respectTransparency false in
/-- Boundaries annihilation for the second-relative shuffle, Bredon VI pp.318–320.
Proof: use the witnesses α×z and (-1)^p c×ζ in the actual quotient. The extra term
whose relative input differential is supported in B disappears in X×B. Therefore
both products are native target boundaries. This includes all degree-zero cases. -/
theorem rightShuffle_boundaries (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :
    boundaries (chains X) p ≤ (rightCycleClasses X Z B p q).ker ∧
    boundaries (relativeChains Z B) q ≤ (rightCycleClasses X Z B p q).flip.ker := by
  have hzero (C : ChainComplex (ModuleCat.{u} ℚ) ℕ) (k : ℕ)
      (c : cycles C k) (x : C.X (k + 1)) (hx : (C.d (k + 1) k).hom x = c.val) :
      cycleClass C k c = 0 :=
    moduleCatHomologyClass_eq_zero_of_boundary C (k + 1) k rfl c ⟨x, hx⟩
  have hcompose (W : TopCat.{u}) {i j k : ℕ} (hij : i = j) (hjk : j = k)
      (c : SignedShuffle.Chain W i) :
      SignedShuffle.regrade W hjk (SignedShuffle.regrade W hij c) =
        SignedShuffle.regrade W (hij.trans hjk) c := by
    subst j
    subst k
    rfl
  have hcomm (W : TopCat.{u}) (D : Set W) (i j : ℕ) (c : (chains W).X i) :
      (relativeChains W D).d i j ((chainProjection W D).f i c) =
        (chainProjection W D).f j ((chains W).d i j c) :=
    ConcreteCategory.congr_hom ((chainProjection W D).comm i j) c
  constructor
  · intro a ha
    apply LinearMap.mem_ker.mpr
    ext b
    obtain ⟨x, hx⟩ := moduleCatBoundary_exists_successor (chains X) p a ha
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection Z B).f q)).mp
      (Cofork.IsColimit.epi
        ((pair Z B).isColimitCokernelCoforkChainComplexX coefficients q)) b.val
    have hdb : (chainProjection Z B).f (q - 1) (SignedShuffle.boundary Z q c) = 0 := by
      rw [SignedShuffle.boundary, ← hcomm, hc]
      exact (dFrom_apply_eq_zero_iff_pred (relativeChains Z B) q b).mp b.property
    change cycleClass _ _ (rightCycleShuffle X Z B p q a b) = 0
    let w := SignedShuffle.regrade (TopCat.of (X × Z))
      (by omega : p + 1 + q = p + q + 1)
      (SignedShuffle.shuffleBilinear X Z (p + 1) q x c)
    apply hzero _ _ _ ((chainProjection _ _).f (p + q + 1) w)
    rw [hcomm]
    have h := (SignedShuffle.signedShuffle_chainMap X Z).2.1 (p + 1) q x c
    simp only [SignedShuffle.shuffle, TensorProduct.lift.tmul] at h
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q + 1) w) = _
    rw [SignedShuffle.boundary_regrade, h, map_add, map_smul, map_add, map_smul]
    have hz : (chainProjection (TopCat.of (X × Z)) (rightProductSubspace X Z B)).f (p + q)
        (SignedShuffle.regrade (TopCat.of (X × Z))
          (by omega : p + 1 + q - 1 = p + q)
          (SignedShuffle.secondBoundaryTerm X Z (p + 1) q x c)) = 0 := by
      apply chainProjection_regrade_eq_zero
      unfold SignedShuffle.secondBoundaryTerm
      split_ifs with hq
      · exact map_zero _
      · apply chainProjection_regrade_eq_zero
        rw [← rightShuffle_projection, hdb]
        simp
    erw [hz, smul_zero, add_zero]
    simp only [SignedShuffle.firstBoundaryTerm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceDIte]
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.regrade (TopCat.of (X × Z)) _
        (SignedShuffle.regrade (TopCat.of (X × Z)) _
          (SignedShuffle.shuffleBilinear X Z p q ((chains X).d (p + 1) p x) c))) = _
    rw [hcompose]
    change (chainProjection _ _).f (p + q)
      (SignedShuffle.shuffleBilinear X Z p q ((chains X).d (p + 1) p x) c) = _
    rw [hx, ← rightShuffle_projection, hc]
    rfl
  · intro b hb
    apply LinearMap.mem_ker.mpr
    ext a
    obtain ⟨x, hx⟩ := moduleCatBoundary_exists_successor (relativeChains Z B) q b hb
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection Z B).f (q + 1))).mp
      (Cofork.IsColimit.epi
        ((pair Z B).isColimitCokernelCoforkChainComplexX coefficients (q + 1))) x
    change cycleClass _ _ (rightCycleShuffle X Z B p q a b) = 0
    let w := SignedShuffle.regrade (TopCat.of (X × Z))
      (by omega : p + (q + 1) = p + q + 1)
      (SignedShuffle.shuffleBilinear X Z p (q + 1) a c)
    apply hzero _ _ _ ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q + 1) w)
    rw [map_smul, hcomm]
    have h := (SignedShuffle.signedShuffle_chainMap X Z).2.1 p (q + 1) a c
    simp only [SignedShuffle.shuffle, TensorProduct.lift.tmul] at h
    have ha := signedShuffle_boundary_cycle X p a
    have hz : SignedShuffle.firstBoundaryTerm X Z p (q + 1) a c = 0 := by
      unfold SignedShuffle.firstBoundaryTerm
      split_ifs <;> simp only [ha, map_zero, LinearMap.zero_apply]
    rw [hz, zero_add] at h
    change (-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.boundary (TopCat.of (X × Z)) (p + q + 1) w) = _
    rw [SignedShuffle.boundary_regrade, h, map_smul, map_smul]
    simp only [SignedShuffle.secondBoundaryTerm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceDIte]
    change (-1 : ℚ) ^ p • ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.regrade (TopCat.of (X × Z)) _
        (SignedShuffle.regrade (TopCat.of (X × Z)) _
          (SignedShuffle.shuffleBilinear X Z p q a ((chains Z).d (q + 1) q c))))) = _
    rw [hcompose]
    change (-1 : ℚ) ^ p • ((-1 : ℚ) ^ p • (chainProjection _ _).f (p + q)
      (SignedShuffle.shuffleBilinear X Z p q a ((chains Z).d (q + 1) q c))) = _
    rw [smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul]
    rw [← rightShuffle_projection, ← hcomm, hc, hx]
    rfl

/-- Canonical second-relative product of the same signed shuffle, Bredon VI p.320. -/
def rightCrossTensor (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ) :
    TensorProduct ℚ (homology X p) (relativeHomology Z B q) →ₗ[ℚ]
      relativeHomology (TopCat.of (X × Z)) (rightProductSubspace X Z B) (p + q) :=
  quotientTensor _ _ _ p q (p + q) (rightCycleClasses X Z B p q)
    (rightShuffle_boundaries X Z B p q).1 (rightShuffle_boundaries X Z B p q).2

/-- Pure classes for the genuine second-relative product, Bredon VI p.320. -/
def rightCross (X Z : TopCat.{u}) (B : Set Z) (p q : ℕ)
    (a : homology X p) (b : relativeHomology Z B q) :
    relativeHomology (TopCat.of (X × Z)) (rightProductSubspace X Z B) (p + q) :=
  rightCrossTensor X Z B p q (a ⊗ₜ[ℚ] b)

/-- The second-relative total-degree source, Bredon VI p.320. -/
abbrev rightKunnethSource (X Z : TopCat.{u}) (B : Set Z) (n : ℕ) :=
  DirectSum (bidegree n) (fun pq ↦
    TensorProduct ℚ (homology X pq.val.1) (relativeHomology Z B pq.val.2))

/-- Total-degree second-relative shuffle map, Bredon VI p.320. -/
def rightKunnethMap (X Z : TopCat.{u}) (B : Set Z) (n : ℕ) :
    rightKunnethSource X Z B n →ₗ[ℚ]
      relativeHomology (TopCat.of (X × Z)) (rightProductSubspace X Z B) n :=
  DirectSum.toModule ℚ (bidegree n) _ (fun pq ↦
    (regradeRelative (TopCat.of (X × Z)) (rightProductSubspace X Z B) pq.property).comp
      (rightCrossTensor X Z B pq.val.1 pq.val.2))

/-- Actual coordinate transposition, Bredon VI §3 pp.324–325. -/
def swapMap (X Z : TopCat.{u}) : TopCat.of (X × Z) ⟶ TopCat.of (Z × X) :=
  TopCat.ofHom ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩

/-- Actual product associator on original point carriers, Bredon VI pp.316–320. -/
def associatorMap (X Z W : TopCat.{u}) :
    TopCat.of ((X × Z) × W) ⟶ TopCat.of (X × (Z × W)) :=
  TopCat.ofHom ⟨fun v ↦ (v.1.1, (v.1.2, v.2)),
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)⟩

/-- A degree-zero point generator is a native cycle, Bredon VI pp.316–320.
Proof: Mathlib's natural-number chain complex has zero outgoing differential at 0;
apply it to the actual singular point generator. This is ordinary H0, not reduced H0. -/
theorem pointGenerator_cycle (X : TopCat.{u}) (x : X) :
    ((chains X).dFrom 0).hom
      (SignedShuffle.generator X (SignedShuffle.pointSimplex X x)) = 0 := by
  simp [HomologicalComplex.dFrom, ComplexShape.down_Rel]

/-- The actual ordinary H0 point class, Bredon VI pp.316–320. -/
def pointClass (X : TopCat.{u}) (x : X) : homology X 0 :=
  cycleClass (chains X) 0
    ⟨SignedShuffle.generator X (SignedShuffle.pointSimplex X x), pointGenerator_cycle X x⟩

/-- Insert an actual point as the second coordinate, Bredon VI pp.316–320. -/
def insertPoint (X Z : TopCat.{u}) (z : Z) : X ⟶ TopCat.of (X × Z) :=
  TopCat.ofHom ⟨fun x ↦ (x, z), continuous_id.prodMk continuous_const⟩

/-- Insert an actual point as the first coordinate, Bredon VI pp.316–320. -/
def insertPointLeft (X Z : TopCat.{u}) (x : X) : Z ⟶ TopCat.of (X × Z) :=
  TopCat.ofHom ⟨fun z ↦ (x, z), continuous_const.prodMk continuous_id⟩

/-- The zero-total-degree summand is exactly (0,0), with positive sign.
Source: Bredon VI Theorem1.5 p.320. -/
def degreeZeroSummand : bidegree 0 := ⟨(0, 0), rfl⟩

/-- Total-degree naturality in the literal labelled direct sum, Bredon VI p.320. -/
def sourceMap {X X' Z Z' : TopCat.{u}} (B : Set X) (D : Set X')
    (f : X ⟶ X') (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (n : ℕ) :
    kunnethSource X Z B n →ₗ[ℚ] kunnethSource X' Z' D n :=
  DirectSum.toModule ℚ (bidegree n) _ (fun pq ↦
    (DirectSum.lof ℚ (bidegree n) _ pq).comp
      (TensorProduct.map (relativeMap B D f hf pq.val.1).hom (homologyMap g pq.val.2).hom))

/-- The literal continuous diagonal, Bredon IV16.1 and VI product naturality. -/
def diagonalMap (X : TopCat.{u}) : X ⟶ TopCat.of (X × X) :=
  TopCat.ofHom ⟨fun x ↦ (x, x), continuous_id.prodMk continuous_id⟩

/-- The actual product map of pairs on target homology, Bredon VI product naturality. -/
def targetMap {X X' Z Z' : TopCat.{u}} (B : Set X) (D : Set X')
    (f : X ⟶ X') (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (n : ℕ) :
    kunnethTarget X Z B n →ₗ[ℚ] kunnethTarget X' Z' D n :=
  (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (X' × Z'))
    (productSubspace X Z B) (productSubspace X' Z' D)
    (productMap f g) (fun _ hw ↦ hf hw) n).hom

/-- A chain map identified with a homotopy equivalence induces a bijection on native homology.
This is the concrete homology-level consequence used when the relative Eilenberg--Zilber
comparison is specialized to the quotient pair. -/
theorem homologyMap_bijective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat.{u} ℚ) ℕ} (f : C ⟶ D)
    (e : HomotopyEquiv C D) (he : e.hom = f) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap f n).hom := by
  have hh : HomologicalComplex.homologyMap e.hom n =
      HomologicalComplex.homologyMap f n := by
    rw [he]
  rw [← hh]
  exact ConcreteCategory.bijective_of_isIso _

/-- The scalar-transport comparison is degreewise bijective on native relative chains.
This is the carrier-level part of transporting the lifted Eilenberg--Zilber comparison
back to the module-valued rational pair used here. -/
theorem nativeRelativeChainComparison_bijective
    (P : SSetPair.{u}) (n : ℕ) :
    Function.Bijective
      ((((HolomorphicAnosov.RationalScalarTransport.nativeRelativeChainComparison P).hom.f n).hom)) := by
  exact ConcreteCategory.bijective_of_isIso _

/-- Scalar transport is also bijective on the corresponding native relative homology.
This records the homology-level carrier equivalence needed before comparing the
transported EZ map with the native cross product. -/
theorem relativeHomologyComparison_bijective
    (P : SSetPair.{u}) (n : ℕ) :
    Function.Bijective
      ((HolomorphicAnosov.RationalScalarTransport.relativeHomologyComparison P n).hom) := by
  exact ConcreteCategory.bijective_of_isIso _

/-- The canonical field Künneth map is bijective whenever the field provider
returns its representative-compatible linear equivalence. This identifies the
provider's abstract witness with the concrete map used by the relative module. -/
theorem field_kunnethMap_bijective
    {K : Type u} [Field K]
    (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    Function.Bijective
      (HolomorphicAnosov.FieldTensorHomologyKunneth.kunnethMap C D n) := by
  obtain ⟨κ, hrep, _⟩ :=
    HolomorphicAnosov.FieldTensorHomologyKunneth.field_chain_tensor_homology_kunneth_same_universe (K := K)
  have heq : HolomorphicAnosov.FieldTensorHomologyKunneth.kunnethMap C D n = (κ C D n).toLinearMap := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, hpq⟩
    apply TensorProduct.ext'
    intro a b
    obtain ⟨c, rfl⟩ := (HolomorphicAnosov.FieldChainKronecker.boundaries C p).mkQ_surjective a
    obtain ⟨d, rfl⟩ := (HolomorphicAnosov.FieldChainKronecker.boundaries D q).mkQ_surjective b
    change HolomorphicAnosov.FieldTensorHomologyKunneth.kunnethMap C D n (DirectSum.lof K (HolomorphicAnosov.FieldTensorHomologyKunneth.degreePairs n) _ ⟨(p, q), hpq⟩
      ((HolomorphicAnosov.FieldChainKronecker.cycleClass C p c) ⊗ₜ[K] (HolomorphicAnosov.FieldChainKronecker.cycleClass D q d))) = _
    rw [HolomorphicAnosov.FieldTensorHomologyKunneth.kunnethMap_representative]
    exact (hrep C D n p q hpq c d).symm
  rw [heq]
  exact (κ C D n).bijective

/-- The degreewise Koszul transposition on tensor products is a linear bijection.
Its pure-tensor formula is the exact `(-1)^(pq)` coefficient used by Bredon’s
coordinate-swap law. -/
def koszulFlip (p q : ℕ) (M N : ModuleCat.{u} ℚ) :
    M ⊗[ℚ] N →ₗ[ℚ] N ⊗[ℚ] M :=
  (-1 : ℚ) ^ (p * q) • (TensorProduct.comm ℚ M N)

theorem koszulFlip_bijective (p q : ℕ) (M N : ModuleCat.{u} ℚ) :
    Function.Bijective (koszulFlip p q M N) := by
  let e := TensorProduct.comm ℚ M N
  have hs : (-1 : ℚ) ^ (p * q) ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro a b h
    apply e.injective
    change ((-1 : ℚ) ^ (p*q)) • e a = ((-1 : ℚ) ^ (p*q)) • e b at h
    exact (smul_right_injective _ hs) h
  · intro y
    refine ⟨((-1 : ℚ) ^ (p*q))⁻¹ • e.symm y, ?_⟩
    simp [koszulFlip, e, hs]

theorem koszulFlip_tmul (p q : ℕ) (M N : ModuleCat.{u} ℚ) (a : M) (b : N) :
    koszulFlip p q M N (a ⊗ₜ[ℚ] b) =
      (-1 : ℚ) ^ (p*q) • (b ⊗ₜ[ℚ] a) := by
  simp [koszulFlip]

theorem koszulFlip_involutive (p q : ℕ) (M N : ModuleCat.{u} ℚ)
    (x : M ⊗[ℚ] N) :
    koszulFlip q p N M (koszulFlip p q M N x) = x := by
  simp only [koszulFlip, LinearMap.smul_apply, map_smul, smul_smul]
  rw [Nat.mul_comm q p, ← mul_pow]
  norm_num

/-- The three-factor tensor associator is a linear bijection with the expected
pure-tensor value. This is the algebraic carrier identity behind shuffle
associativity under the product associator. -/
def tensorAssoc (M N P : ModuleCat.{u} ℚ) :
    (M ⊗[ℚ] N) ⊗[ℚ] P →ₗ[ℚ] M ⊗[ℚ] (N ⊗[ℚ] P) :=
  (TensorProduct.assoc ℚ M N P).toLinearMap

theorem tensorAssoc_bijective (M N P : ModuleCat.{u} ℚ) :
    Function.Bijective (tensorAssoc M N P) := by
  exact (TensorProduct.assoc ℚ M N P).bijective

theorem tensorAssoc_tmul (M N P : ModuleCat.{u} ℚ) (a : M) (b : N) (c : P) :
    tensorAssoc M N P ((a ⊗ₜ[ℚ] b) ⊗ₜ[ℚ] c) = a ⊗ₜ[ℚ] (b ⊗ₜ[ℚ] c) := by
  exact TensorProduct.assoc_tmul a b c

/-- Coordinate transposition is involutive on the literal product carriers.
This carrier identity is the topological part of the residual swap law. -/
theorem swapMap_involutive (X Z : TopCat.{u}) :
    swapMap Z X ≫ swapMap X Z = 𝟙 (TopCat.of (Z × X)) := by
  ext w <;> rfl

/-- The literal product transposition preserves the first-relative support guard. -/
theorem swapMap_mapsTo (X Z : TopCat.{u}) (B : Set X) :
    Set.MapsTo (swapMap X Z) (productSubspace X Z B)
      (rightProductSubspace Z X B) := by
  intro w hw
  exact hw

/-- The literal product associator preserves the first-relative support guard. -/
theorem associatorMap_mapsTo (X Z W : TopCat.{u}) (B : Set X) :
    Set.MapsTo (associatorMap X Z W)
      (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
      (productSubspace X (TopCat.of (Z × W)) B) := by
  intro w hw
  exact hw

/-- The reverse coordinate transposition preserves the second-relative support guard. -/
theorem swapMap_mapsTo_reverse (X Z : TopCat.{u}) (B : Set X) :
    Set.MapsTo (swapMap Z X) (rightProductSubspace Z X B)
      (productSubspace X Z B) := by
  intro w hw
  exact hw

open RationalScalarTransport NativeRelativeShuffleComparison SingularEilenbergZilber in
/-- The transported native comparison sends a tensor of actual relative and absolute
cycles to their prescribed relative shuffle class. Source: Bredon VI p.320.
Lift the relative chain through the quotient (without assuming its lift is a cycle),
apply the projected pure-tensor calculation, then use cycle-class naturality. -/
theorem transported_tensor_cycleClass (X Z : TopCat.{u}) (B : Set X)
    (e : HomotopyEquiv
      (HomologicalComplex.tensorObj (relativeComplex X B) (chainFunctor.obj Z))
      (relativeComplex (TopCat.of (X × Z)) (productSupport X Z B)))
    (he : HomologicalComplex.tensorHom
      ((nativePair X B).chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}))
      (𝟙 (chainFunctor.obj Z)) ≫ e.hom =
      shuffleChainMap X Z ≫
        (nativePair (TopCat.of (X × Z)) (productSupport X Z B)).chainComplexπ
          (ModuleCat.of LiftQ.{u} LiftQ.{u}))
    (p q : ℕ) (a : cycles (relativeChains X B) p) (b : cycles (chains Z) q) :
    (HomologicalComplex.homologyMap
      (RationalRelativeTensorComparison.transportNativeEquivalence X Z B e).hom (p+q)).hom
      (cycleClass _ (p+q)
        (FieldTensorHomologyKunneth.ArbitraryUniverse.tensorCycle
          (relativeChains X B) (chains Z) p q (p+q) rfl a b)) =
    cross X Z B p q (cycleClass _ p a) (cycleClass _ q b) := by
  unfold cross crossTensor
  rw [quotientTensor_cycleClass]
  apply cycleClass_map
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
    (Cofork.IsColimit.epi
      ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
  change (RationalRelativeTensorComparison.transportNativeEquivalence X Z B e).hom.f (p+q)
    (FieldTensorHomologyKunneth.ArbitraryUniverse.tensorChain
      (relativeChains X B) (chains Z) p q (p+q) rfl a.val b.val) =
    relativeShuffle X Z B p q a.val b.val
  rw [← hc, relativeShuffle_projection]
  exact RationalRelativeTensorComparison.transportNativeEquivalence_projected_tensor
    X Z B e he p q c b.val

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical relative shuffle Künneth map is bijective. Source: Bredon VI
Theorem 1.5 and the one-relative-factor argument, pp.318–320. Compose the algebraic
field tensor-homology equivalence with the native relative shuffle comparison.
Their values on tensor cycle classes are the prescribed cross products, so tensor
and direct-sum generation identify this composite with the defined Künneth map. -/
theorem kunnethMap_bijective (X Z : TopCat.{u}) (B : Set X) (n : ℕ) :
    Function.Bijective (kunnethMap X Z B n) := by
  classical
  obtain ⟨e, he⟩ :=
    NativeRelativeShuffleComparison.native_relative_shuffle_homotopy_equiv X Z B
  let E := RationalRelativeTensorComparison.transportNativeEquivalence X Z B e
  let C := relativeChains X B
  let D := chains Z
  let T := FieldTensorHomologyKunneth.ArbitraryUniverse.totalComplex.{0,u} C D
  obtain ⟨κ, hκ, _⟩ :=
    FieldTensorHomologyKunneth.field_chain_tensor_homology_kunneth.{0,u} (K := ℚ)
  let S : kunnethSource X Z B n ≃ₗ[ℚ]
      FieldTensorHomologyKunneth.ArbitraryUniverse.homologyTensorSum.{0,u} C D n :=
    DirectSum.congrLinearEquiv fun pq ↦
      TensorProduct.congr ((C.sc pq.val.1).moduleCatHomologyIso.toLinearEquiv)
        ((D.sc pq.val.2).moduleCatHomologyIso.toLinearEquiv)
  let U := (T.sc n).moduleCatHomologyIso.symm.toLinearEquiv
  let F : kunnethSource X Z B n →ₗ[ℚ] kunnethTarget X Z B n :=
    (HomologicalComplex.homologyMap E.hom n).hom.comp
      (U.toLinearMap.comp ((κ C D n).toLinearMap.comp S.toLinearMap))
  have hF : Function.Bijective F :=
    (homologyMap_bijective_of_homotopyEquiv E.hom E rfl n).comp
      (U.bijective.comp ((κ C D n).bijective.comp S.bijective))
  have hclass (V : ChainComplex (ModuleCat.{u} ℚ) ℕ) (j : ℕ) (a : cycles V j) :
      (V.sc j).moduleCatHomologyIso.hom (cycleClass V j a) =
        FieldChainKronecker.cycleClass V j a := by
    exact Iso.inv_hom_id_apply (V.sc j).moduleCatHomologyIso _
  have hmap : kunnethMap X Z B n = F := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩, hpq⟩
    apply TensorProduct.ext'
    intro a b
    obtain ⟨a, rfl⟩ := cycleClass_surjective C p a
    obtain ⟨b, rfl⟩ := cycleClass_surjective D q b
    subst n
    change kunnethMap X Z B (p+q)
      (DirectSum.lof ℚ (bidegree (p+q)) _ ⟨(p,q),rfl⟩
        (cycleClass C p a ⊗ₜ[ℚ] cycleClass D q b)) = _
    simp only [kunnethMap, DirectSum.toModule_lof, LinearMap.comp_apply]
    change cross X Z B p q (cycleClass C p a) (cycleClass D q b) =
      (HomologicalComplex.homologyMap E.hom (p+q)).hom
        (U (κ C D (p+q) (S (DirectSum.lof ℚ (bidegree (p+q)) _ ⟨(p,q),rfl⟩
          (cycleClass C p a ⊗ₜ[ℚ] cycleClass D q b)))))
    simp only [S, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
      LinearEquiv.coe_coe, TensorProduct.congr_tmul]
    change cross X Z B p q (cycleClass C p a) (cycleClass D q b) =
      (HomologicalComplex.homologyMap E.hom (p+q)).hom
        (U (κ C D (p+q) (DirectSum.lof ℚ (bidegree (p+q)) _ ⟨(p,q),rfl⟩
          (((C.sc p).moduleCatHomologyIso.hom (cycleClass C p a)) ⊗ₜ[ℚ]
            ((D.sc q).moduleCatHomologyIso.hom (cycleClass D q b))))))
    erw [hclass C p a, hclass D q b]
    have hk := hκ C D (p+q) p q rfl a b
    have hh := congrArg (fun x ↦ (HomologicalComplex.homologyMap E.hom (p+q)).hom (U x)) hk
    have hU (c : cycles T (p+q)) : U (FieldChainKronecker.cycleClass T (p+q) c) =
        cycleClass T (p+q) c := rfl
    change _ = (HomologicalComplex.homologyMap E.hom (p+q)).hom
      (U (FieldChainKronecker.cycleClass T (p+q)
        (FieldTensorHomologyKunneth.ArbitraryUniverse.tensorCycle C D p q (p+q) rfl a b))) at hh
    rw [hU] at hh
    have hrep := transported_tensor_cycleClass X Z B e he p q a b
    exact hrep.symm.trans hh.symm
  rw [hmap]
  exact hF


set_option backward.isDefEq.respectTransparency false in
/-- Graded commutativity of the relative shuffle, Bredon VI §3 pp.324–325.
Lift the relative chain, use the signed staircase transposition identity, and
pass to the genuine quotient and cycle classes. -/
theorem cross_swap (X Z : TopCat.{u}) (B : Set X) (p q : ℕ)
    (a : relativeHomology X B p) (b : homology Z q) :
    (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (Z × X))
      (productSubspace X Z B) (rightProductSubspace Z X B)
      (swapMap X Z) (fun _ hw ↦ hw) (p+q)).hom (cross X Z B p q a b) =
    (-1 : ℚ)^(p*q) • regradeRelative (TopCat.of (Z × X))
      (rightProductSubspace Z X B) (Nat.add_comm q p) (rightCross Z X B q p b a) := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (relativeChains X B) p a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
  simp only [cross, crossTensor, rightCross, rightCrossTensor, quotientTensor_cycleClass,
    relativeCycleClasses, rightCycleClasses, LinearMap.compr₂_apply]
  rw [← (regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B)
    (Nat.add_comm q p)).map_smul]
  rw [← (cycleClass (relativeChains (TopCat.of (Z × X)) (rightProductSubspace Z X B))
    (q+p)).map_smul]
  symm
  apply regradeRelative_cycleClass_map
  change HEq ((-1 : ℚ)^(p*q) • rightShuffle Z X B q p b.val a.val)
    ((SSetPair.chainComplexMap (pairMap (productSubspace X Z B) (rightProductSubspace Z X B)
      (swapMap X Z) (fun _ hw ↦ hw)) coefficients).f (p+q)
        (relativeShuffle X Z B p q a.val b.val))
  obtain ⟨a₀, ha⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
    (Cofork.IsColimit.epi
      ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
  rw [← ha, rightShuffle_projection, relativeShuffle_projection]
  have hπ := congrArg (fun k ↦ (k.f (p+q)).hom
    (SignedShuffle.shuffleBilinear X Z p q a₀ b.val))
      (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℚ)).app coefficients).naturality
        (pairMap (productSubspace X Z B) (rightProductSubspace Z X B)
          (swapMap X Z) (fun _ hw ↦ hw)))
  erw [← hπ]
  change HEq ((-1 : ℚ)^(p*q) •
    (chainProjection (TopCat.of (Z × X)) (rightProductSubspace Z X B)).f (q+p)
      (SignedShuffle.shuffleBilinear Z X q p b.val a₀))
    ((chainProjection (TopCat.of (Z × X)) (rightProductSubspace Z X B)).f (p+q)
      ((SSet.chainComplexMap (TopCat.toSSet.map (swapMap X Z)) coefficients).f (p+q)
        (SignedShuffle.shuffleBilinear X Z p q a₀ b.val)))
  erw [SignedShuffle.shuffleBilinear_swap X Z p q a₀ b.val]
  rw [← ((chainProjection (TopCat.of (Z × X)) (rightProductSubspace Z X B)).f (q+p)).hom.map_smul]
  rw [← (SignedShuffle.regrade (TopCat.of (Z × X)) (Nat.add_comm q p)).map_smul]
  exact (chainProjection_regrade_heq _ _ _ _).symm

/-- Reversing bidegrees preserves the total degree. -/
def bidegreeSwap (n : ℕ) : bidegree n ≃ bidegree n where
  toFun i := ⟨(i.val.2, i.val.1), (Nat.add_comm _ _).trans i.property⟩
  invFun i := ⟨(i.val.2, i.val.1), (Nat.add_comm _ _).trans i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Koszul coordinate flip is an equivalence on the full homology direct sum.
Source: Bredon VI §3 pp.324–325. -/
def crossSourceSwap (X Z : TopCat.{u}) (B : Set X) (n : ℕ) :
    kunnethSource X Z B n ≃ₗ[ℚ] rightKunnethSource Z X B n :=
  (DirectSum.lequivCongrLeft ℚ
    (M := fun pq : bidegree n ↦ relativeHomology X B pq.val.1 ⊗[ℚ] homology Z pq.val.2)
    (bidegreeSwap n)).trans
      (DirectSum.congrLinearEquiv fun pq ↦
        LinearEquiv.ofBijective (koszulFlip pq.val.2 pq.val.1
          (relativeHomology X B pq.val.2) (homology Z pq.val.1))
          (koszulFlip_bijective _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The degree-reversing source equivalence takes each tensor to its Koszul flip. -/
theorem crossSourceSwap_lof (X Z : TopCat.{u}) (B : Set X) (n p q : ℕ)
    (hpq : p+q=n) (a : relativeHomology X B p) (b : homology Z q) :
    crossSourceSwap X Z B n
      (DirectSum.lof ℚ (bidegree n) _ ⟨(p,q),hpq⟩ (a ⊗ₜ[ℚ] b)) =
    DirectSum.lof ℚ (bidegree n) _ ⟨(q,p),(Nat.add_comm q p).trans hpq⟩
      ((-1 : ℚ)^(p*q) • (b ⊗ₜ[ℚ] a)) := by
  classical
  dsimp only [crossSourceSwap, LinearEquiv.trans_apply]
  erw [DirectSum.lequivCongrLeft_lof ℚ (e := bidegreeSwap n) (i := ⟨(p,q),hpq⟩)
    (k := ⟨(q,p),(Nat.add_comm q p).trans hpq⟩) rfl _ _ rfl]
  simp only [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Right-relative Künneth bijectivity follows from the actual coordinate swap and
the already-proved left-relative equivalence. Source: Bredon VI p.320 and §3. -/
theorem rightKunnethMap_bijective (X Z : TopCat.{u}) (B : Set X) (n : ℕ) :
    Function.Bijective (rightKunnethMap Z X B n) := by
  classical
  let J : pair (TopCat.of (X × Z)) (productSubspace X Z B) ≅
      pair (TopCat.of (Z × X)) (rightProductSubspace Z X B) :=
    { hom := pairMap (productSubspace X Z B) (rightProductSubspace Z X B)
        (swapMap X Z) (fun _ hw ↦ hw)
      inv := pairMap (rightProductSubspace Z X B) (productSubspace X Z B)
        (swapMap Z X) (fun _ hw ↦ hw)
      hom_inv_id := by
        apply MorphismProperty.Arrow.Hom.ext <;> ext i x <;> rfl
      inv_hom_id := by
        apply MorphismProperty.Arrow.Hom.ext <;> ext i x <;> rfl }
  let T := ((SSetPair.homologyFunctor.{u} coefficients n).mapIso J).toLinearEquiv
  have heq : (rightKunnethMap Z X B n).comp (crossSourceSwap X Z B n).toLinearMap =
      T.toLinearMap.comp (kunnethMap X Z B n) := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩, hpq⟩
    apply TensorProduct.ext'
    intro a b
    subst n
    change rightKunnethMap Z X B (p+q)
      (crossSourceSwap X Z B (p+q)
        (DirectSum.lof ℚ (bidegree (p+q)) _ ⟨(p,q),rfl⟩ (a ⊗ₜ[ℚ] b))) =
      T (kunnethMap X Z B (p+q)
        (DirectSum.lof ℚ (bidegree (p+q)) _ ⟨(p,q),rfl⟩ (a ⊗ₜ[ℚ] b)))
    erw [crossSourceSwap_lof X Z B (p+q) p q rfl a b]
    simp only [rightKunnethMap, kunnethMap, DirectSum.toModule_lof, LinearMap.comp_apply,
      map_smul]
    change (-1 : ℚ)^(p*q) •
      regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.add_comm q p)
        (rightCross Z X B q p b a) =
      (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (Z × X))
        (productSubspace X Z B) (rightProductSubspace Z X B)
        (swapMap X Z) (fun _ hw ↦ hw) (p+q)).hom (cross X Z B p q a b)
    exact (cross_swap X Z B p q a b).symm
  have hbij : Function.Bijective
      ((rightKunnethMap Z X B n).comp (crossSourceSwap X Z B n).toLinearMap) := by
    rw [heq]
    exact T.bijective.comp (kunnethMap_bijective X Z B n)
  exact (Function.Bijective.of_comp_iff _ (crossSourceSwap X Z B n).bijective).mp hbij

set_option backward.isDefEq.respectTransparency false in
/-- Residual source laws for the relative shuffle Künneth construction.

Source: Bredon, *Topology and Geometry* VI §§1,3, pp.316–325. The helper isolates
the four algebraic source clauses. Relative bijectivity is proved by the exact
tensor comparison above; transposition and right-relative bijectivity are proved by
the source coordinate flip. Associativity follows from the proved signed three-coordinate
staircase identity: lift the first relative cycle to an absolute chain, apply native
chain shuffle associativity, and commute the quotient projection with the product
associator. Regrading commutes with projection. Passing to cycle classes gives the
asserted relative law, which the parent combines with naturality and the unit laws.
-/
theorem rational_relative_homology_cross_product_kunneth_residual
    (X Z : TopCat.{u}) (B : Set X) (_hB : IsOpen B) :

    (∀ n : ℕ, Function.Bijective (kunnethMap X Z B n)) ∧
    (∀ (p q : ℕ) (a : relativeHomology X B p) (b : homology Z q),
      (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (Z × X))
        (productSubspace X Z B) (rightProductSubspace Z X B)
        (swapMap X Z) (fun _ hw ↦ hw) (p + q)).hom (cross X Z B p q a b) =
        (-1 : ℚ) ^ (p * q) •
          regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.add_comm q p)
            (rightCross Z X B q p b a)) ∧
    (∀ n : ℕ, Function.Bijective (rightKunnethMap Z X B n)) ∧
    (∀ (W : TopCat.{u}) (p q r : ℕ) (a : relativeHomology X B p)
      (b : homology Z q) (c : homology W r),
      (relativeMap (X := TopCat.of ((X × Z) × W)) (Y := TopCat.of (X × (Z × W)))
        (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
        (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
        (fun _ hw ↦ hw) ((p + q) + r)).hom
          (cross (TopCat.of (X × Z)) W (productSubspace X Z B) (p + q) r
            (cross X Z B p q a b) c) =
        regradeRelative (TopCat.of (X × (Z × W)))
          (productSubspace X (TopCat.of (Z × W)) B) (Nat.add_assoc p q r).symm
          (cross X (TopCat.of (Z × W)) B p (q + r) a (absoluteCross Z W q r b c))) := by
  refine ⟨kunnethMap_bijective X Z B, cross_swap X Z B,
    rightKunnethMap_bijective X Z B, ?_⟩
  intro W p q r a b c
  obtain ⟨a, rfl⟩ := cycleClass_surjective (relativeChains X B) p a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
  obtain ⟨c, rfl⟩ := cycleClass_surjective (chains W) r c
  simp only [cross, crossTensor, absoluteCross, absoluteCrossTensor,
    quotientTensor_cycleClass, relativeCycleClasses, absoluteCycleClasses,
    LinearMap.compr₂_apply]
  symm
  apply regradeRelative_cycleClass_map
  change HEq
    (relativeShuffle X (TopCat.of (Z × W)) B p (q + r) a.val
      (SignedShuffle.shuffleBilinear Z W q r b.val c.val))
    ((SSetPair.chainComplexMap
      (pairMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
        (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
        (fun _ hw ↦ hw)) coefficients).f ((p + q) + r)
      (relativeShuffle (TopCat.of (X × Z)) W (productSubspace X Z B) (p + q) r
        (relativeShuffle X Z B p q a.val b.val) c.val))
  obtain ⟨a₀, ha⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
    (Cofork.IsColimit.epi
      ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
  rw [← ha, relativeShuffle_projection, relativeShuffle_projection,
    relativeShuffle_projection]
  have hπ := congrArg (fun k ↦ (k.f (p + q + r)).hom
    (SignedShuffle.shuffleBilinear (TopCat.of (X × Z)) W (p + q) r
      (SignedShuffle.shuffleBilinear X Z p q a₀ b.val) c.val))
      (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℚ)).app coefficients).naturality
        (pairMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
          (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
          (fun _ hw ↦ hw)))
  change
    (chainProjection (TopCat.of (X × (Z × W))) (productSubspace X (TopCat.of (Z × W)) B)).f
      (p + q + r) (SignedShuffle.pushforward (SignedShuffle.associate X Z W) (p + q + r)
        (SignedShuffle.shuffleBilinear (TopCat.of (X × Z)) W (p + q) r
          (SignedShuffle.shuffleBilinear X Z p q a₀ b.val) c.val)) =
    (SSetPair.chainComplexMap
      (pairMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
        (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
        (fun _ hw ↦ hw)) coefficients).f (p + q + r)
      ((chainProjection (TopCat.of ((X × Z) × W))
        (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))).f (p + q + r)
          (SignedShuffle.shuffleBilinear (TopCat.of (X × Z)) W (p + q) r
            (SignedShuffle.shuffleBilinear X Z p q a₀ b.val) c.val)) at hπ
  rw [← hπ]
  rw [SignedShuffle.shuffleBilinear_assoc X Z W p q r a₀ b.val c.val]
  exact (chainProjection_regrade_heq (TopCat.of (X × (Z × W)))
    (productSubspace X (TopCat.of (Z × W)) B) (Nat.add_assoc p q r).symm
    (SignedShuffle.shuffleBilinear X (TopCat.of (Z × W)) p (q + r)
      a₀ (SignedShuffle.shuffleBilinear Z W q r b.val c.val))).symm



set_option backward.isDefEq.respectTransparency false in
/-- Complete canonical relative rational Künneth statement for arbitrary topological
spaces and ONE open relative subspace. No CW, compactness, Hausdorff, finite-type,
finite-generation, or connectedness assumptions occur. All data are constructed above
from the exact published signed staircase shuffle, the native pair cokernel, native
cycle quotients, tensor universal property and algebraic direct sum.

Sources: Bredon, Topology and Geometry, IV16.1 pp.220–222; VI1.1–1.3 pp.316–318,
Cor1.4 p.318, algebraic Künneth1.5 pp.318–320 (field specialization p.320), the
one-relative-factor proof after1.6 p.320; VI§3 pp.324–325. Hatcher pp.277–278.
Complete natural-language proof of this node:

P1. Bredon's natural acyclic-model chain equivalence on the two standard simplices
has the same point initialization as the published signed shuffle. The natural
acyclic-model uniqueness homotopy compares those ACTUAL maps, not an unspecified
replacement. On the free models the tensor contractions cone each positive-degree
cycle to the fixed vertex; apply the same finite recurrence naturally. Restricting
the natural comparison and its homotopies to B×Z preserves the subspace support.
Thus the prescribed shuffle induces the absolute Eilenberg–Zilber isomorphism.

P2. The native relative complex is degreewise the quotient by the singular simplices
whose images lie in B. The remaining simplices are a free basis, so the degreewise
sequence is split exact and tensoring with the free Z-chain modules preserves it.
Compare this tensor short exact sequence with the actual product pair sequence
using the prescribed shuffle, its subspace restriction and quotient descent.
Absolute Eilenberg–Zilber on B×Z and X×Z and the long exact sequence give the
relative comparison isomorphism by the five lemma in every positive degree. At
zero the relative group is the cokernel of H0(B×Z)→H0(X×Z), or equivalently the
explicit quotient E0/(image j0+image boundary1); the same comparison gives an
isomorphism. This uses ordinary H0 and no hypothetical negative homology. Although
this one-relative argument works for arbitrary B, the unchanged exported theorem
retains its stated IsOpen B hypothesis. It neither assumes nor exports the stronger
double-relative union-pair theorem without its additional open-pair hypotheses.

P3. Apply Bredon's algebraic chain-tensor Künneth theorem to the actual relative and
absolute free rational complexes. Over ℚ every module is free and the Tor term is
zero, hence the direct sum of homology tensor products is isomorphic to tensor-total
homology in every degree. Its pure generator [c]⊗[z] is [c⊗z]. Composing with the
relative shuffle comparison gives precisely the quotientTensor/crossTensor/map data
above. Relative cycles lift to chains with boundary in B, not generally to absolute
cycles: the first descent and its cycle certificate explicitly keep that distinction.
All finite degree p+q=n summands are present, including (0,0).

P4. The Koszul flip c⊗z↦(-1)^(pq)z⊗c is a chain map on the tensor total complex.
Bredon's interchange homotopy compares it followed by the swapped prescribed shuffle
with the coordinate-transposed prescribed shuffle. Natural support restriction gives
the second-relative quotient. The resulting homology identity below contains exactly
(-1)^(pq). It gives the second-relative isomorphism and preserves ordinary degree zero.

P5. Postcomposition with actual continuous pair maps commutes with every staircase
simplex, hence with chain descent, cycle classes, tensors and the direct sum. This
proves both pure-class and whole-sum naturality. Inclusions and diagonal maps are
particular actual pair maps satisfying the displayed MapsTo guard, so this is their
relative/absolute diagram, not a new diagonal convention. For three inputs the two
iterated shuffles index the same words in three kinds of steps; inversion counts add
to the same sign and affine maps agree on all vertices. Passing through the actual
product associator and relative quotient yields associativity below. A point-factor
has one staircase and sign+1, giving the displayed insertion identity, including
arbitrary ordinary H0 classes and the one-point coefficient unit.

P6. At n=0 only (0,0) remains and no minus sign or negative-degree differential is
introduced. Empty factors have no singular simplices and zero chain modules; B=X
has zero relative quotient; B=∅ recovers the absolute comparison via its native
quotient map. All constructions and conclusions remain valid. Arbitrary infinite
complexes and homology dimensions cause no issue: only a finite total-degree index
is summed, and the source algebraic direct sum is the actual Mathlib DirectSum.
All canonical data are explicit; no canonical maps are selected
from an unknown existence conclusion. Stage3 is not claimed.
-/
theorem rational_relative_homology_cross_product_kunneth
    (X Z : TopCat.{u}) (B : Set X) (hB : IsOpen B) :
    (∀ n : ℕ, Function.Bijective (kunnethMap X Z B n)) ∧
    (∀ (p q : ℕ) (a : (chains X).X p) (b : (chains Z).X q),
      relativeShuffle X Z B p q ((chainProjection X B).f p a) b =
        (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
          (SignedShuffle.shuffleBilinear X Z p q a b)) ∧
    (∀ (p q : ℕ) (a : (chains Z).X p) (b : (chains X).X q),
      rightShuffle Z X B p q a ((chainProjection X B).f q b) =
        (chainProjection (TopCat.of (Z × X)) (rightProductSubspace Z X B)).f (p + q)
          (SignedShuffle.shuffleBilinear Z X p q a b)) ∧
    (∀ (p q : ℕ) (a : cycles (relativeChains X B) p) (b : cycles (chains Z) q),
      cross X Z B p q (cycleClass (relativeChains X B) p a) (cycleClass (chains Z) q b) =
        cycleClass (relativeChains (TopCat.of (X × Z)) (productSubspace X Z B))
          (p + q) (relativeCycleShuffle X Z B p q a b)) ∧
    (∀ (X' Z' : TopCat.{u}) (D : Set X') (f : X ⟶ X')
      (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (n : ℕ),
      (targetMap B D f hf g n).comp (kunnethMap X Z B n) =
        (kunnethMap X' Z' D n).comp (sourceMap B D f hf g n)) ∧
    (∀ n : ℕ,
      (targetMap (X := X) (Z := Z) (X' := TopCat.of (X × X))
        (Z' := TopCat.of (Z × Z)) B (productSubspace X X B) (diagonalMap X) (fun _ hw ↦ hw)
        (diagonalMap Z) n).comp (kunnethMap X Z B n) =
          (kunnethMap (TopCat.of (X × X)) (TopCat.of (Z × Z))
            (productSubspace X X B) n).comp
              (sourceMap (X := X) (Z := Z) (X' := TopCat.of (X × X))
                (Z' := TopCat.of (Z × Z)) B (productSubspace X X B) (diagonalMap X)
                (fun _ hw ↦ hw) (diagonalMap Z) n)) ∧
    (∀ (p q : ℕ) (a : homology X p) (b : homology Z q),
      homologyProjection (TopCat.of (X × Z)) (productSubspace X Z B) (p + q)
        (absoluteCross X Z p q a b) =
          cross X Z B p q (homologyProjection X B p a) b) ∧
    (∀ (p q : ℕ) (a : relativeHomology X B p) (b : homology Z q),
      (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (Z × X))
        (productSubspace X Z B) (rightProductSubspace Z X B)
        (swapMap X Z) (fun _ hw ↦ hw) (p + q)).hom (cross X Z B p q a b) =
        (-1 : ℚ) ^ (p * q) •
          regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.add_comm q p)
            (rightCross Z X B q p b a)) ∧
    (∀ n : ℕ, Function.Bijective (rightKunnethMap Z X B n)) ∧
    (∀ (W : TopCat.{u}) (p q r : ℕ) (a : relativeHomology X B p)
      (b : homology Z q) (c : homology W r),
      (relativeMap (X := TopCat.of ((X × Z) × W)) (Y := TopCat.of (X × (Z × W)))
        (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
        (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
        (fun _ hw ↦ hw) ((p + q) + r)).hom
          (cross (TopCat.of (X × Z)) W (productSubspace X Z B) (p + q) r
            (cross X Z B p q a b) c) =
        regradeRelative (TopCat.of (X × (Z × W)))
          (productSubspace X (TopCat.of (Z × W)) B) (Nat.add_assoc p q r).symm
          (cross X (TopCat.of (Z × W)) B p (q + r) a (absoluteCross Z W q r b c))) ∧
    (∀ (p : ℕ) (a : relativeHomology X B p) (z : Z),
      cross X Z B p 0 a (pointClass Z z) =
        (relativeMap (X := X) (Y := TopCat.of (X × Z))
          B (productSubspace X Z B) (insertPoint X Z z)
          (fun _ hw ↦ hw) p).hom a) ∧
    (∀ (q : ℕ) (x : X) (b : homology Z q),
      regradeRelative (TopCat.of (X × Z)) (productSubspace X Z B) (Nat.zero_add q)
        (cross X Z B 0 q (homologyProjection X B 0 (pointClass X x)) b) =
          homologyProjection (TopCat.of (X × Z)) (productSubspace X Z B) q
            ((homologyMap (insertPointLeft X Z x) q).hom b)) ∧
    (∀ (p : ℕ) (a : relativeHomology X B p) (z : Z),
      regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.zero_add p)
        (rightCross Z X B 0 p (pointClass Z z) a) =
          (relativeMap (X := X) (Y := TopCat.of (Z × X))
            B (rightProductSubspace Z X B) (insertPointLeft Z X z)
            (fun _ hw ↦ hw) p).hom a) := by
  have hπ {U V : TopCat.{u}} (A : Set U) (D : Set V) (f : U ⟶ V)
      (hf : Set.MapsTo f A D) (n : ℕ) (a : (chains U).X n) :
      (SSetPair.chainComplexMap (pairMap A D f hf) coefficients).f n
          ((chainProjection U A).f n a) =
        (chainProjection V D).f n
          ((SSet.chainComplexMap (TopCat.toSSet.map f) coefficients).f n a) := by
    exact (congrArg (fun k ↦ (k.f n).hom a)
      (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℚ)).app coefficients).naturality
        (pairMap A D f hf))).symm
  have hsh {X' Z' : TopCat.{u}} (D : Set X') (f : X ⟶ X')
      (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (p q : ℕ)
      (a : (relativeChains X B).X p) (b : (chains Z).X q) :
      (SSetPair.chainComplexMap
        (pairMap (productSubspace X Z B) (productSubspace X' Z' D)
          (productMap f g) (fun _ hw ↦ hf hw)) coefficients).f (p + q)
          (relativeShuffle X Z B p q a b) =
        relativeShuffle X' Z' D p q
          ((SSetPair.chainComplexMap (pairMap B D f hf) coefficients).f p a)
          ((SSet.chainComplexMap (TopCat.toSSet.map g) coefficients).f q b) := by
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
      (Cofork.IsColimit.epi
        ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a
    rw [relativeShuffle_projection, hπ B D f hf,
      hπ (productSubspace X Z B) (productSubspace X' Z' D) (productMap f g)
        (fun _ hw ↦ hf hw), relativeShuffle_projection]
    congr 1
    exact (SignedShuffle.signedShuffle_chainMap X Z).2.2.1 X' Z' f.hom g.hom p q c b
  have hcross {X' Z' : TopCat.{u}} (D : Set X') (f : X ⟶ X')
      (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (p q : ℕ)
      (a : relativeHomology X B p) (b : homology Z q) :
      targetMap B D f hf g (p + q) (cross X Z B p q a b) =
        cross X' Z' D p q ((relativeMap B D f hf p).hom a) ((homologyMap g q).hom b) := by
    obtain ⟨a, rfl⟩ := cycleClass_surjective (relativeChains X B) p a
    obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
    let a' := FieldChainKronecker.cycleMap
      (SSetPair.chainComplexMap (pairMap B D f hf) coefficients) p a
    let b' := FieldChainKronecker.cycleMap
      (SSet.chainComplexMap (TopCat.toSSet.map g) coefficients) q b
    have ha : (relativeMap B D f hf p).hom (cycleClass (relativeChains X B) p a) =
        cycleClass (relativeChains X' D) p a' := cycleClass_map _ p a a' rfl
    have hb : (homologyMap g q).hom (cycleClass (chains Z) q b) =
        cycleClass (chains Z') q b' := cycleClass_map _ q b b' rfl
    rw [ha, hb]
    simp only [cross, crossTensor, quotientTensor_cycleClass]
    apply cycleClass_map
    exact hsh D f hf g p q a b
  have hnat : ∀ (X' Z' : TopCat.{u}) (D : Set X') (f : X ⟶ X')
      (hf : Set.MapsTo f B D) (g : Z ⟶ Z') (n : ℕ),
      (targetMap B D f hf g n).comp (kunnethMap X Z B n) =
        (kunnethMap X' Z' D n).comp (sourceMap B D f hf g n) := by
    intro X' Z' D f hf g n
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, hpq⟩
    subst n
    apply TensorProduct.ext'
    intro a b
    simpa only [LinearMap.comp_apply, kunnethMap, sourceMap, DirectSum.toModule_lof,
      TensorProduct.map_tmul, regradeRelative, LinearMap.id_apply, cross] using
        hcross D f hf g p q a b
  have hunit : ∀ (p : ℕ) (a : relativeHomology X B p) (z : Z),
      cross X Z B p 0 a (pointClass Z z) =
        (relativeMap (X := X) (Y := TopCat.of (X × Z))
          B (productSubspace X Z B) (insertPoint X Z z) (fun _ hw ↦ hw) p).hom a := by
    intro p a z
    obtain ⟨a, rfl⟩ := cycleClass_surjective (relativeChains X B) p a
    simp only [cross, crossTensor, pointClass, quotientTensor_cycleClass]
    symm
    apply cycleClass_map
    change (SSetPair.chainComplexMap (pairMap B (productSubspace X Z B)
      (insertPoint X Z z) (fun _ hw ↦ hw)) coefficients).f p a.val =
        relativeShuffle X Z B p 0 a.val
          (SignedShuffle.generator Z (SignedShuffle.pointSimplex Z z))
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
      (Cofork.IsColimit.epi
        ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
    rw [← hc, hπ, relativeShuffle_projection, SignedShuffle.right_row_chain]
    rfl
  have hrightunit : ∀ (p : ℕ) (a : relativeHomology X B p) (z : Z),
      regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.zero_add p)
        (rightCross Z X B 0 p (pointClass Z z) a) =
          (relativeMap (X := X) (Y := TopCat.of (Z × X))
            B (rightProductSubspace Z X B) (insertPointLeft Z X z)
            (fun _ hw ↦ hw) p).hom a := by
    intro p a z
    obtain ⟨a, rfl⟩ := cycleClass_surjective (relativeChains X B) p a
    simp only [rightCross, rightCrossTensor, pointClass, quotientTensor_cycleClass]
    apply regradeRelative_cycleClass_map
    change HEq (rightShuffle Z X B 0 p
      (SignedShuffle.generator Z (SignedShuffle.pointSimplex Z z)) a.val)
        ((SSetPair.chainComplexMap (pairMap B (rightProductSubspace Z X B)
          (insertPointLeft Z X z) (fun _ hw ↦ hw)) coefficients).f p a.val)
    obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((chainProjection X B).f p)).mp
      (Cofork.IsColimit.epi
        ((pair X B).isColimitCokernelCoforkChainComplexX coefficients p)) a.val
    rw [← hc, hπ, rightShuffle_projection, SignedShuffle.left_row_chain]
    exact chainProjection_regrade_heq _ _ _ _
  have hleft : ∀ (q : ℕ) (x : X) (b : homology Z q),
      regradeRelative (TopCat.of (X × Z)) (productSubspace X Z B) (Nat.zero_add q)
        (cross X Z B 0 q (homologyProjection X B 0 (pointClass X x)) b) =
          homologyProjection (TopCat.of (X × Z)) (productSubspace X Z B) q
            ((homologyMap (insertPointLeft X Z x) q).hom b) := by
    intro q x b
    obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
    let a : cycles (chains X) 0 :=
      ⟨SignedShuffle.generator X (SignedShuffle.pointSimplex X x), pointGenerator_cycle X x⟩
    let a' := FieldChainKronecker.cycleMap (chainProjection X B) 0 a
    have ha : homologyProjection X B 0 (pointClass X x) =
        cycleClass (relativeChains X B) 0 a' := cycleClass_map _ 0 a a' rfl
    rw [ha]
    simp only [cross, crossTensor, quotientTensor_cycleClass]
    let F : chains Z ⟶ relativeChains (TopCat.of (X × Z)) (productSubspace X Z B) :=
      SSet.chainComplexMap (TopCat.toSSet.map (insertPointLeft X Z x)) coefficients ≫
        chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)
    have hF : (HomologicalComplex.homologyMap F q).hom (cycleClass (chains Z) q b) =
        homologyProjection (TopCat.of (X × Z)) (productSubspace X Z B) q
          ((homologyMap (insertPointLeft X Z x) q).hom (cycleClass (chains Z) q b)) := by
      simp only [F, HomologicalComplex.homologyMap_comp]
      rfl
    rw [← hF]
    apply regradeRelative_cycleClass_map
    change HEq (relativeShuffle X Z B 0 q ((chainProjection X B).f 0 a.val) b.val)
      ((chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f q
        ((SSet.chainComplexMap (TopCat.toSSet.map (insertPointLeft X Z x)) coefficients).f q b.val))
    rw [relativeShuffle_projection]
    change HEq ((chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (0 + q)
      (SignedShuffle.shuffleBilinear X Z 0 q
        (SignedShuffle.generator X (SignedShuffle.pointSimplex X x)) b.val)) _
    rw [SignedShuffle.left_row_chain]
    exact chainProjection_regrade_heq _ _ _ _
  have hquot : ∀ (p q : ℕ) (a : homology X p) (b : homology Z q),
      homologyProjection (TopCat.of (X × Z)) (productSubspace X Z B) (p + q)
        (absoluteCross X Z p q a b) =
          cross X Z B p q (homologyProjection X B p a) b := by
    intro p q a b
    obtain ⟨a, rfl⟩ := cycleClass_surjective (chains X) p a
    obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
    let a' : cycles (relativeChains X B) p :=
      FieldChainKronecker.cycleMap (chainProjection X B) p a
    have ha : homologyProjection X B p (cycleClass (chains X) p a) =
        cycleClass (relativeChains X B) p a' :=
      cycleClass_map (chainProjection X B) p a a' rfl
    rw [ha]
    simp only [absoluteCross, absoluteCrossTensor, cross, crossTensor,
      quotientTensor_cycleClass]
    apply cycleClass_map
    change (chainProjection (TopCat.of (X × Z)) (productSubspace X Z B)).f (p + q)
        (SignedShuffle.shuffleBilinear X Z p q a b) =
      relativeShuffle X Z B p q ((chainProjection X B).f p a) b
    exact (relativeShuffle_projection X Z B p q a b).symm
  suffices h :
    (∀ n : ℕ, Function.Bijective (kunnethMap X Z B n)) ∧
    (∀ (p q : ℕ) (a : relativeHomology X B p) (b : homology Z q),
      (relativeMap (X := TopCat.of (X × Z)) (Y := TopCat.of (Z × X))
        (productSubspace X Z B) (rightProductSubspace Z X B)
        (swapMap X Z) (fun _ hw ↦ hw) (p + q)).hom (cross X Z B p q a b) =
        (-1 : ℚ) ^ (p * q) •
          regradeRelative (TopCat.of (Z × X)) (rightProductSubspace Z X B) (Nat.add_comm q p)
            (rightCross Z X B q p b a)) ∧
    (∀ n : ℕ, Function.Bijective (rightKunnethMap Z X B n)) ∧
    (∀ (W : TopCat.{u}) (p q r : ℕ) (a : relativeHomology X B p)
      (b : homology Z q) (c : homology W r),
      (relativeMap (X := TopCat.of ((X × Z) × W)) (Y := TopCat.of (X × (Z × W)))
        (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z B))
        (productSubspace X (TopCat.of (Z × W)) B) (associatorMap X Z W)
        (fun _ hw ↦ hw) ((p + q) + r)).hom
          (cross (TopCat.of (X × Z)) W (productSubspace X Z B) (p + q) r
            (cross X Z B p q a b) c) =
        regradeRelative (TopCat.of (X × (Z × W)))
          (productSubspace X (TopCat.of (Z × W)) B) (Nat.add_assoc p q r).symm
          (cross X (TopCat.of (Z × W)) B p (q + r) a (absoluteCross Z W q r b c))) by
    rcases h with ⟨hiso, hswap, hright, hassoc⟩
    refine ⟨hiso, relativeShuffle_projection X Z B,
      rightShuffle_projection Z X B, ?_, hnat, ?_,
      hquot, hswap, hright, hassoc, hunit, hleft, hrightunit⟩
    · intro p q a b
      exact quotientTensor_cycleClass _ _ _ p q (p + q) _ _ _ a b
    · intro n
      exact hnat (TopCat.of (X × X)) (TopCat.of (Z × Z))
        (productSubspace X X B) (diagonalMap X) (fun _ hw ↦ hw) (diagonalMap Z) n
  -- Assemble the proved bijectivity, Koszul flip, and associator laws.
  exact rational_relative_homology_cross_product_kunneth_residual X Z B hB

/-- The inverse is derived only from the named bijectivity proof of the ACTUAL map.
Source: Bredon VI field Künneth p.320. The canonical forward map is crossTensor above. -/
def kunnethIso (X Z : TopCat.{u}) (B : Set X) (hB : IsOpen B) (n : ℕ) :
    kunnethSource X Z B n ≃ₗ[ℚ] kunnethTarget X Z B n :=
  LinearEquiv.ofBijective (kunnethMap X Z B n)
    ((rational_relative_homology_cross_product_kunneth X Z B hB).1 n)


end HolomorphicAnosov.RationalRelativeKunneth


