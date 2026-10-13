import HolomorphicAnosov.AlgebraicTopology.CharacteristicCellCohomologyComparison
import HolomorphicAnosov.Algebra.GradedRingOfBilinearProduct
import HolomorphicAnosov.AlgebraicTopology.GradedAlgebraOfBilinear
import HolomorphicAnosov.AlgebraicTopology.FiniteFreeBasis
import HolomorphicAnosov.AlgebraicTopology.TensorExactOfFree
import HolomorphicAnosov.AlgebraicTopology.DirectSumExact
import HolomorphicAnosov.AlgebraicTopology.DirectSumDegreewiseEquivalence
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyPairTheorems
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws
import Mathlib.Topology.CWComplex.Classical.Finite
import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15
import HolomorphicAnosov.Topology.FiniteCWULiftCharacteristicMaps
import HolomorphicAnosov.Topology.PointPositiveCohomologyProviderG12
import HolomorphicAnosov.Topology.ZeroCohomologyCycleEquivG10
import HolomorphicAnosov.Topology.StandardDiskBoundaryFiniteCW
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite-CW cohomological cross-product Künneth interface

Source: Hatcher, *Algebraic Topology*, Theorem 3.15, pages 214–218, with the
finite-dimensional induction in Proposition 3.17, page 217.
DAG node: `topo.finite_cw_cohomology_cross_product_kunneth_g3`.

The actual ordinary singular cochain and quotient cohomology types are reused.
The existing G9 front/back cochain formula and cocycle-class map are reused,
rather than taking a cohomology ring or a Künneth isomorphism as input.
No duplicate cup, unit or cocycle-class definitions are introduced here.
The theorem constructs quotient-cup and graded-ring data in its conclusion, pinned
to these original cochains, and asserts the exact degreewise and graded ring maps.

The internal cross-product lemmas require these representative equations too.
Arbitrary graded rings on the same modules do not suffice: over ℚ at a point,
rescaling one factor's product to 2ab and its unit to 1/2 makes the identity
cross map fail multiplicativity. On S¹ × S¹, replacing the positive-degree
products by zero makes the degree-(1,1) cross map zero, hence not an isomorphism.
The private compatibility hypotheses exclude both counterexamples and are
discharged by the constructed singular cup rings.
-/

noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial TensorProduct DirectSum

universe u

namespace HolomorphicAnosov.SingularCochain

variable (R : Type u) [CommRing R]

/-- The original ordinary product space, with the product topology.
Source: Hatcher's cross-product construction, page 214. -/
abbrev crossProductSpace (X Y : TopCat.{u}) : TopCat.{u} := TopCat.of (X × Y)

/-- The continuous first projection from the ordinary product.
Source: Hatcher's cross-product construction, page 214. -/
def crossProductFst (X Y : TopCat.{u}) : crossProductSpace X Y ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The continuous second projection from the ordinary product.
Source: Hatcher's cross-product construction, page 214. -/
def crossProductSnd (X Y : TopCat.{u}) : crossProductSpace X Y ⟶ Y :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The actual cochain cross product `p₁♯a ∪ p₂♯b`, before quotient descent.
Source: Hatcher, pages 214–215. Both pullbacks are the existing singular functor maps. -/
def crossCochain (X Y : TopCat.{u}) (p q : ℕ)
    (a : cochains R X p) (b : cochains R Y q) :
    cochains R (crossProductSpace X Y) (p + q) :=
  cupCochain R (crossProductSpace X Y)
    (((pullback R (crossProductFst X Y)).f p).hom a)
    (((pullback R (crossProductSnd X Y)).f q).hom b)

/-- The actual finite degree-k sum of tensor products occurring in Hatcher's theorem.
Source: Hatcher, pages 215–217. The index includes exactly p,q≥0 with p+q=k. -/
abbrev crossProductDegreeDomain (X Y : TopCat.{u}) (k : ℕ) :=
  ⨁ i : {i : ℕ × ℕ // i.1 + i.2 = k},
    (cohomology R X i.val.1 ⊗[R] cohomology R Y i.val.2)

/-- The ordinary graded cohomology module, with finite-support direct-sum convention.
Source: Hatcher, pages 214–216. No multiplication has yet been assumed on it. -/
abbrev gradedCohomology (X : TopCat.{u}) := ⨁ n : ℕ, cohomology R X n

/-- Hatcher pp.206–207: bilinear homogeneous cup products, associativity and the
constant-one class give the graded ring and its scalar algebra structure. -/
private theorem graded_ring_of_bilinear_cup
    (R : Type u) [CommRing R] (C : ℕ → Type u)
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (μ : ∀ p q, C p →ₗ[R] C q →ₗ[R] C (p + q)) (e : C 0)
    (hassoc : ∀ p q r (a : C p) (b : C q) (c : C r),
      HEq (μ (p + q) r (μ p q a b) c) (μ p (q + r) a (μ q r b c)))
    (hl : ∀ p (a : C p), HEq (μ 0 p e a) a)
    (hr : ∀ p (a : C p), HEq (μ p 0 a e) a) :
    ∃ G : DirectSum.GRing C,
      (∀ p q (a : C p) (b : C q), @GradedMonoid.GMul.mul _ _ _ G.toGMul _ _ a b = μ p q a b) ∧
      @GradedMonoid.GOne.one _ _ _ G.toGOne = e ∧
      (letI := G; Nonempty (DirectSum.GAlgebra R C)) := by
  let G := HolomorphicAnosov.gradedRingOfBilinearProduct R C μ e hl hr hassoc
  refine ⟨G, fun _ _ _ _ ↦ rfl, rfl, ?_⟩
  let := G
  exact HolomorphicAnosov.AlgebraicTopology.graded_algebra_of_bilinear R C μ
    (fun _ _ _ _ ↦ rfl)


/-- Hatcher pp.206–212: the ordinary specialization of the existing cup laws
constructs graded rings and scalar algebras on the literal singular cohomology
quotients. The products and units retain their original cocycle representatives. -/
private theorem cohomology_graded_ring_data :
    ∃ G : ∀ Z : TopCat.{u}, DirectSum.GRing (fun n ↦ cohomology R Z n),
      (∀ Z : TopCat.{u},
        letI := G Z
        (∀ (p q : ℕ) (a : cycles R (complex R Z) p)
          (b : cycles R (complex R Z) q),
          ∃ hc : cupCochain R Z a.val b.val ∈ cycles R (complex R Z) (p + q),
            GradedMonoid.GMul.mul (A := fun n : ℕ ↦ cohomology R Z n)
              (cocycleClass R (complex R Z) p a) (cocycleClass R (complex R Z) q b) =
              cocycleClass R (complex R Z) (p + q) ⟨cupCochain R Z a.val b.val, hc⟩) ∧
        (∃ hu : oneCochain R Z ∈ cycles R (complex R Z) 0,
          GradedMonoid.GOne.one (A := fun n : ℕ ↦ cohomology R Z n) =
            cocycleClass R (complex R Z) 0 ⟨oneCochain R Z, hu⟩)) ∧
      (∀ Z : TopCat.{u}, letI := G Z
        Nonempty (DirectSum.GAlgebra R (fun n ↦ cohomology R Z n))) := by
  classical
  obtain ⟨μ, pb, hrep, hassoc, hunit, _⟩ := singular_cup_product_laws R
  choose e he hunit using hunit
  have hex (Z : TopCat.{u}) := graded_ring_of_bilinear_cup R
    (fun n ↦ cohomology R Z n) (fun p q ↦ μ Z ∅ false false p q)
    (cocycleClass R (complex R Z) 0 (e Z))
    (fun p q r a b c ↦ hassoc Z ∅ false false false p q r a b c)
    (fun p a ↦ (hunit Z ∅ false p a).1)
    (fun p a ↦ (hunit Z ∅ false p a).2)
  choose G hmul hone hA using hex
  refine ⟨G, ?_, hA⟩
  intro Z
  let := G Z
  constructor
  · intro p q a b
    obtain ⟨c, hc, hclass⟩ := hrep Z ∅ false false p q a b
    have hv : c.val = cupCochain R Z a.val b.val := by
      change c.val = cupCochain R Z a.val b.val at hc
      exact hc
    have hm : cupCochain R Z a.val b.val ∈ cycles R (complex R Z) (p + q) :=
      hv ▸ c.property
    refine ⟨hm, ?_⟩
    rw [hmul]
    have heqc : c = ⟨cupCochain R Z a.val b.val, hm⟩ := Subtype.ext hv
    change μ Z ∅ false false p q (cocycleClass R (complex R Z) p a)
      (cocycleClass R (complex R Z) q b) = cocycleClass R (complex R Z) (p + q) c at hclass
    rw [heqc] at hclass
    exact hclass
  · have hm : oneCochain R Z ∈ cycles R (complex R Z) 0 := he Z ▸ (e Z).property
    refine ⟨hm, ?_⟩
    rw [hone]
    exact congrArg (cocycleClass R (complex R Z) 0) (Subtype.ext (he Z))


/-- Hatcher p.216: Mathlib's Koszul multiplication gives a ring on the original
additive tensor module. Its addition, zero, negation and unit are the original tensor operations;
its multiplication is precisely the Koszul bilinear map. -/
private theorem koszul_tensor_ring
    (R : Type*) [CommRing R] (A B : ℕ → Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
    [∀ n, Module R (A n)] [∀ n, Module R (B n)]
    [DirectSum.GRing A] [DirectSum.GRing B]
    [DirectSum.GAlgebra R A] [DirectSum.GAlgebra R B] :
    ∃ rt : Ring ((⨁ n, A n) ⊗[R] (⨁ n, B n)),
      (∀ u v, rt.add u v = u + v) ∧ rt.zero = 0 ∧ (∀ u, rt.neg u = -u) ∧
      (∀ u v, rt.mul u v = TensorProduct.gradedMul R A B u v) ∧
      rt.one = (1 : ⨁ n, A n) ⊗ₜ[R] (1 : ⨁ n, B n) := by
  let T := (⨁ n, A n) ⊗[R] (⨁ n, B n)
  let rt : Ring T :=
    { (inferInstance : AddCommGroup T), (inferInstance : AddGroupWithOne T) with
      mul := fun x y ↦ TensorProduct.gradedMul R A B x y
      npow := fun n x ↦ Nat.rec 1 (fun _ y ↦ TensorProduct.gradedMul R A B y x) n
      npow_zero := fun _ ↦ rfl
      npow_succ := fun _ _ ↦ rfl
      mul_assoc := TensorProduct.gradedMul_assoc A B
      one_mul := TensorProduct.one_gradedMul A B
      mul_one := TensorProduct.gradedMul_one A B
      left_distrib := fun _ _ _ ↦ map_add _ _ _
      right_distrib := fun x y z ↦ by
        exact LinearMap.congr_fun (map_add (TensorProduct.gradedMul R A B) x y) z
      zero_mul := fun x ↦ by
        exact LinearMap.congr_fun (map_zero (TensorProduct.gradedMul R A B)) x
      mul_zero := fun _ ↦ map_zero _ }
  exact ⟨rt, fun _ _ ↦ rfl, rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, rfl⟩


/-- The Koszul ring on a tensor of graded direct sums, with its native
additive and unit operations. This is the algebraic part of Hatcher p.216;
all fields are inherited from Mathlib's `TensorProduct.gradedMul` identities. -/
private theorem koszul_tensor_ring_data
    (R : Type*) [CommRing R] (A B : ℕ → Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
    [∀ n, Module R (A n)] [∀ n, Module R (B n)]
    [DirectSum.GRing A] [DirectSum.GRing B]
    [DirectSum.GAlgebra R A] [DirectSum.GAlgebra R B] :
    ∃ rt : Ring ((⨁ n, A n) ⊗[R] (⨁ n, B n)),
      (∀ u v, rt.add u v = u + v) ∧ rt.zero = 0 ∧ (∀ u, rt.neg u = -u) ∧
      (∀ u v, rt.mul u v = TensorProduct.gradedMul R A B u v) ∧
      rt.one = (1 : ⨁ n, A n) ⊗ₜ[R] (1 : ⨁ n, B n) := by
  exact koszul_tensor_ring R A B

/-- Internal abbreviation for the representative and unit equations already proved by
`cohomology_graded_ring_data`; it adds no cohomology structure. -/
private abbrev IsCochainGradedRing (R : Type u) [CommRing R] (Z : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R Z n)] : Prop :=
  (∀ (p q : ℕ) (a : cycles R (complex R Z) p) (b : cycles R (complex R Z) q),
    ∃ hc : cupCochain R Z a.val b.val ∈ cycles R (complex R Z) (p + q),
      GradedMonoid.GMul.mul (A := fun n : ℕ ↦ cohomology R Z n)
        (cocycleClass R (complex R Z) p a) (cocycleClass R (complex R Z) q b) =
        cocycleClass R (complex R Z) (p + q) ⟨cupCochain R Z a.val b.val, hc⟩) ∧
  (∃ hu : oneCochain R Z ∈ cycles R (complex R Z) 0,
    GradedMonoid.GOne.one (A := fun n : ℕ ↦ cohomology R Z n) =
      cocycleClass R (complex R Z) 0 ⟨oneCochain R Z, hu⟩)

/-- Equality of quotient products follows from their identical cocycle formula. -/
private theorem cochain_graded_mul_eq (R : Type u) [CommRing R] (Z : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R Z n)]
    (hZ : IsCochainGradedRing R Z)
    (cup : ∀ p q, cohomology R Z p →ₗ[R] cohomology R Z q →ₗ[R]
      cohomology R Z (p + q))
    (hcup : ∀ p q (a : cycles R (complex R Z) p) (b : cycles R (complex R Z) q),
      ∃ c : cycles R (complex R Z) (p + q), c.val = cupCochain R Z a.val b.val ∧
        cup p q (cocycleClass R _ p a) (cocycleClass R _ q b) =
          cocycleClass R _ (p + q) c)
    (p q : ℕ) (a : cohomology R Z p) (b : cohomology R Z q) :
    GradedMonoid.GMul.mul (A := fun n ↦ cohomology R Z n) a b = cup p q a b := by
  obtain ⟨a, rfl⟩ := MixedCup.cocycleClass_surjective R _ p a
  obtain ⟨b, rfl⟩ := MixedCup.cocycleClass_surjective R _ q b
  obtain ⟨hc, h⟩ := hZ.1 p q a b
  obtain ⟨c, hc', h'⟩ := hcup p q a b
  rw [h, h']
  exact congrArg (cocycleClass R _ (p + q)) (Subtype.ext hc'.symm)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The source-level multiplicativity calculation for the homogeneous
cross-product map. The proof is Hatcher's homogeneous cup calculation; it is
kept separate from the purely algebraic ring packaging below.

Source: Hatcher, Algebraic Topology, pp. 216–218. Choose cocycle representatives
of the four classes, using quotient surjectivity. The compatibility hypotheses
identify their products with the descended cup. Pullback naturality and
associativity rewrite the two sides as the same four factors except for the
middle pair. Graded commutativity exchanges that pair with sign (-1)^(q*r),
exactly Mathlib's `tmul_of_gradedMul_of_tmul`. The constant-one representative
pulls back to constant one; the two cup units prove the displayed unit identity.

Compatibility is essential: over ℚ and X = Y = point, give H⁰(X) multiplication
(a,b) ↦ 2ab and unit 1/2, with scalar algebra map r ↦ r/2, and use the usual rings
on Y and the product. The identity cross map satisfies the pure formula but
fails both multiplicativity and unit preservation. The hypotheses here rule
out that arbitrary-ring counterexample. -/
private theorem homogeneous_cross_product_mul
    (R : Type u) [CommRing R] (X Y : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R X n)]
    [DirectSum.GRing (fun n ↦ cohomology R Y n)]
    [DirectSum.GRing (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R X n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R Y n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    (hX : IsCochainGradedRing R X) (hY : IsCochainGradedRing R Y)
    (hP : IsCochainGradedRing R (crossProductSpace X Y))
    (μ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃ₗ[R]
      gradedCohomology R (crossProductSpace X Y))
    (hpure : ∀ (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q),
      μ ((DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a) ⊗ₜ[R]
          (DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)) =
        DirectSum.lof R ℕ (fun n ↦ cohomology R (crossProductSpace X Y) n) (p + q)
          (GradedMonoid.GMul.mul
            (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
            ((cohomologyPullback R (crossProductFst X Y) p).hom a)
            ((cohomologyPullback R (crossProductSnd X Y) q).hom b))) :
    ∀ p q r s (a : cohomology R X p) (b : cohomology R Y q)
      (c : cohomology R X r) (d : cohomology R Y s),
      μ (TensorProduct.gradedMul R (fun n ↦ cohomology R X n)
        (fun n ↦ cohomology R Y n)
        (DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a ⊗ₜ[R]
          DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)
        (DirectSum.lof R ℕ (fun n ↦ cohomology R X n) r c ⊗ₜ[R]
          DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) s d)) =
        μ (DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a ⊗ₜ[R]
          DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b) *
        μ (DirectSum.lof R ℕ (fun n ↦ cohomology R X n) r c ⊗ₜ[R]
          DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) s d) := by
  obtain ⟨cup, pb, hrep, hassoc, hunit, hpb, hnat, hcomm⟩ := singular_cup_product_laws R
  have hrep' (Z : TopCat.{u}) (p q : ℕ)
      (a : cycles R (complex R Z) p) (b : cycles R (complex R Z) q) :
      ∃ c : cycles R (complex R Z) (p + q), c.val = cupCochain R Z a.val b.val ∧
        cup Z ∅ false false p q (cocycleClass R _ p a) (cocycleClass R _ q b) =
          cocycleClass R _ (p + q) c := by
    exact hrep Z ∅ false false p q a b
  have hXeq := cochain_graded_mul_eq R X hX (cup X ∅ false false) (hrep' X)
  have hYeq := cochain_graded_mul_eq R Y hY (cup Y ∅ false false) (hrep' Y)
  have hPeq := cochain_graded_mul_eq R (crossProductSpace X Y) hP
    (cup (crossProductSpace X Y) ∅ false false) (hrep' _)
  have hnat' {Z W : TopCat.{u}} (f : Z ⟶ W) (p q : ℕ)
      (a : cohomology R W p) (b : cohomology R W q) :
      (cohomologyPullback R f (p + q)).hom (cup W ∅ false false p q a b) =
        cup Z ∅ false false p q ((cohomologyPullback R f p).hom a)
          ((cohomologyPullback R f q).hom b) := by
    have hp := hpb f ∅ ∅ (Set.mapsTo_empty f ∅) false
    have hp' : pb f ∅ ∅ (Set.mapsTo_empty f ∅) false = pullback R f := by
      change pb f ∅ ∅ (Set.mapsTo_empty f ∅) false ≫ 𝟙 _ = 𝟙 _ ≫ pullback R f at hp
      simpa only [Category.comp_id, Category.id_comp] using hp
    have hn := hnat f ∅ ∅ (Set.mapsTo_empty f ∅) false false p q a b
    change quotientMap R (pb f ∅ ∅ (Set.mapsTo_empty f ∅) false) (p + q) _ = _ at hn
    rw [hp'] at hn
    exact hn
  intro p q r s a b c d
  rw [TensorProduct.tmul_of_gradedMul_of_tmul]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, map_smul]
  simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]
  simp only [← DirectSum.lof_eq_of R]
  rw [hpure, hpure, hpure]
  rw [hXeq, hYeq]
  erw [hnat' (crossProductFst X Y) p r a c, hnat' (crossProductSnd X Y) q s b d]
  erw [← hPeq p r ((cohomologyPullback R (crossProductFst X Y) p).hom a)
    ((cohomologyPullback R (crossProductFst X Y) r).hom c),
    ← hPeq q s ((cohomologyPullback R (crossProductSnd X Y) q).hom b)
    ((cohomologyPullback R (crossProductSnd X Y) s).hom d)]
  simp only [DirectSum.lof_eq_of, ← DirectSum.of_mul_of]
  have hcommTotal (i j : ℕ) (x : cohomology R (crossProductSpace X Y) i)
      (y : cohomology R (crossProductSpace X Y) j) :
      DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) i x *
        DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) j y =
      (-1 : R) ^ (i * j) •
        (DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) j y *
          DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) i x) := by
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    have hc := hcomm (crossProductSpace X Y) ∅ false i j x y
    erw [← hPeq i j x y, ← hPeq j i y x] at hc
    have hs : (⟨i + j, GradedMonoid.GMul.mul (A := fun n ↦ cohomology R (crossProductSpace X Y) n) x y⟩ :
        Σ n, cohomology R (crossProductSpace X Y) n) =
        ⟨j + i, (-1 : R) ^ (i * j) • GradedMonoid.GMul.mul
          (A := fun n ↦ cohomology R (crossProductSpace X Y) n) y x⟩ :=
      by
        apply Sigma.ext (Nat.add_comm i j)
        exact hc
    have he := DirectSum.of_eq_of_gradedMonoid_eq hs
    simpa only [← DirectSum.lof_eq_of R, map_smul] using he
  let aa := DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) p
    ((cohomologyPullback R (crossProductFst X Y) p).hom a)
  let bb := DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) q
    ((cohomologyPullback R (crossProductSnd X Y) q).hom b)
  let cc := DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) r
    ((cohomologyPullback R (crossProductFst X Y) r).hom c)
  let dd := DirectSum.of (fun n ↦ cohomology R (crossProductSpace X Y) n) s
    ((cohomologyPullback R (crossProductSnd X Y) s).hom d)
  have hbc : bb * cc = (-1 : R) ^ (q * r) • (cc * bb) := hcommTotal q r _ _
  change (((((-1 : ℤˣ) ^ (q * r) : ℤˣ) : ℤ) : R)) •
    ((aa * cc) * (bb * dd)) = (aa * bb) * (cc * dd)
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  calc
    (-1 : R) ^ (q * r) • ((aa * cc) * (bb * dd)) =
        aa * (((-1 : R) ^ (q * r) • (cc * bb)) * dd) := by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (aa * bb) * (cc * dd) := by rw [← hbc]; simp only [mul_assoc]


/-- Tensor and direct-sum induction extend the homogeneous cup calculation to
all finitely supported tensors. Surjectivity then forces the unit identity. -/
private theorem total_cross_product_mul_unit
    (R : Type u) [CommRing R] (X Y : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R X n)]
    [DirectSum.GRing (fun n ↦ cohomology R Y n)]
    [DirectSum.GRing (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R X n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R Y n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    (hX : IsCochainGradedRing R X) (hY : IsCochainGradedRing R Y)
    (hP : IsCochainGradedRing R (crossProductSpace X Y))
    (μ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃ₗ[R]
      gradedCohomology R (crossProductSpace X Y))
    (hpure : ∀ (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q),
      μ ((DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a) ⊗ₜ[R]
          (DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)) =
        DirectSum.lof R ℕ (fun n ↦ cohomology R (crossProductSpace X Y) n) (p + q)
          (GradedMonoid.GMul.mul
            (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
            ((cohomologyPullback R (crossProductFst X Y) p).hom a)
            ((cohomologyPullback R (crossProductSnd X Y) q).hom b))) :
    (∀ u v, μ (TensorProduct.gradedMul R
        (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) = μ u * μ v) ∧
      μ ((1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y)) = 1 := by
  have hhom := homogeneous_cross_product_mul R X Y hX hY hP μ hpure
  have hmul : ∀ u v, μ (TensorProduct.gradedMul R
      (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) = μ u * μ v := by
    intro u
    refine TensorProduct.inductionOn u ?_ ?_
    · intro x y v
      refine TensorProduct.inductionOn v ?_ ?_
      · intro z w
        induction x using DirectSum.induction_on with
        | zero => simp
        | of i a =>
          induction y using DirectSum.induction_on with
          | zero => simp
          | of j b =>
            induction z using DirectSum.induction_on with
            | zero => simp
            | of k c =>
              induction w using DirectSum.induction_on with
              | zero => simp
              | of l d => exact hhom i j k l a b c d
              | add x y hx hy =>
                simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]
            | add x y hx hy =>
              simp only [TensorProduct.add_tmul, map_add, mul_add, hx, hy]
          | add x y hx hy =>
            simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, add_mul, hx, hy]
        | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul, hx, hy]
      · intro z w hz hw
        simp only [map_add, mul_add, hz, hw]
    · intro x y hx hy v
      simp only [map_add, LinearMap.add_apply, hx v, hy v, add_mul]

  refine ⟨hmul, ?_⟩
  obtain ⟨t, ht⟩ := μ.surjective 1
  have h := hmul ((1 : gradedCohomology R X) ⊗ₜ[R]
    (1 : gradedCohomology R Y)) t
  rw [show TensorProduct.gradedMul R (fun n ↦ cohomology R X n)
      (fun n ↦ cohomology R Y n) ((1 : gradedCohomology R X) ⊗ₜ[R]
        (1 : gradedCohomology R Y)) t = t from
      TensorProduct.one_gradedMul (fun n ↦ cohomology R X n)
        (fun n ↦ cohomology R Y n) t, ht, mul_one] at h
  exact h.symm

/-- The remaining algebraic transport of the source-level identities to the
RingEquiv field of the target. The map is the same linear equivalence `μ`; its
multiplication and unit preservation are exactly the two preceding identities. -/
private theorem total_cross_product_ring_equiv
    (R : Type u) [CommRing R] (X Y : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R X n)]
    [DirectSum.GRing (fun n ↦ cohomology R Y n)]
    [DirectSum.GRing (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R X n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R Y n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    (μ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃ₗ[R]
      gradedCohomology R (crossProductSpace X Y))
    (hmul : ∀ u v, μ (TensorProduct.gradedMul R
        (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) = μ u * μ v)
    (_hone : μ ((1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y)) = 1)
    (rt : Ring (gradedCohomology R X ⊗[R] gradedCohomology R Y))
    (hmulrt : ∀ u v, rt.mul u v = TensorProduct.gradedMul R
      (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v)
    (_honert : rt.one = (1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y)) :
      (letI := rt
       letI : Mul (gradedCohomology R X ⊗[R] gradedCohomology R Y) := rt.toMul
       ∃ Φ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃+*
           gradedCohomology R (crossProductSpace X Y),
         ∀ u, Φ u = μ u) := by
  let := rt
  let : Mul (gradedCohomology R X ⊗[R] gradedCohomology R Y) := rt.toMul
  let Φ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃+*
      gradedCohomology R (crossProductSpace X Y) :=
    { μ.toEquiv with
      map_mul' := by
        intro u v
        change μ (rt.mul u v) = μ u * μ v
        rw [hmulrt]
        exact hmul u v
      map_add' := μ.map_add }
  exact ⟨Φ, fun u ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The explicit degreewise linear cross map: pull back each factor, apply the
literal descended cup product, and transport the degree along the index equation.
Source: Hatcher, Algebraic Topology, pp.214–216. -/
private def degreeCrossMap (R : Type u) [CommRing R] (X Y : TopCat.{u}) (k : ℕ) :
    crossProductDegreeDomain R X Y k →ₗ[R] cohomology R (crossProductSpace X Y) k :=
  DirectSum.toModule R _ _ fun i ↦
    (LinearEquiv.cast (R := R) (M := fun n ↦ cohomology R (crossProductSpace X Y) n)
      i.property).toLinearMap.comp
      (TensorProduct.lift ((MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false
        i.val.1 i.val.2).compl₁₂
          (cohomologyPullback R (crossProductFst X Y) i.val.1).hom
          (cohomologyPullback R (crossProductSnd X Y) i.val.2).hom))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the constructed degree cross map on its pure generators.
This is the tensor and direct-sum universal property from Hatcher pp.214–216. -/
private theorem degreeCrossMap_pure (R : Type u) [CommRing R] (X Y : TopCat.{u}) (k : ℕ)
    (i : {i : ℕ × ℕ // i.1 + i.2 = k})
    (a : cohomology R X i.val.1) (b : cohomology R Y i.val.2) :
    degreeCrossMap R X Y k (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) =
      cast (congrArg (fun n ↦ (cohomology R (crossProductSpace X Y) n : Type u)) i.property)
        (MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false i.val.1 i.val.2
          ((cohomologyPullback R (crossProductFst X Y) i.val.1).hom a)
          ((cohomologyPullback R (crossProductSnd X Y) i.val.2).hom b)) := by
  simp only [degreeCrossMap, DirectSum.toModule_lof, LinearMap.comp_apply,
    TensorProduct.lift.tmul]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Forgetting support sends the mixed relative cup to the ordinary cup.
Source: Hatcher p.209. Reduce both inputs to cocycles; the defining relative
inclusion equation identifies the products before passage to their quotients. -/
private theorem mixedCup_forget (X : TopCat.{u}) (A : Set X) (p q : ℕ)
    (a : relativeCohomology R X A p) (b : cohomology R X q) :
    quotientMap R (cupInclusion R X A true) (p + q)
        (MixedCup.descended_cup R X A true false p q a b) =
      MixedCup.descended_cup R X ∅ false false p q
        (quotientMap R (cupInclusion R X A true) p a) b := by
  obtain ⟨a, rfl⟩ := MixedCup.cocycleClass_surjective R _ p a
  obtain ⟨b, rfl⟩ := MixedCup.cocycleClass_surjective R _ q b
  let f := cupInclusion R X A true
  let ac := MixedCup.cycle_map R f p a
  let c := MixedCup.tagged_cup_linear R X A true false p q a b
  let d := MixedCup.tagged_cup_linear R X ∅ false false p q ac b
  have hcd : MixedCup.cycle_map R f (p + q) c = d := by
    apply Subtype.ext
    exact (MixedCup.tagged_cochain_cup_inclusion R X A true false p q a.val b.val).trans
      (MixedCup.tagged_cochain_cup_inclusion R X ∅ false false p q
        (f.f p a.val) b.val).symm
  calc
    _ = quotientMap R f (p + q) (cocycleClass R (relativeComplex R X A) (p + q) c) :=
      congrArg (quotientMap R f (p + q))
        (MixedCup.descended_cup_representatives R X A true false p q a b)
    _ = cocycleClass R (complex R X) (p + q) (MixedCup.cycle_map R f (p + q) c) :=
      MixedCup.quotientMap_cocycleClass R f (p + q) c
    _ = cocycleClass R (complex R X) (p + q) d := congrArg _ hcd
    _ = MixedCup.descended_cup R X ∅ false false p q
        (cocycleClass R (complex R X) p ac) (cocycleClass R (complex R X) q b) :=
      (MixedCup.descended_cup_representatives R X ∅ false false p q ac b).symm
    _ = _ := congrArg (fun t ↦ MixedCup.descended_cup R X ∅ false false p q t
        (cocycleClass R (complex R X) q b))
      (MixedCup.quotientMap_cocycleClass R f p a).symm

/-- The product pair has the literal inverse image of A under the first projection.
Source: Hatcher pp.216–217. -/
private abbrev crossPair (X Y : TopCat.{u}) (A : Set X) : Set (crossProductSpace X Y) :=
  {z | z.1 ∈ A}

set_option backward.isDefEq.respectTransparency false in
/-- The relative cross product on one homogeneous tensor summand.
Source: Hatcher pp.216–217: first pull back the relative class along the first
projection of pairs, then cup with the absolute second projection pullback. -/
private def relativeCrossHomogeneous (X Y : TopCat.{u}) (A : Set X) (p q : ℕ) :
    relativeCohomology R X A p →ₗ[R] cohomology R Y q →ₗ[R]
      relativeCohomology R (crossProductSpace X Y) (crossPair X Y A) (p + q) :=
  (MixedCup.descended_cup R (crossProductSpace X Y) (crossPair X Y A) true false p q).compl₁₂
      (relativeCohomologyPullback R (crossProductFst X Y) (fun _ hz ↦ hz) p).hom
      (cohomologyPullback R (crossProductSnd X Y) q).hom

set_option backward.isDefEq.respectTransparency false in
/-- The cross-product square for relative-to-absolute maps commutes.
Source: Hatcher pp.216–217. The inclusion square for first-projection pullback
and the representative mixed-cup inclusion identity give the equality. -/
private theorem relativeCrossHomogeneous_forget (X Y : TopCat.{u}) (A : Set X)
    (p q : ℕ) (a : relativeCohomology R X A p) (b : cohomology R Y q) :
    (relativeForget R (crossProductSpace X Y) (crossPair X Y A) (p + q))
        (relativeCrossHomogeneous R X Y A p q a b) =
      MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false p q
        ((cohomologyPullback R (crossProductFst X Y) p)
          (relativeForget R X A p a))
        ((cohomologyPullback R (crossProductSnd X Y) q) b) := by
  change quotientMap R (cupInclusion R _ _ true) (p + q)
    (MixedCup.descended_cup R _ _ true false p q _ _) = _
  rw [mixedCup_forget]
  have hs := congrArg (fun f ↦ quotientMap R f p)
    (MixedCup.tagged_pullback_square R (crossProductFst X Y)
      (crossPair X Y A) A (fun _ hz ↦ hz) true)
  rw [HolomorphicAnosov.CharacteristicCellComparison.quotientMap_comp_bridge,
    HolomorphicAnosov.CharacteristicCellComparison.quotientMap_comp_bridge] at hs
  have ha := congrArg (fun f ↦ f a) hs
  change quotientMap R (cupInclusion R _ _ true) p
      (relativeCohomologyPullback R (crossProductFst X Y) (fun _ hz ↦ hz) p a) =
    cohomologyPullback R (crossProductFst X Y) p (relativeForget R X A p a) at ha
  exact congrArg (fun t ↦ MixedCup.descended_cup R (crossProductSpace X Y) ∅
    false false p q t ((cohomologyPullback R (crossProductSnd X Y) q) b)) ha

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism is a right module map for cup with an ambient
absolute class. Source: Hatcher pp.199–200 and Lemma 3.6 p.206. Extend the
subspace cocycle, cup that extension with the ambient cocycle, and apply the
Leibniz identity. The second differential term is zero; the first is the
relative cup of the connecting representative with the ambient cocycle. -/
private theorem connecting_cup_right (X : TopCat.{u}) (A : Set X) (p q : ℕ)
    (a : cohomology R (TopCat.of A) p) (b : cohomology R X q) :
    HEq
      (quotientConnecting R (singular_cochain_pair_shortExact R X A) (p + q)
        (MixedCup.descended_cup R (TopCat.of A) ∅ false false p q a
          (cohomologyPullback R (subspaceInclusion X A) q b)))
      (MixedCup.descended_cup R X A true false (p + 1) q
        (quotientConnecting R (singular_cochain_pair_shortExact R X A) p a) b) := by
  obtain ⟨a, rfl⟩ := MixedCup.cocycleClass_surjective R _ p a
  obtain ⟨b, rfl⟩ := MixedCup.cocycleClass_surjective R _ q b
  obtain ⟨e, he⟩ := singular_cochain_restriction_surjective R X A p a.val
  obtain ⟨β, hβ⟩ := singular_relative_cocycle_of_extension R X A p a e he
  have hconn := cochain_quotient_connecting_representative R
    (singular_cochain_pair_shortExact R X A) p a e he β hβ
  let br := MixedCup.cycle_map R (pullback R (subspaceInclusion X A)) q b
  let ab := MixedCup.tagged_cup_linear R (TopCat.of A) ∅ false false p q a br
  have hab : ab.val = cupCochain R (TopCat.of A) a.val br.val :=
    MixedCup.tagged_cochain_cup_inclusion R (TopCat.of A) ∅ false false p q a.val br.val
  have heab : (pullback R (subspaceInclusion X A)).f (p + q)
      (cupCochain R X e b.val) = ab.val := by
    rw [pullback_cupCochain, he, hab]
    rfl
  obtain ⟨γ, hγ⟩ := singular_relative_cocycle_of_extension R X A (p + q)
    ab (cupCochain R X e b.val) heab
  have hconnab := cochain_quotient_connecting_representative R
    (singular_cochain_pair_shortExact R X A) (p + q) ab
    (cupCochain R X e b.val) heab γ hγ
  have hl : MixedCup.descended_cup R (TopCat.of A) ∅ false false p q
      (cocycleClass R (complex R (TopCat.of A)) p a)
      (cohomologyPullback R (subspaceInclusion X A) q
        (cocycleClass R (complex R X) q b)) =
      cocycleClass R (complex R (TopCat.of A)) (p + q) ab := by
    calc
      _ = MixedCup.descended_cup R (TopCat.of A) ∅ false false p q
          (cocycleClass R (complex R (TopCat.of A)) p a)
          (cocycleClass R (complex R (TopCat.of A)) q br) :=
        congrArg (fun t ↦ MixedCup.descended_cup R (TopCat.of A) ∅ false false p q
          (cocycleClass R (complex R (TopCat.of A)) p a) t)
          (MixedCup.quotientMap_cocycleClass R (pullback R (subspaceInclusion X A)) q b)
      _ = _ := MixedCup.descended_cup_representatives R (TopCat.of A) ∅ false false p q a br
  let d := MixedCup.tagged_cup_linear R X A true false (p + 1) q β b
  have hr : MixedCup.descended_cup R X A true false (p + 1) q
      (quotientConnecting R (singular_cochain_pair_shortExact R X A) p
        (cocycleClass R (complex R (TopCat.of A)) p a))
      (cocycleClass R (complex R X) q b) =
      cocycleClass R (relativeComplex R X A) ((p + 1) + q) d := by
    calc
      _ = MixedCup.descended_cup R X A true false (p + 1) q
          (cocycleClass R (relativeComplex R X A) (p + 1) β)
          (cocycleClass R (complex R X) q b) :=
        congrArg (fun t ↦ MixedCup.descended_cup R X A true false (p + 1) q t
          (cocycleClass R (complex R X) q b)) hconn
      _ = _ := MixedCup.descended_cup_representatives R X A true false (p + 1) q β b
  have hlc := (congrArg
    (quotientConnecting R (singular_cochain_pair_shortExact R X A) (p + q)) hl).trans hconnab
  apply (heq_of_eq hlc).trans
  apply HEq.trans ?_ (heq_of_eq hr.symm)
  apply HEq.symm
  apply MixedCup.class_heq_of_inclusion_cast R X A (i := true) (j := true) rfl
    (show (p + 1) + q = p + q + 1 by omega) d γ
  change ((complex R X).XIsoOfEq _).hom
    ((cupInclusion R X A true).f ((p + 1) + q)
      (MixedCup.tagged_cochain_cup R X A true false (p + 1) q β.val b.val)) = _
  erw [MixedCup.tagged_cochain_cup_inclusion R X A true false (p + 1) q β.val b.val]
  change ((complex R X).XIsoOfEq _).hom
      (cupCochain R X ((relativeInclusion R X A).f (p + 1) β.val) b.val) =
    (relativeInclusion R X A).f (p + q + 1) γ.val
  calc
    _ = ((complex R X).XIsoOfEq (show (p + 1) + q = p + q + 1 by omega)).hom
        (cupCochain R X (coboundary R X p e) b.val) :=
      congrArg (fun t ↦ ((complex R X).XIsoOfEq
        (show (p + 1) + q = p + q + 1 by omega)).hom (cupCochain R X t b.val)) hβ
    _ = coboundary R X (p + q) (cupCochain R X e b.val) := by
      have hb := (MixedCup.mem_cycles_iff_d_eq_zero R (complex R X) q b.val).mp b.property
      obtain ⟨B, hB⟩ := cupCochain_bilinear R X p (q + 1)
      have hz : cupCochain R X e (0 : cochains R X (q + 1)) = 0 :=
        (hB e 0).symm.trans (map_zero (B e))
      have hzero : cupCochain R X e (coboundary R X q b.val) = 0 :=
        (congrArg (cupCochain R X e) hb).trans hz
      have hh := cochain_cup_leibniz R X e b.val
      rw [hzero, smul_zero, add_zero] at hh
      exact hh.symm
    _ = _ := hγ.symm

set_option backward.isDefEq.respectTransparency false in
/-- Specialize the imported degree-zero quotient equivalence to cocycle classes. Source: Hatcher p.198: the incoming differential in degree
zero vanishes in an unaugmented cochain complex, so quotienting changes nothing. -/
private theorem zero_cohomology_cycle_equiv (Q : CochainComplex (ModuleCat.{u} R) ℕ) :
    ∃ e : cycles R Q 0 ≃ₗ[R] quotient R Q 0,
      ∀ a, e a = cocycleClass R Q 0 a :=
  exists_zero_cohomology_cycle_equiv R Q

set_option backward.isDefEq.respectTransparency false in
/-- The constant-one class is the scalar basis of degree-zero cohomology of a
one-point space. Source: Hatcher pp.197–198 and the existing point-degree-zero
basis proof. Evaluate on the unique zero simplex; multiplication of the unit
cocycle by this scalar is the inverse, because cochains are determined by their
generator values. There are no degree-zero boundaries. -/
private theorem unique_zero_cohomology_equiv (X : TopCat.{u}) [Unique X] :
    ∃ E : R ≃ₗ[R] cohomology R X 0, ∀ r : R,
      E r = r • cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X) := by
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (TopCat.toSSetObjEquiv X (op ⦋0⦌)).symm (ContinuousMap.const _ (default : X))
  let z := ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ).hom 1
  let ev0 : (((chainFunctor R).obj X).X 0 ⟶ ModuleCat.of R R) →ₗ[R] R :=
    { toFun := fun a ↦ LinearMap.applyₗ z (ModuleCat.Hom.hom a)
      map_add' := by intro a b; simp [ModuleCat.Hom.hom]
      map_smul' := by intro c a; simp [ModuleCat.Hom.hom] }
  let ev : cycles R (complex R X) 0 →ₗ[R] R :=
    { toFun := fun a ↦ ev0 a.val
      map_add' := fun _ _ ↦ map_add ev0 _ _
      map_smul' := fun _ _ ↦ map_smul ev0 _ _ }
  let up := MixedCup.unit_cocycle R X
  have hev : ev up = 1 := by
    change (((TopCat.toSSet.obj X).ιChainComplex σ) ≫ oneCochain R X).hom 1 = 1
    simp [SSet.ιChainComplex, oneCochain]
  let inv : R →ₗ[R] cycles R (complex R X) 0 :=
    { toFun := fun r ↦ r • up
      map_add' := fun _ _ ↦ add_smul _ _ _
      map_smul' := fun _ _ ↦ mul_smul _ _ _ }
  have hs (τ : (TopCat.toSSet.obj X) _⦋0⦌) : τ = σ := by
    apply (TopCat.toSSetObjEquiv X (op ⦋0⦌)).injective
    exact Subsingleton.elim _ _
  have hinv : Function.LeftInverse inv ev := by
    intro c
    apply Subtype.ext
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [hs τ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ev (inv (ev c)) = ev c
    change ev ((ev c) • up) = ev c
    rw [map_smul, hev, smul_eq_mul, mul_one]
  have hleft : Function.LeftInverse ev inv := by
    intro r
    change ev (r • up) = r
    rw [map_smul, hev, smul_eq_mul, mul_one]
  obtain ⟨E0, hE0⟩ := zero_cohomology_cycle_equiv R (complex R X)
  let E := (LinearEquiv.ofBijective inv ⟨hleft.injective, hinv.surjective⟩).trans E0
  refine ⟨E, ?_⟩
  intro r
  change E0 (r • up) = _
  rw [hE0, map_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Package the existing quotient pullbacks as their contravariant functor.
Source: Hatcher p.201. Conjugating the homology functor by the canonical
module quotient isomorphisms preserves identity and composition. -/
private def actualCohomologyFunctor (n : ℕ) : TopCat.{u}ᵒᵖ ⥤ ModuleCat.{u} R where
  obj X := cohomology R X.unop n
  map f := cohomologyPullback R f.unop n
  map_id X := by
    change quotientMap R ((cochainFunctor R).map (𝟙 X)) n = 𝟙 _
    rw [(cochainFunctor R).map_id X]
    dsimp [quotientMap]
    rw [HomologicalComplex.homologyMap_id]
    exact (Category.comp_id _).trans
      (((cochainFunctor R).obj X).sc n).moduleCatHomologyIso.inv_hom_id
  map_comp f g := by
    change quotientMap R ((cochainFunctor R).map (f ≫ g)) n = _
    rw [Functor.map_comp,
      HolomorphicAnosov.CharacteristicCellComparison.quotientMap_comp_bridge]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary-ring/universe form of the existing constant-one pullback theorem,
retaining the literal cochain. Source: Hatcher pp.201 and 207. Each free singular
simplex generator maps to one generator, where the constant-one value is one. -/
private theorem actualPullback_one {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (pullback R f).f 0 (oneCochain R Y) = oneCochain R X := by
  change (((chainFunctor R).map f).f 0) ≫ oneCochain R Y = oneCochain R X
  apply SSet.chainComplex_hom_ext
  intro σ
  dsimp only [oneCochain]
  rw [← Category.assoc]
  change ((TopCat.toSSet.obj X).ιChainComplex σ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f 0) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f]
  simp [SSet.ιChainComplex]

set_option backward.isDefEq.respectTransparency false in
private theorem actualPullback_unitClass {X Y : TopCat.{u}} (f : X ⟶ Y) :
    cohomologyPullback R f 0 (cocycleClass R (complex R Y) 0 (MixedCup.unit_cocycle R Y)) =
      cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X) := by
  apply (MixedCup.quotientMap_cocycleClass R (pullback R f) 0 _).trans
  apply congrArg (cocycleClass R (complex R X) 0)
  apply Subtype.ext
  exact actualPullback_one R f

set_option backward.isDefEq.respectTransparency false in
/-- Crossing the degree-zero unit class with b is the second pullback of b.
Source: Hatcher p.214 and the cup unit identity p.207. The first projection
preserves the constant-one cocycle; the degree transport then removes 0+k. -/
private theorem degreeCrossMap_zero_left (X Y : TopCat.{u}) (k : ℕ)
    (b : cohomology R Y k) :
    degreeCrossMap R X Y k (DirectSum.lof R _ _ ⟨(0, k), Nat.zero_add k⟩
      (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X) ⊗ₜ[R] b)) =
      cohomologyPullback R (crossProductSnd X Y) k b := by
  apply (degreeCrossMap_pure R X Y k ⟨(0, k), Nat.zero_add k⟩
    (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X)) b).trans
  have hu := actualPullback_unitClass R (crossProductFst X Y)
  obtain ⟨c, hc⟩ := MixedCup.cocycleClass_surjective R (complex R (crossProductSpace X Y)) k
    (cohomologyPullback R (crossProductSnd X Y) k b)
  have heq : HEq
      (MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false 0 k
        (cohomologyPullback R (crossProductFst X Y) 0
          (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X)))
        (cohomologyPullback R (crossProductSnd X Y) k b))
      (cohomologyPullback R (crossProductSnd X Y) k b) := by
    rw [hu, ← hc]
    exact MixedCup.tagged_cup_unit_left R (crossProductSpace X Y) ∅ false k c
  apply cast_eq_iff_heq.mpr
  dsimp only
  exact heq

/-- Linear algebra for the point base case: a graded module concentrated in
zero with generator e has tensor totalization equal to the other module.
Source: Hatcher Theorem 3.15, p.217. Insert e in the (0,k) summand; all other
summands vanish, and linearity reduces the inverse identity to this generator. -/
private theorem degreeTensor_point_bijective
    (C D : ℕ → Type u) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (F : Type u) [AddCommGroup F] [Module R F] (k : ℕ)
    (μ : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = k}, C i.val.1 ⊗[R] D i.val.2) →ₗ[R] F)
    (e : C 0) (hC : ∀ n, 0 < n → Subsingleton (C n))
    (hgen : ∀ a : C 0, ∃ r : R, a = r • e)
    (P : D k ≃ₗ[R] F)
    (hμ : ∀ b : D k, μ (DirectSum.lof R _ _ ⟨(0, k), Nat.zero_add k⟩ (e ⊗ₜ[R] b)) = P b) :
    Function.Bijective μ := by
  classical
  let J : D k →ₗ[R] (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = k}, C i.val.1 ⊗[R] D i.val.2) :=
    (DirectSum.lof R _ _ ⟨(0, k), Nat.zero_add k⟩).comp
      (TensorProduct.mk R (C 0) (D k) e)
  let inv := J.comp P.symm.toLinearMap
  have hright : Function.RightInverse inv μ := by
    intro c
    exact (hμ (P.symm c)).trans (P.apply_symm_apply c)
  have hleft : inv.comp μ = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro a b
    change inv (μ (DirectSum.lof R _ _ i (a ⊗ₜ[R] b))) = DirectSum.lof R _ _ i (a ⊗ₜ[R] b)
    rcases i with ⟨⟨p, q⟩, hi⟩
    by_cases hp : p = 0
    · subst p
      have hq : q = k := by omega
      subst q
      obtain ⟨r, rfl⟩ := hgen a
      rw [← TensorProduct.smul_tmul']
      simp only [map_smul]
      apply congrArg (r • ·)
      change J (P.symm (μ (DirectSum.lof R _ _ ⟨(0,k), Nat.zero_add k⟩ (e ⊗ₜ[R] b)))) = J b
      rw [hμ, P.symm_apply_apply]
    · have : Subsingleton (C p) := hC p (by omega)
      have ha : a = 0 := Subsingleton.elim _ _
      rw [ha, TensorProduct.zero_tmul, map_zero, map_zero, map_zero]
  exact ⟨(show Function.LeftInverse inv μ from fun a ↦ LinearMap.congr_fun hleft a).injective,
    hright.surjective⟩

set_option backward.isDefEq.respectTransparency false in
/-- The degree cross map is bijective when the first factor is a point.
Source: Hatcher Theorem 3.15, p.217 base case. Positive point cohomology
vanishes and its zero group is generated by the constant-one class.
The product projection is a homeomorphism. Cross with this generator is
its pullback; the graded-module point lemma supplies the inverse identities. -/
private theorem degreeCrossMap_unique_bijective (X Y : TopCat.{u}) [Unique X] (k : ℕ) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  classical
  let e : crossProductSpace X Y ≃ₜ Y :=
    { toFun := Prod.snd
      invFun := fun y ↦ (default, y)
      left_inv := fun x ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_snd
      continuous_invFun := continuous_const.prodMk continuous_id }
  let P : cohomology R Y k ≃ₗ[R] cohomology R (crossProductSpace X Y) k :=
    ((actualCohomologyFunctor R k).mapIso (TopCat.isoOfHomeo e).op).toLinearEquiv
  refine degreeTensor_point_bijective R (fun n ↦ cohomology R X n)
    (fun n ↦ cohomology R Y n) (cohomology R (crossProductSpace X Y) k) k
    (degreeCrossMap R X Y k) (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X))
    (unique_positive_cohomology R X) ?_ P ?_
  · intro a
    obtain ⟨E, hE⟩ := unique_zero_cohomology_equiv R X
    obtain ⟨r, rfl⟩ := E.surjective a
    exact ⟨r, hE r⟩
  · exact degreeCrossMap_zero_left R X Y k

set_option backward.isDefEq.respectTransparency false in
private theorem actualPullback_comp_apply {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (c : cohomology R Z n) :
    cohomologyPullback R f n (cohomologyPullback R g n c) =
      cohomologyPullback R (f ≫ g) n c := by
  have h := (actualCohomologyFunctor R n).map_comp g.op f.op
  exact congrArg (fun t : cohomology R Z n ⟶ cohomology R X n ↦ t c) h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher p.217: the point cross-product calculation is invariant under a
contraction of the first factor. Retraction pullbacks identify its positive
cohomology with zero and its degree zero with the unit-generated point group.
After taking the product with Y, the same deformation identifies the second
projection pullback with the homeomorphic point-product projection. The
abstract point tensor lemma then applies to the actual cross map. -/
private theorem degreeCrossMap_deformation_point_bijective
    (A X Y : TopCat.{u}) [Unique A] (i : A ⟶ X) (r : X ⟶ A)
    (hri : i ≫ r = 𝟙 A) (H : TopCat.Homotopy (𝟙 X) (r ≫ i)) (k : ℕ) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  classical
  have hi (n : ℕ) := cohomologyPullback_isIso_of_deformationRetraction R i r hri H n
  let E (n : ℕ) : cohomology R X n ≃ₗ[R] cohomology R A n :=
    (asIso (cohomologyPullback R i n)).toLinearEquiv
  have hpositive (n : ℕ) (hn : 0 < n) : Subsingleton (cohomology R X n) := by
    have : Subsingleton (cohomology R A n) := unique_positive_cohomology R A n hn
    exact (E n).injective.subsingleton
  have hgen (a : cohomology R X 0) : ∃ t : R,
      a = t • cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X) := by
    obtain ⟨EA, hEA⟩ := unique_zero_cohomology_equiv R A
    obtain ⟨t, ht⟩ := EA.surjective (E 0 a)
    refine ⟨t, (E 0).injective ?_⟩
    rw [map_smul]
    change E 0 a = t • cohomologyPullback R i 0
      (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X))
    rw [actualPullback_unitClass, ← hEA, ht]
  let ip : crossProductSpace A Y ⟶ crossProductSpace X Y :=
    TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y))
  have hip : IsIso (cohomologyPullback R ip k) :=
    cohomologyPullback_prod_isIso_of_deformationRetraction R i r hri H Y k
  let I : cohomology R (crossProductSpace X Y) k ≃ₗ[R]
      cohomology R (crossProductSpace A Y) k :=
    (asIso (cohomologyPullback R ip k)).toLinearEquiv
  let e : crossProductSpace A Y ≃ₜ Y :=
    { toFun := Prod.snd
      invFun := fun y ↦ (default, y)
      left_inv := fun z ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_snd
      continuous_invFun := continuous_const.prodMk continuous_id }
  let Q : cohomology R Y k ≃ₗ[R] cohomology R (crossProductSpace A Y) k :=
    ((actualCohomologyFunctor R k).mapIso (TopCat.isoOfHomeo e).op).toLinearEquiv
  let P := Q.trans I.symm
  have hP (b : cohomology R Y k) :
      cohomologyPullback R (crossProductSnd X Y) k b = P b := by
    apply I.injective
    change cohomologyPullback R ip k (cohomologyPullback R (crossProductSnd X Y) k b) =
      I (I.symm (Q b))
    rw [I.apply_symm_apply, actualPullback_comp_apply]
    rfl
  refine degreeTensor_point_bijective R (fun n ↦ cohomology R X n)
    (fun n ↦ cohomology R Y n) (cohomology R (crossProductSpace X Y) k) k
    (degreeCrossMap R X Y k) (cocycleClass R (complex R X) 0 (MixedCup.unit_cocycle R X))
    hpositive hgen P ?_
  intro b
  exact (degreeCrossMap_zero_left R X Y k b).trans (hP b)

/-- Hatcher p.217: contraction to a point supplies the disk base case. -/
private theorem degreeCrossMap_contractible_bijective
    (X Y : TopCat.{u}) [ContractibleSpace X] (k : ℕ) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let A : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let i : A ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  let r : X ⟶ A := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  apply degreeCrossMap_deformation_point_bijective R A X Y i r
    (by ext a) H k

/-- Hatcher p.217: native closed cell disks are convex and contractible.
The universe lift is a homeomorphism and preserves this contraction. -/
private theorem degreeCrossMap_cellDisk_bijective (m : ℕ) (Y : TopCat.{u}) (k : ℕ) :
    Function.Bijective (degreeCrossMap R
      (TopCat.of (HolomorphicAnosov.CharacteristicCellComparison.CellDisk.{u} m)) Y k) := by
  have : ContractibleSpace (Metric.closedBall (0 : Fin m → ℝ) 1) :=
    (convex_closedBall (0 : Fin m → ℝ) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  have : ContractibleSpace (HolomorphicAnosov.CharacteristicCellComparison.CellDisk.{u} m) :=
    Homeomorph.ulift.contractibleSpace
  exact degreeCrossMap_contractible_bijective R _ Y k

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the fixed connecting map, with its chosen cochain quotient
construction. Source: Hatcher pp.199–200. Apply the short-complex connecting
naturality theorem to the actual restriction square of the pair map. -/
private theorem actualConnecting_natural {X Z : TopCat.{u}} {A : Set X} {B : Set Z}
    (f : X ⟶ Z) (hf : Set.MapsTo f A B) (p : ℕ)
    (a : cohomology R (TopCat.of B) p) :
    relativeCohomologyPullback R f hf (p + 1)
      (quotientConnecting R (singular_cochain_pair_shortExact R Z B) p a) =
    quotientConnecting R (singular_cochain_pair_shortExact R X A) p
      (cohomologyPullback R (pairSubspaceMap f hf) p a) := by
  let φ : ShortComplex.kernelSequence (pullback R (subspaceInclusion Z B)) ⟶
      ShortComplex.kernelSequence (pullback R (subspaceInclusion X A)) :=
    { τ₁ := relativePullback R f hf
      τ₂ := pullback R f
      τ₃ := pullback R (pairSubspaceMap f hf)
      comm₁₂ := by dsimp [relativePullback, ShortComplex.kernelSequence]; simp
      comm₂₃ := (pairRestrictionSquare R f hf).symm }
  exact congrArg (fun t ↦ t a)
    (cochain_quotient_connecting_naturality R φ
      (singular_cochain_pair_shortExact R Z B)
      (singular_cochain_pair_shortExact R X A) p)

set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous relative cross map commutes with the connecting map.
Source: Hatcher pp.216–217. Pullback of the first-factor connecting class is
the connecting class of its subspace pullback. Cup with the second projection
class commutes with connecting because that class is an ambient cocycle. -/
private theorem relativeCrossHomogeneous_connecting
    (X Y : TopCat.{u}) (A : Set X) (p q : ℕ)
    (a : cohomology R (TopCat.of A) p) (b : cohomology R Y q) :
    HEq
      (quotientConnecting R
        (singular_cochain_pair_shortExact R (crossProductSpace X Y) (crossPair X Y A)) (p + q)
        (MixedCup.descended_cup R (TopCat.of (crossPair X Y A)) ∅ false false p q
          (cohomologyPullback R
            (pairSubspaceMap (crossProductFst X Y) (fun _ hz ↦ hz)) p a)
          (cohomologyPullback R
            (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A) ≫ crossProductSnd X Y) q b)))
      (relativeCrossHomogeneous R X Y A (p + 1) q
        (quotientConnecting R (singular_cochain_pair_shortExact R X A) p a) b) := by
  have hc := connecting_cup_right R (crossProductSpace X Y) (crossPair X Y A) p q
    (cohomologyPullback R
      (pairSubspaceMap (crossProductFst X Y) (fun _ hz ↦ hz)) p a)
    (cohomologyPullback R (crossProductSnd X Y) q b)
  rw [actualPullback_comp_apply] at hc
  change HEq _ (MixedCup.descended_cup R (crossProductSpace X Y) (crossPair X Y A)
    true false (p + 1) q
    (relativeCohomologyPullback R (crossProductFst X Y) (fun _ hz ↦ hz) (p + 1)
      (quotientConnecting R (singular_cochain_pair_shortExact R X A) p a))
    (cohomologyPullback R (crossProductSnd X Y) q b))
  apply hc.trans
  apply heq_of_eq
  exact congrArg (fun t ↦ MixedCup.descended_cup R (crossProductSpace X Y)
      (crossPair X Y A) true false (p + 1) q t
      (cohomologyPullback R (crossProductSnd X Y) q b))
    (actualConnecting_natural R (A := crossPair X Y A) (B := A)
      (crossProductFst X Y) (fun _ hz ↦ hz) p a).symm

/-- Insert a direct sum along an injective change of its index set. -/
private def directSumIndexMap {ι κ : Type*} (B : κ → Type u)
    [∀ j, AddCommMonoid (B j)] [∀ j, Module R (B j)] (j : ι → κ) :
    (⨁ i, B (j i)) →ₗ[R] ⨁ t, B t := by
  classical
  exact DirectSum.toModule R _ _ fun i ↦ DirectSum.lof R _ _ (j i)

private theorem directSumIndexMap_lof {ι κ : Type*} (B : κ → Type u)
    [∀ t, AddCommMonoid (B t)] [∀ t, Module R (B t)]
    [di : DecidableEq ι] [dk : DecidableEq κ]
    (j : ι → κ) (i : ι) (x : B (j i)) :
    directSumIndexMap R B j (DirectSum.lof R _ _ i x) = DirectSum.lof R _ _ (j i) x := by
  have hi : di = Classical.decEq ι := Subsingleton.elim _ _
  have hk : dk = Classical.decEq κ := Subsingleton.elim _ _
  subst di dk
  simp only [directSumIndexMap, DirectSum.toModule_lof]

private theorem directSumIndexMap_component {ι κ : Type*} (B : κ → Type u)
    [∀ t, AddCommGroup (B t)] [∀ t, Module R (B t)]
    (j : ι → κ) (hj : Function.Injective j) (i : ι) (x : ⨁ i, B (j i)) :
    directSumIndexMap R B j x (j i) = x i := by
  classical
  have h : (DirectSum.component R _ B (j i)).comp (directSumIndexMap R B j) =
      DirectSum.component R _ (fun t ↦ B (j t)) i := by
    apply DirectSum.linearMap_ext
    intro a
    apply LinearMap.ext
    intro b
    by_cases ha : a = i
    · subst a
      simp [directSumIndexMap, DirectSum.component.lof_self]
    · have hja : j a ≠ j i := fun h ↦ ha (hj h)
      simp [directSumIndexMap, DirectSum.component.of, ha, hja]
  exact LinearMap.congr_fun h x

private theorem directSumIndexMap_off {ι κ : Type*} (B : κ → Type u)
    [∀ t, AddCommGroup (B t)] [∀ t, Module R (B t)]
    (j : ι → κ) (t : κ) (ht : t ∉ Set.range j) (x : ⨁ i, B (j i)) :
    directSumIndexMap R B j x t = 0 := by
  classical
  have h : (DirectSum.component R _ B t).comp (directSumIndexMap R B j) = 0 := by
    apply DirectSum.linearMap_ext
    intro a
    apply LinearMap.ext
    intro b
    have hja : j a ≠ t := fun h ↦ ht ⟨a, h⟩
    simp [directSumIndexMap, DirectSum.component.of, hja]
  exact LinearMap.congr_fun h x

/-- Hatcher p.218: exactness after extending the index set by terms where
the outgoing map is injective. On the image of the old index set, choose
component preimages using exactness. Outside it the kernel vanishes by
injectivity. Finite support makes the assembled preimage a direct sum. -/
private theorem directSum_shift_exact {ι κ : Type*}
    (A : ι → Type u) (B C : κ → Type u)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ t, AddCommGroup (B t)] [∀ t, Module R (B t)]
    [∀ t, AddCommGroup (C t)] [∀ t, Module R (C t)]
    (j : ι → κ) (hj : Function.Injective j)
    (f : ∀ i, A i →ₗ[R] B (j i)) (g : ∀ t, B t →ₗ[R] C t)
    (he : ∀ i, Function.Exact (f i) (g (j i)))
    (ho : ∀ t, t ∉ Set.range j → Function.Injective (g t)) :
    Function.Exact ((directSumIndexMap R B j).comp (DirectSum.lmap f)) (DirectSum.lmap g) := by
  classical
  intro x
  constructor
  · intro hx
    let y : ⨁ i, B (j i) := DFinsupp.comapDomain j hj x
    have hpre (i : (y.support : Set ι)) : ∃ a : A i.val, f i.val a = y i.val := by
      apply (he i.val (y i.val)).mp
      exact congrArg (fun z : ⨁ t, C t ↦ z (j i.val)) hx
    choose a ha using hpre
    let z : ⨁ i, A i := DFinsupp.mk y.support a
    have hf : DirectSum.lmap f z = y := by
      ext i
      by_cases hi : i ∈ y.support
      · simpa only [z, DirectSum.lmap_apply, DFinsupp.mk_of_mem hi] using ha ⟨i, hi⟩
      · have hz : y i = 0 := by simpa only [DFinsupp.mem_support_toFun, not_not] using hi
        simp only [z, DirectSum.lmap_apply, DFinsupp.mk_apply, hi, ↓reduceDIte, map_zero, hz]
    refine ⟨z, ?_⟩
    change directSumIndexMap R B j (DirectSum.lmap f z) = x
    rw [hf]
    ext t
    by_cases ht : t ∈ Set.range j
    · obtain ⟨i, rfl⟩ := ht
      exact directSumIndexMap_component R B j hj i y
    · rw [directSumIndexMap_off R B j t ht]
      apply ho t ht
      rw [map_zero]
      exact (congrArg (fun z : ⨁ t, C t ↦ z t) hx).symm
  · rintro ⟨z, rfl⟩
    ext t
    change g t (directSumIndexMap R B j (DirectSum.lmap f z) t) = 0
    by_cases ht : t ∈ Set.range j
    · obtain ⟨i, rfl⟩ := ht
      rw [directSumIndexMap_component R B j hj]
      exact (he i (f i (z i))).mpr ⟨z i, rfl⟩
    · rw [directSumIndexMap_off R B j t ht, map_zero]

private theorem directSumIndexMap_injective {ι κ : Type*} (B : κ → Type u)
    [∀ t, AddCommGroup (B t)] [∀ t, Module R (B t)]
    (j : ι → κ) (hj : Function.Injective j) :
    Function.Injective (directSumIndexMap R B j) := by
  intro x y h
  ext i
  exact (directSumIndexMap_component R B j hj i x).symm.trans
    ((congrArg (fun z : ⨁ t, B t ↦ z (j i)) h).trans
      (directSumIndexMap_component R B j hj i y))

private abbrev degreePairs (k : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = k}

private abbrev raiseDegreePair (k : ℕ) (i : degreePairs k) : degreePairs (k + 1) :=
  ⟨(i.val.1 + 1, i.val.2), by have := i.property; omega⟩

private theorem raiseDegreePair_injective (k : ℕ) : Function.Injective (raiseDegreePair k) := by
  intro i j h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  dsimp [raiseDegreePair] at h'
  apply Prod.ext
  · have := congrArg Prod.fst h'; dsimp at this; omega
  · simpa only using congrArg Prod.snd h'

private theorem raiseDegreePair_not_mem (k : ℕ) (i : degreePairs (k + 1))
    (hi : i ∉ Set.range (raiseDegreePair k)) : i.val.1 = 0 := by
  by_contra hp
  apply hi
  refine ⟨⟨(i.val.1 - 1, i.val.2), by have := i.property; omega⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · dsimp [raiseDegreePair]; omega
  · rfl

private abbrev degreeTensor (C D : ℕ → Type u)
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] (k : ℕ) :=
  ⨁ i : degreePairs k, C i.val.1 ⊗[R] D i.val.2

private def degreeTensorMap (A B D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (f : ∀ n, A n →ₗ[R] B n) (k : ℕ) :
    degreeTensor R A D k →ₗ[R] degreeTensor R B D k :=
  DirectSum.lmap fun i ↦ (f i.val.1).rTensor (D i.val.2)

private def degreeTensorConnecting (A B D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (d : ∀ n, A n →ₗ[R] B (n + 1)) (k : ℕ) :
    degreeTensor R A D k →ₗ[R] degreeTensor R B D (k + 1) :=
  (directSumIndexMap R (fun i : degreePairs (k + 1) ↦ B i.val.1 ⊗[R] D i.val.2)
    (raiseDegreePair k)).comp
    (DirectSum.lmap fun i : degreePairs k ↦ (d i.val.1).rTensor (D i.val.2))

/-- Exactness at the relative term in the total tensor long exact sequence.
Source: Hatcher p.218. Tensor each component with the free module D^q.
Positive first degrees come from connecting; the extra first-degree-zero
summand has injective forget map and contributes no kernel. -/
private theorem degreeTensor_connecting_exact
    (A B C D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] [∀ n, Module.Free R (D n)]
    (d : ∀ n, A n →ₗ[R] B (n + 1)) (g : ∀ n, B n →ₗ[R] C n)
    (he : ∀ n, Function.Exact (d n) (g (n + 1))) (hzero : Function.Injective (g 0)) (k : ℕ) :
    Function.Exact (degreeTensorConnecting R A B D d k) (degreeTensorMap R B C D g (k + 1)) := by
  apply directSum_shift_exact R _ _ _ (raiseDegreePair k) (raiseDegreePair_injective k)
  · intro i
    exact HolomorphicAnosov.AlgebraicTopology.tensor_exact_of_free R _ _ _ _ _ _ (he i.val.1)
  · intro i hi
    have hp := raiseDegreePair_not_mem k i hi
    change Function.Injective ((g i.val.1).rTensor (D i.val.2))
    rw [hp]
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := D i.val.2) (g 0) hzero

/-- Universe-general form of direct-sum exactness, obtained by the identity
index insertion in the preceding lemma. Source: Hatcher p.218. -/
private theorem directSum_lmap_exact_universe {ι : Type*} (A B C : ι → Type u)
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  classical
  have hid : directSumIndexMap R B id = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simp [directSumIndexMap]
  have hex := directSum_shift_exact R A B C id Function.injective_id f g h
    (fun i hi ↦ False.elim (hi ⟨i, rfl⟩))
  simpa only [hid, LinearMap.id_comp] using hex

/-- Fixed-degree tensor sums preserve exactness, by flatness of each second
factor and exactness of finite-support direct sums. Source: Hatcher p.218. -/
private theorem degreeTensor_map_exact
    (A B C D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] [∀ n, Module.Free R (D n)]
    (f : ∀ n, A n →ₗ[R] B n) (g : ∀ n, B n →ₗ[R] C n)
    (he : ∀ n, Function.Exact (f n) (g n)) (k : ℕ) :
    Function.Exact (degreeTensorMap R A B D f k) (degreeTensorMap R B C D g k) := by
  exact directSum_lmap_exact_universe R _ _ _ _ _
    (fun i : degreePairs k ↦ HolomorphicAnosov.AlgebraicTopology.tensor_exact_of_free R _ _ _ _ _ _ (he i.val.1))

/-- Exactness at the subspace term, where connecting raises the first degree.
Source: Hatcher p.218. Tensor exactness gives the kernel before reindexing;
the injective index insertion preserves it. -/
private theorem degreeTensor_map_connecting_exact
    (A B C D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] [∀ n, Module.Free R (D n)]
    (f : ∀ n, A n →ₗ[R] B n) (d : ∀ n, B n →ₗ[R] C (n + 1))
    (he : ∀ n, Function.Exact (f n) (d n)) (k : ℕ) :
    Function.Exact (degreeTensorMap R A B D f k) (degreeTensorConnecting R B C D d k) := by
  have h := directSum_lmap_exact_universe R
    (fun i : degreePairs k ↦ A i.val.1 ⊗[R] D i.val.2)
    (fun i : degreePairs k ↦ B i.val.1 ⊗[R] D i.val.2)
    (fun i : degreePairs k ↦ C (i.val.1 + 1) ⊗[R] D i.val.2)
    (fun i : degreePairs k ↦ (f i.val.1).rTensor (D i.val.2))
    (fun i : degreePairs k ↦ (d i.val.1).rTensor (D i.val.2))
    (fun i : degreePairs k ↦ HolomorphicAnosov.AlgebraicTopology.tensor_exact_of_free R _ _ _ _ _ _ (he i.val.1))
  let J := directSumIndexMap R
    (fun i : degreePairs (k + 1) ↦ C i.val.1 ⊗[R] D i.val.2) (raiseDegreePair k)
  exact h.comp_injective J
    (directSumIndexMap_injective R _ _ (raiseDegreePair_injective k)) J.map_zero

private theorem degreeTensor_map_injective
    (A B D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] [∀ n, Module.Free R (D n)]
    (f : ∀ n, A n →ₗ[R] B n) (hf : Function.Injective (f 0)) :
    Function.Injective (degreeTensorMap R A B D f 0) := by
  intro x y h
  ext i
  have hp : i.val.1 = 0 := by have := i.property; omega
  have hinj : Function.Injective ((f i.val.1).rTensor (D i.val.2)) := by
    rw [hp]
    exact Module.Flat.rTensor_preserves_injective_linearMap (f 0) hf
  apply hinj
  exact congrArg (fun z : degreeTensor R B D 0 ↦ z i) h

/-- The nonnegative long exact sequence of a pair, with its initial injection. -/
private structure PairExactSequence where
  rel : ℕ → ModuleCat.{u} R
  abs : ℕ → ModuleCat.{u} R
  sub : ℕ → ModuleCat.{u} R
  forget : ∀ n, rel n →ₗ[R] abs n
  restrict : ∀ n, abs n →ₗ[R] sub n
  connect : ∀ n, sub n →ₗ[R] rel (n + 1)
  initial : Function.Injective (forget 0)
  exact_abs : ∀ n, Function.Exact (forget n) (restrict n)
  exact_sub : ∀ n, Function.Exact (restrict n) (connect n)
  exact_rel : ∀ n, Function.Exact (connect n) (forget (n + 1))

private structure PairSequenceMap (S T : PairExactSequence R) where
  rel : ∀ n, S.rel n →ₗ[R] T.rel n
  abs : ∀ n, S.abs n →ₗ[R] T.abs n
  sub : ∀ n, S.sub n →ₗ[R] T.sub n
  forget : ∀ n, (T.forget n).comp (rel n) = (abs n).comp (S.forget n)
  restrict : ∀ n, (T.restrict n).comp (abs n) = (sub n).comp (S.restrict n)
  connect : ∀ n, (T.connect n).comp (sub n) = (rel (n + 1)).comp (S.connect n)

/-- Five-lemma passage from absolute and subspace isomorphisms to relative
isomorphisms, including degree zero. Source: Hatcher p.218. For positive degree
use the window H^n(X), H^n(A), H^(n+1)(X,A), H^(n+1)(X), H^(n+1)(A).
For zero use the initial three-term exact window and its injective first map. -/
private theorem PairSequenceMap.rel_bijective {S T : PairExactSequence R}
    (F : PairSequenceMap R S T) (ha : ∀ n, Function.Bijective (F.abs n))
    (hs : ∀ n, Function.Bijective (F.sub n)) : ∀ n, Function.Bijective (F.rel n) := by
  intro n
  cases n with
  | zero =>
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (S.forget 0) (S.restrict 0) (T.forget 0) (T.restrict 0)
      (F.rel 0) (F.abs 0) (F.sub 0) (F.forget 0) (F.restrict 0)
      (S.exact_abs 0) (T.exact_abs 0) (ha 0) (hs 0).injective S.initial T.initial
  | succ n =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (S.restrict n) (S.connect n) (S.forget (n + 1)) (S.restrict (n + 1))
      (T.restrict n) (T.connect n) (T.forget (n + 1)) (T.restrict (n + 1))
      (F.abs n) (F.sub n) (F.rel (n + 1)) (F.abs (n + 1)) (F.sub (n + 1))
      (F.restrict n) (F.connect n) (F.forget (n + 1)) (F.restrict (n + 1))
      (S.exact_sub n) (S.exact_rel n) (S.exact_abs (n + 1))
      (T.exact_sub n) (T.exact_rel n) (T.exact_abs (n + 1))
      (ha n).surjective (hs n) (ha (n + 1)) (hs (n + 1)).injective

/-- Five-lemma passage from relative and subspace isomorphisms to the ambient
isomorphism. Source: Hatcher p.218. In positive degree use the window ending
in the next relative term. In zero the preceding subspace term is zero and
the four-lemma injection and surjection arguments use the initial injections. -/
private theorem PairSequenceMap.abs_bijective {S T : PairExactSequence R}
    (F : PairSequenceMap R S T) (hr : ∀ n, Function.Bijective (F.rel n))
    (hs : ∀ n, Function.Bijective (F.sub n)) : ∀ n, Function.Bijective (F.abs n) := by
  intro n
  cases n with
  | zero =>
    constructor
    · intro x y h
      have hsub : S.restrict 0 x = S.restrict 0 y := (hs 0).injective (by
        simpa only [LinearMap.comp_apply] using
          (LinearMap.congr_fun (F.restrict 0) x).symm.trans
            ((congrArg (T.restrict 0) h).trans (LinearMap.congr_fun (F.restrict 0) y)))
      have hz : S.restrict 0 (x - y) = 0 := by rw [map_sub, hsub, sub_self]
      obtain ⟨r, hrr⟩ := (S.exact_abs 0 (x - y)).mp hz
      have hfr : F.rel 0 r = 0 := T.initial (by
        rw [map_zero]
        change (T.forget 0).comp (F.rel 0) r = 0
        rw [F.forget]
        change F.abs 0 (S.forget 0 r) = 0
        rw [hrr, map_sub, h, sub_self])
      have hzero : r = 0 := (hr 0).injective (hfr.trans (map_zero (F.rel 0)).symm)
      have : x - y = 0 := hrr.symm.trans (hzero ▸ map_zero (S.forget 0))
      exact sub_eq_zero.mp this
    · exact LinearMap.surjective_of_surjective_of_surjective_of_injective
        (S.forget 0) (S.restrict 0) (S.connect 0)
        (T.forget 0) (T.restrict 0) (T.connect 0)
        (F.rel 0) (F.abs 0) (F.sub 0) (F.rel 1)
        (F.forget 0) (F.restrict 0) (F.connect 0)
        (S.exact_sub 0) (T.exact_abs 0) (T.exact_sub 0)
        (hr 0).surjective (hs 0).surjective (hr 1).injective
  | succ n =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (S.connect n) (S.forget (n + 1)) (S.restrict (n + 1)) (S.connect (n + 1))
      (T.connect n) (T.forget (n + 1)) (T.restrict (n + 1)) (T.connect (n + 1))
      (F.sub n) (F.rel (n + 1)) (F.abs (n + 1)) (F.sub (n + 1)) (F.rel (n + 2))
      (F.connect n) (F.forget (n + 1)) (F.restrict (n + 1)) (F.connect (n + 1))
      (S.exact_rel n) (S.exact_abs (n + 1)) (S.exact_sub (n + 1))
      (T.exact_rel n) (T.exact_abs (n + 1)) (T.exact_sub (n + 1))
      (hs n).surjective (hr (n + 1)) (hs (n + 1)) (hr (n + 2)).injective

set_option backward.isDefEq.respectTransparency false in
/-- The fixed quotient connecting maps form the ordinary long exact pair
sequence. Source: Hatcher pp.199–200. Use the kernel cochain short exact row;
in degree zero its inclusion is injective because there are no incoming
boundaries. All other exactness clauses are transported homology exactness. -/
private def actualPairExactSequence (X : TopCat.{u}) (A : Set X) : PairExactSequence R where
  rel n := relativeCohomology R X A n
  abs n := cohomology R X n
  sub n := cohomology R (TopCat.of A) n
  forget n := (relativeForget R X A n).hom
  restrict n := (cohomologyPullback R (subspaceInclusion X A) n).hom
  connect n := (quotientConnecting R (singular_cochain_pair_shortExact R X A) n).hom
  initial := by
    obtain ⟨conn, hex, _⟩ := (relative_cohomology_pair_theorems R).1
    exact (hex X A).1
  exact_abs n := LinearMap.exact_iff.mpr
    (cochain_quotient_exact_of_shortExact R _ (singular_cochain_pair_shortExact R X A) n).symm
  exact_sub n := LinearMap.exact_iff.mpr
    (cochain_quotient_connecting_exact R _ (singular_cochain_pair_shortExact R X A) n).1.symm
  exact_rel n := LinearMap.exact_iff.mpr
    (cochain_quotient_connecting_exact R _ (singular_cochain_pair_shortExact R X A) n).2.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 60000 in
/-- Tensor a nonnegative pair sequence degreewise with a free graded module.
Source: Hatcher p.218. Flatness and direct-sum exactness give the three exact
positions; the zero-degree initial map remains injective under tensoring. -/
private def tensorPairExactSequence (S : PairExactSequence R) (D : ℕ → ModuleCat.{u} R)
    [∀ n, Module.Free R (D n)] : PairExactSequence R where
  rel n := ModuleCat.of R (degreeTensor R (fun p ↦ S.rel p) (fun q ↦ D q) n)
  abs n := ModuleCat.of R (degreeTensor R (fun p ↦ S.abs p) (fun q ↦ D q) n)
  sub n := ModuleCat.of R (degreeTensor R (fun p ↦ S.sub p) (fun q ↦ D q) n)
  forget n := degreeTensorMap R (fun p ↦ S.rel p) (fun p ↦ S.abs p) (fun q ↦ D q) S.forget n
  restrict n := degreeTensorMap R (fun p ↦ S.abs p) (fun p ↦ S.sub p) (fun q ↦ D q) S.restrict n
  connect n := degreeTensorConnecting R (fun p ↦ S.sub p) (fun p ↦ S.rel p) (fun q ↦ D q) S.connect n
  initial := degreeTensor_map_injective R _ _ (fun q ↦ D q) S.forget S.initial
  exact_abs n := degreeTensor_map_exact R _ _ _ (fun q ↦ D q) S.forget S.restrict S.exact_abs n
  exact_sub n := degreeTensor_map_connecting_exact R (fun p ↦ S.abs p) (fun p ↦ S.sub p) (fun p ↦ S.rel p) (fun q ↦ D q) S.restrict S.connect S.exact_sub n
  exact_rel n := degreeTensor_connecting_exact R (fun p ↦ S.sub p) (fun p ↦ S.rel p) (fun p ↦ S.abs p) (fun q ↦ D q) S.connect S.forget S.exact_rel S.initial n

/-- The degreewise tensor sum of a homogeneous bilinear map. -/
private def degreeTensorLift (A D E : ℕ → ModuleCat.{u} R)
    (μ : ∀ p q, A p →ₗ[R] D q →ₗ[R] E (p + q)) (k : ℕ) :
    degreeTensor R (fun n ↦ A n) (fun n ↦ D n) k →ₗ[R] E k := by
  classical
  exact DirectSum.toModule R _ _ fun i ↦
    (LinearEquiv.cast (R := R) (M := fun n ↦ E n) i.property).toLinearMap.comp
      (TensorProduct.lift (μ i.val.1 i.val.2))

private theorem degreeTensorLift_pure (A D E : ℕ → ModuleCat.{u} R)
    (μ : ∀ p q, A p →ₗ[R] D q →ₗ[R] E (p + q)) (k : ℕ)
    (i : degreePairs k) (a : A i.val.1) (b : D i.val.2) :
    degreeTensorLift R A D E μ k (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) =
      cast (congrArg (fun n ↦ (E n : Type u)) i.property) (μ i.val.1 i.val.2 a b) := by
  simp only [degreeTensorLift, DirectSum.toModule_lof, LinearMap.comp_apply, TensorProduct.lift.tmul]
  rfl

/-- A homogeneous naturality square remains commutative after degreewise
sum and tensor descent. Source: Hatcher pp.216–217, linear extension from
pure cross products. The total index equality identifies the target degrees. -/
private theorem degreeTensorLift_natural (A B D E F : ℕ → ModuleCat.{u} R)
    (μ : ∀ p q, A p →ₗ[R] D q →ₗ[R] E (p + q))
    (ν : ∀ p q, B p →ₗ[R] D q →ₗ[R] F (p + q))
    (f : ∀ n, A n →ₗ[R] B n) (g : ∀ n, E n →ₗ[R] F n)
    (h : ∀ p q a b, g (p + q) (μ p q a b) = ν p q (f p a) b) (k : ℕ) :
    (g k).comp (degreeTensorLift R A D E μ k) =
      (degreeTensorLift R B D F ν k).comp
        (degreeTensorMap R (fun n ↦ A n) (fun n ↦ B n) (fun n ↦ D n) f k) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  rcases i with ⟨⟨p, q⟩, rfl⟩
  simp only [LinearMap.comp_apply, degreeTensorMap, DirectSum.lmap_lof, LinearMap.rTensor_tmul,
    degreeTensorLift_pure]
  exact h p q a b

set_option backward.isDefEq.respectTransparency false in
private theorem degreeTensorConnecting_pure (A B D : ℕ → ModuleCat.{u} R)
    (d : ∀ n, A n →ₗ[R] B (n + 1)) (k : ℕ) (i : degreePairs k)
    (a : A i.val.1) (b : D i.val.2) :
    degreeTensorConnecting R (fun n ↦ A n) (fun n ↦ B n) (fun n ↦ D n) d k
      (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) =
    DirectSum.lof R _ _ (raiseDegreePair k i) (d i.val.1 a ⊗ₜ[R] b) := by
  classical
  change directSumIndexMap R (fun j : degreePairs (k + 1) ↦ B j.val.1 ⊗[R] D j.val.2)
    (raiseDegreePair k)
    (DirectSum.lmap (fun j : degreePairs k ↦ (d j.val.1).rTensor (D j.val.2))
      (DirectSum.lof R _ _ i (a ⊗ₜ[R] b))) = _
  rw [DirectSum.lmap_lof, LinearMap.rTensor_tmul]
  exact directSumIndexMap_lof R
    (fun j : degreePairs (k + 1) ↦ B j.val.1 ⊗[R] D j.val.2)
    (raiseDegreePair k) i (d i.val.1 a ⊗ₜ[R] b)

set_option backward.isDefEq.respectTransparency false in
/-- The connecting square survives tensor descent with the degree shift.
Source: Hatcher p.218. Its homogeneous square is stated with heterogeneous
equality to identify (p+q)+1 and (p+1)+q; the defining cast of the total map
is exactly this identification. -/
private theorem degreeTensorLift_connecting (A B D E F : ℕ → ModuleCat.{u} R)
    (μ : ∀ p q, A p →ₗ[R] D q →ₗ[R] E (p + q))
    (ν : ∀ p q, B p →ₗ[R] D q →ₗ[R] F (p + q))
    (d : ∀ n, A n →ₗ[R] B (n + 1)) (g : ∀ n, E n →ₗ[R] F (n + 1))
    (h : ∀ p q a b, HEq (g (p + q) (μ p q a b)) (ν (p + 1) q (d p a) b)) (k : ℕ) :
    (g k).comp (degreeTensorLift R A D E μ k) =
      (degreeTensorLift R B D F ν (k + 1)).comp
        (degreeTensorConnecting R (fun n ↦ A n) (fun n ↦ B n) (fun n ↦ D n) d k) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  rcases i with ⟨⟨p, q⟩, rfl⟩
  simp only [LinearMap.comp_apply, degreeTensorConnecting_pure, degreeTensorLift_pure]
  apply eq_of_heq
  apply (h p q a b).trans
  exact (cast_heq _ _).symm

set_option backward.isDefEq.respectTransparency false in
private def absoluteCrossHomogeneous (X Y : TopCat.{u}) (p q : ℕ) :
    cohomology R X p →ₗ[R] cohomology R Y q →ₗ[R]
      cohomology R (crossProductSpace X Y) (p + q) :=
  (MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false p q).compl₁₂
    (cohomologyPullback R (crossProductFst X Y) p).hom
    (cohomologyPullback R (crossProductSnd X Y) q).hom

set_option backward.isDefEq.respectTransparency false in
private def subspaceCrossHomogeneous (X Y : TopCat.{u}) (A : Set X) (p q : ℕ) :
    cohomology R (TopCat.of A) p →ₗ[R] cohomology R Y q →ₗ[R]
      cohomology R (TopCat.of (crossPair X Y A)) (p + q) :=
  (MixedCup.descended_cup R (TopCat.of (crossPair X Y A)) ∅ false false p q).compl₁₂
    (cohomologyPullback R
      (pairSubspaceMap (crossProductFst X Y) (fun _ hz ↦ hz)) p).hom
    (cohomologyPullback R
      (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A) ≫ crossProductSnd X Y) q).hom

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the product subspace commutes with homogeneous cross
products. Source: Hatcher p.216. Naturality of cup and composition of the two
projection pullbacks identify the two expressions. -/
private theorem absoluteCrossHomogeneous_restrict (X Y : TopCat.{u}) (A : Set X)
    (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q) :
    cohomologyPullback R (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A))
      (p + q) (absoluteCrossHomogeneous R X Y p q a b) =
    subspaceCrossHomogeneous R X Y A p q
      (cohomologyPullback R (subspaceInclusion X A) p a) b := by
  have h := MixedCup.descended_cup_naturality R
    (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A)) ∅ ∅
    (Set.mapsTo_empty _ _) false false p q
    (cohomologyPullback R (crossProductFst X Y) p a)
    (cohomologyPullback R (crossProductSnd X Y) q b)
  change cohomologyPullback R _ (p + q) _ =
    MixedCup.descended_cup R (TopCat.of (crossPair X Y A)) ∅ false false p q
      (cohomologyPullback R _ p (cohomologyPullback R (crossProductFst X Y) p a))
      (cohomologyPullback R _ q (cohomologyPullback R (crossProductSnd X Y) q b)) at h
  rw [actualPullback_comp_apply, actualPullback_comp_apply] at h
  apply h.trans
  exact congrArg (fun t ↦ MixedCup.descended_cup R (TopCat.of (crossPair X Y A))
    ∅ false false p q t
    (cohomologyPullback R
      (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A) ≫ crossProductSnd X Y) q b))
    (actualPullback_comp_apply R
      (pairSubspaceMap (crossProductFst X Y) (fun _ hz ↦ hz))
      (subspaceInclusion X A) p a).symm

set_option backward.isDefEq.respectTransparency false in
private def relativeDegreeCrossMap (X Y : TopCat.{u}) (A : Set X) (k : ℕ) :=
  degreeTensorLift R (fun n ↦ relativeCohomology R X A n) (fun n ↦ cohomology R Y n)
    (fun n ↦ relativeCohomology R (crossProductSpace X Y) (crossPair X Y A) n)
    (relativeCrossHomogeneous R X Y A) k

set_option backward.isDefEq.respectTransparency false in
private def subspaceDegreeCrossMap (X Y : TopCat.{u}) (A : Set X) (k : ℕ) :=
  degreeTensorLift R (fun n ↦ cohomology R (TopCat.of A) n) (fun n ↦ cohomology R Y n)
    (fun n ↦ cohomology R (TopCat.of (crossPair X Y A)) n)
    (subspaceCrossHomogeneous R X Y A) k

set_option backward.isDefEq.respectTransparency false in
/-- Cross products give a morphism from the tensor pair sequence to the
product-pair sequence. Source: Hatcher p.218. The forgetful, restriction, and
connecting squares follow on pure tensors from cup naturality and the cup
Leibniz rule, and linear descent preserves those squares. -/
private def crossPairSequenceMap (X Y : TopCat.{u}) (A : Set X)
    [∀ n, Module.Free R (cohomology R Y n)] :
    PairSequenceMap R
      (tensorPairExactSequence R (actualPairExactSequence R X A) (fun n ↦ cohomology R Y n))
      (actualPairExactSequence R (crossProductSpace X Y) (crossPair X Y A)) where
  rel := relativeDegreeCrossMap R X Y A
  abs := degreeCrossMap R X Y
  sub := subspaceDegreeCrossMap R X Y A
  forget k := degreeTensorLift_natural R
    (fun n ↦ relativeCohomology R X A n) (fun n ↦ cohomology R X n)
    (fun n ↦ cohomology R Y n)
    (fun n ↦ relativeCohomology R (crossProductSpace X Y) (crossPair X Y A) n)
    (fun n ↦ cohomology R (crossProductSpace X Y) n)
    (relativeCrossHomogeneous R X Y A) (absoluteCrossHomogeneous R X Y)
    (fun n ↦ (relativeForget R X A n).hom)
    (fun n ↦ (relativeForget R (crossProductSpace X Y) (crossPair X Y A) n).hom)
    (relativeCrossHomogeneous_forget R X Y A) k
  restrict k := degreeTensorLift_natural R
    (fun n ↦ cohomology R X n) (fun n ↦ cohomology R (TopCat.of A) n)
    (fun n ↦ cohomology R Y n)
    (fun n ↦ cohomology R (crossProductSpace X Y) n)
    (fun n ↦ cohomology R (TopCat.of (crossPair X Y A)) n)
    (absoluteCrossHomogeneous R X Y) (subspaceCrossHomogeneous R X Y A)
    (fun n ↦ (cohomologyPullback R (subspaceInclusion X A) n).hom)
    (fun n ↦ (cohomologyPullback R
      (subspaceInclusion (crossProductSpace X Y) (crossPair X Y A)) n).hom)
    (absoluteCrossHomogeneous_restrict R X Y A) k
  connect k := degreeTensorLift_connecting R
    (fun n ↦ cohomology R (TopCat.of A) n) (fun n ↦ relativeCohomology R X A n)
    (fun n ↦ cohomology R Y n)
    (fun n ↦ cohomology R (TopCat.of (crossPair X Y A)) n)
    (fun n ↦ relativeCohomology R (crossProductSpace X Y) (crossPair X Y A) n)
    (subspaceCrossHomogeneous R X Y A) (relativeCrossHomogeneous R X Y A)
    (fun n ↦ (quotientConnecting R (singular_cochain_pair_shortExact R X A) n).hom)
    (fun n ↦ (quotientConnecting R
      (singular_cochain_pair_shortExact R (crossProductSpace X Y) (crossPair X Y A)) n).hom)
    (relativeCrossHomogeneous_connecting R X Y A) k

private def crossPairHomeo (X Y : TopCat.{u}) (A : Set X) :
    TopCat.of (crossPair X Y A) ≃ₜ crossProductSpace (TopCat.of A) Y where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

private theorem degreeTensorMap_id (A D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)] (k : ℕ) :
    degreeTensorMap R A A D (fun _ ↦ LinearMap.id) k = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, degreeTensorMap, DirectSum.lmap_lof,
    LinearMap.rTensor_tmul, LinearMap.id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem subspaceCrossHomogeneous_eq (X Y : TopCat.{u}) (A : Set X)
    (p q : ℕ) (a : cohomology R (TopCat.of A) p) (b : cohomology R Y q) :
    cohomologyPullback R (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom (p + q)
      (absoluteCrossHomogeneous R (TopCat.of A) Y p q a b) =
    subspaceCrossHomogeneous R X Y A p q a b := by
  have h := MixedCup.descended_cup_naturality R
    (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom ∅ ∅
    (Set.mapsTo_empty _ _) false false p q
    (cohomologyPullback R (crossProductFst (TopCat.of A) Y) p a)
    (cohomologyPullback R (crossProductSnd (TopCat.of A) Y) q b)
  change cohomologyPullback R _ (p + q) _ =
    MixedCup.descended_cup R (TopCat.of (crossPair X Y A)) ∅ false false p q
      (cohomologyPullback R _ p (cohomologyPullback R _ p a))
      (cohomologyPullback R _ q (cohomologyPullback R _ q b)) at h
  rw [actualPullback_comp_apply, actualPullback_comp_apply] at h
  have hf : (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom ≫
      crossProductFst (TopCat.of A) Y =
      pairSubspaceMap (crossProductFst X Y) (fun _ hz ↦ hz) := by ext z; rfl
  have hg : (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom ≫
      crossProductSnd (TopCat.of A) Y =
      subspaceInclusion (crossProductSpace X Y) (crossPair X Y A) ≫
        crossProductSnd X Y := by ext z; rfl
  rw [hf, hg] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem subspaceDegreeCrossMap_eq (X Y : TopCat.{u}) (A : Set X) (k : ℕ) :
    subspaceDegreeCrossMap R X Y A k =
      (cohomologyPullback R (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom k).hom.comp
        (degreeCrossMap R (TopCat.of A) Y k) := by
  have h := degreeTensorLift_natural R
    (fun n ↦ cohomology R (TopCat.of A) n) (fun n ↦ cohomology R (TopCat.of A) n)
    (fun n ↦ cohomology R Y n)
    (fun n ↦ cohomology R (crossProductSpace (TopCat.of A) Y) n)
    (fun n ↦ cohomology R (TopCat.of (crossPair X Y A)) n)
    (absoluteCrossHomogeneous R (TopCat.of A) Y) (subspaceCrossHomogeneous R X Y A)
    (fun _ ↦ LinearMap.id)
    (fun n ↦ (cohomologyPullback R (TopCat.isoOfHomeo (crossPairHomeo X Y A)).hom n).hom)
    (subspaceCrossHomogeneous_eq R X Y A) k
  rw [degreeTensorMap_id, LinearMap.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem subspaceDegreeCrossMap_bijective (X Y : TopCat.{u}) (A : Set X) (k : ℕ)
    (h : Function.Bijective (degreeCrossMap R (TopCat.of A) Y k)) :
    Function.Bijective (subspaceDegreeCrossMap R X Y A k) := by
  rw [subspaceDegreeCrossMap_eq]
  let E := ((actualCohomologyFunctor R k).mapIso
    (TopCat.isoOfHomeo (crossPairHomeo X Y A)).op).toLinearEquiv
  exact E.bijective.comp h

set_option backward.isDefEq.respectTransparency false in
/-- The pair five lemma transfers absolute cross-product isomorphisms to the
relative cross product. Source: Hatcher p.218. Identify the product subspace
with A × Y, then apply the five lemma to the constructed exact-sequence map. -/
private theorem relativeDegreeCrossMap_bijective_of_absolute
    (X Y : TopCat.{u}) (A : Set X) [∀ n, Module.Free R (cohomology R Y n)]
    (hX : ∀ n, Function.Bijective (degreeCrossMap R X Y n))
    (hA : ∀ n, Function.Bijective (degreeCrossMap R (TopCat.of A) Y n)) :
    ∀ n, Function.Bijective (relativeDegreeCrossMap R X Y A n) :=
  PairSequenceMap.rel_bijective R (crossPairSequenceMap R X Y A) hX
    (fun n ↦ subspaceDegreeCrossMap_bijective R X Y A n (hA n))

set_option backward.isDefEq.respectTransparency false in
/-- The pair five lemma transfers relative and subspace cross-product
isomorphisms to the ambient cross product. Source: Hatcher p.218. The exact
sequence map above has isomorphisms in the four neighboring terms. -/
private theorem degreeCrossMap_bijective_of_relative
    (X Y : TopCat.{u}) (A : Set X) [∀ n, Module.Free R (cohomology R Y n)]
    (hrel : ∀ n, Function.Bijective (relativeDegreeCrossMap R X Y A n))
    (hA : ∀ n, Function.Bijective (degreeCrossMap R (TopCat.of A) Y n)) :
    ∀ n, Function.Bijective (degreeCrossMap R X Y n) :=
  PairSequenceMap.abs_bijective R (crossPairSequenceMap R X Y A) hrel
    (fun n ↦ subspaceDegreeCrossMap_bijective R X Y A n (hA n))

private instance degreePairs_finite (k : ℕ) : Finite (degreePairs k) := by
  apply Finite.of_injective (fun i : degreePairs k ↦ (⟨i.val.1, by have := i.property; omega⟩ : Fin (k + 1)))
  intro i j hij
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val hij
  · have hp := congrArg Fin.val hij
    change i.val.1 = j.val.1 at hp
    have hi := i.property
    have hj := j.property
    omega

/-- Tensor products distribute over a finite family of component maps.
Source: Hatcher p.217. Identify the first module with the finite product by
its given component maps, then use finite-product tensor distribution. -/
private theorem tensorPiMap_bijective {ι : Type u} [Fintype ι]
    (A D : Type u) (B : ι → Type u)
    [AddCommGroup A] [Module R A] [AddCommGroup D] [Module R D]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (f : ∀ i, A →ₗ[R] B i) (hf : Function.Bijective (LinearMap.pi f)) :
    Function.Bijective (LinearMap.pi (fun i ↦ (f i).rTensor D)) := by
  classical
  let E := (LinearEquiv.ofBijective (LinearMap.pi f) hf).rTensor D
  let P := TensorProduct.piLeft R D B
  have h : LinearMap.pi (fun i ↦ (f i).rTensor D) = P.toLinearMap.comp E.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    ext i
    simp [E, P, TensorProduct.piLeft, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]
  rw [h]
  exact P.bijective.comp E.bijective

/-- Finite cell comparison isomorphisms remain isomorphisms after tensoring
and collecting a total degree. Source: Hatcher p.217. Tensor distribution gives
an isomorphism in each (p,q) summand. Degree pairs form a finite set, so choose
one inverse tensor in each summand and assemble their direct sum. -/
private theorem degreeTensorFamilyMap_bijective {ι : Type u} [Fintype ι]
    (A D : ℕ → Type u) (B : ι → ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    [∀ i n, AddCommGroup (B i n)] [∀ i n, Module R (B i n)]
    (f : ∀ n i, A n →ₗ[R] B i n)
    (hf : ∀ n, Function.Bijective (LinearMap.pi (f n))) (k : ℕ) :
    Function.Bijective (LinearMap.pi fun i ↦ degreeTensorMap R A (B i) D (fun n ↦ f n i) k) := by
  classical
  let := Fintype.ofFinite (degreePairs k)
  have he (j : degreePairs k) := tensorPiMap_bijective R (A j.val.1) (D j.val.2)
    (fun i ↦ B i j.val.1) (f j.val.1) (hf j.val.1)
  constructor
  · intro x y h
    ext j
    apply (he j).injective
    funext i
    exact congrArg (fun z : ∀ i, degreeTensor R (B i) D k ↦ z i j) h
  · intro z
    choose t ht using fun j : degreePairs k ↦ (he j).surjective (fun i ↦ z i j)
    let x : degreeTensor R A D k := (DirectSum.linearEquivFunOnFintype R _ _).symm t
    refine ⟨x, ?_⟩
    ext i j
    have hx : x j = t j := congrFun
      ((DirectSum.linearEquivFunOnFintype R _ _).apply_symm_apply t) j
    change (f j.val.1 i).rTensor (D j.val.2) (x j) = z i j
    rw [hx]
    exact congrFun (ht j) i

set_option backward.isDefEq.respectTransparency false in
private theorem actualRelativePullback_comp_apply {X Z W : TopCat.{u}}
    {A : Set X} {B : Set Z} {C : Set W} (f : X ⟶ Z) (g : Z ⟶ W)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ)
    (a : relativeCohomology R W C n) :
    relativeCohomologyPullback R f hf n (relativeCohomologyPullback R g hg n a) =
      relativeCohomologyPullback R (f ≫ g) (hg.comp hf) n a := by
  have hc := relativePullback_comp R f g hf hg
  have h := congrArg (fun t ↦ quotientMap R t n) hc
  rw [HolomorphicAnosov.CharacteristicCellComparison.quotientMap_comp_bridge] at h
  exact (congrArg (fun t ↦ t a) h).symm

private def crossProductMap {X Z : TopCat.{u}} (f : X ⟶ Z) (Y : TopCat.{u}) :
    crossProductSpace X Y ⟶ crossProductSpace Z Y :=
  TopCat.ofHom (f.hom.prodMap (ContinuousMap.id Y))

set_option backward.isDefEq.respectTransparency false in
/-- First-factor maps of pairs preserve the relative cross product.
Source: Hatcher p.216, naturality of cross products. Cup naturality and the
commuting projection squares identify both pulled-back factors. -/
private theorem relativeCrossHomogeneous_natural {X Z : TopCat.{u}} (Y : TopCat.{u})
    {A : Set X} {B : Set Z} (f : X ⟶ Z) (hf : Set.MapsTo f A B)
    (p q : ℕ) (a : relativeCohomology R Z B p) (b : cohomology R Y q) :
    relativeCohomologyPullback R (crossProductMap f Y) (fun _z hz ↦ hf hz) (p + q)
      (relativeCrossHomogeneous R Z Y B p q a b) =
    relativeCrossHomogeneous R X Y A p q (relativeCohomologyPullback R f hf p a) b := by
  have h := MixedCup.descended_cup_naturality R (crossProductMap f Y)
    (crossPair X Y A) (crossPair Z Y B) (fun z hz ↦ hf hz) true false p q
    (relativeCohomologyPullback R (crossProductFst Z Y) (fun _ hz ↦ hz) p a)
    (cohomologyPullback R (crossProductSnd Z Y) q b)
  change relativeCohomologyPullback R (crossProductMap f Y) (fun z hz ↦ hf hz) (p + q) _ =
    MixedCup.descended_cup R (crossProductSpace X Y) (crossPair X Y A) true false p q
      (relativeCohomologyPullback R (crossProductMap f Y) (fun z hz ↦ hf hz) p
        (relativeCohomologyPullback R (crossProductFst Z Y) (fun _ hz ↦ hz) p a))
      (cohomologyPullback R _ q (cohomologyPullback R (crossProductSnd Z Y) q b)) at h
  have ha := actualRelativePullback_comp_apply R (A := crossPair X Y A)
    (B := crossPair Z Y B) (C := B) (crossProductMap f Y) (crossProductFst Z Y)
    (fun z hz ↦ hf hz) (fun _ hz ↦ hz) p a
  have hb := actualRelativePullback_comp_apply R (A := crossPair X Y A)
    (B := A) (C := B) (crossProductFst X Y) f (fun _ hz ↦ hz) hf p a
  apply h.trans
  exact congrArg₂ (fun aa bb ↦ MixedCup.descended_cup R (crossProductSpace X Y) (crossPair X Y A)
    true false p q aa bb) (ha.trans hb.symm)
    (actualPullback_comp_apply R (crossProductMap f Y) (crossProductSnd Z Y) q b)

set_option backward.isDefEq.respectTransparency false in
private theorem relativeDegreeCrossMap_natural {X Z : TopCat.{u}} (Y : TopCat.{u})
    {A : Set X} {B : Set Z} (f : X ⟶ Z) (hf : Set.MapsTo f A B) (k : ℕ) :
    (relativeCohomologyPullback R (crossProductMap f Y) (fun _z hz ↦ hf hz) k).hom.comp
      (relativeDegreeCrossMap R Z Y B k) =
    (relativeDegreeCrossMap R X Y A k).comp
      (degreeTensorMap R (fun n ↦ relativeCohomology R Z B n)
        (fun n ↦ relativeCohomology R X A n) (fun n ↦ cohomology R Y n)
        (fun n ↦ (relativeCohomologyPullback R f hf n).hom) k) :=
  degreeTensorLift_natural R
    (fun n ↦ relativeCohomology R Z B n) (fun n ↦ relativeCohomology R X A n)
    (fun n ↦ cohomology R Y n)
    (fun n ↦ relativeCohomology R (crossProductSpace Z Y) (crossPair Z Y B) n)
    (fun n ↦ relativeCohomology R (crossProductSpace X Y) (crossPair X Y A) n)
    (relativeCrossHomogeneous R Z Y B) (relativeCrossHomogeneous R X Y A)
    (fun n ↦ (relativeCohomologyPullback R f hf n).hom)
    (fun n ↦ (relativeCohomologyPullback R (crossProductMap f Y) (fun _ hz ↦ hf hz) n).hom)
    (relativeCrossHomogeneous_natural R Y f hf) k


set_option backward.isDefEq.respectTransparency false in
/-- Cross-product isomorphisms assemble through a finite family of pair
comparison maps. Source: Hatcher Proposition 3.17, p.217. The comparison maps
are isomorphisms on relative cohomology before and after product with Y.
Finite-product tensor distribution gives the remaining comparison isomorphism;
relative cross-product naturality makes the resulting square commute. -/
private theorem relativeDegreeCrossMap_bijective_of_family {ι : Type u} [Fintype ι]
    (X : ι → TopCat.{u}) (A : ∀ i, Set (X i)) (Z Y : TopCat.{u}) (B : Set Z)
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Set.MapsTo (f i) (A i) B)
    (hc : ∀ n, Function.Bijective
      (LinearMap.pi fun i ↦ (relativeCohomologyPullback R (f i) (hf i) n).hom))
    (hp : ∀ n, Function.Bijective (LinearMap.pi fun i ↦
      (relativeCohomologyPullback R (A := crossPair (X i) Y (A i)) (B := crossPair Z Y B) (crossProductMap (f i) Y)
        (fun _z hz ↦ hf i hz) n).hom))
    (hX : ∀ i n, Function.Bijective (relativeDegreeCrossMap R (X i) Y (A i) n))
    (k : ℕ) : Function.Bijective (relativeDegreeCrossMap R Z Y B k) := by
  let F := LinearMap.pi fun i ↦ degreeTensorMap R
    (fun n ↦ relativeCohomology R Z B n) (fun n ↦ relativeCohomology R (X i) (A i) n)
    (fun n ↦ cohomology R Y n) (fun n ↦ (relativeCohomologyPullback R (f i) (hf i) n).hom) k
  let G := LinearMap.pi fun i ↦
    (relativeCohomologyPullback R (A := crossPair (X i) Y (A i)) (B := crossPair Z Y B) (crossProductMap (f i) Y) (fun z hz ↦ hf i hz) k).hom
  let H := LinearMap.piMap fun i ↦ relativeDegreeCrossMap R (X i) Y (A i) k
  have hF : Function.Bijective F := degreeTensorFamilyMap_bijective R
    (fun n ↦ relativeCohomology R Z B n) (fun n ↦ cohomology R Y n)
    (fun i n ↦ relativeCohomology R (X i) (A i) n)
    (fun n i ↦ (relativeCohomologyPullback R (f i) (hf i) n).hom) hc k
  have hH : Function.Bijective H := Function.Bijective.piMap (fun i ↦ hX i k)
  have hs : G.comp (relativeDegreeCrossMap R Z Y B k) = H.comp F := by
    apply LinearMap.ext
    intro x
    funext i
    exact LinearMap.congr_fun (relativeDegreeCrossMap_natural R Y (f i) (hf i) k) x
  have hcomp : Function.Bijective (G.comp (relativeDegreeCrossMap R Z Y B k)) := by
    rw [hs]
    exact hH.comp hF
  exact Function.Bijective.of_comp_left (f := G)
    (g := relativeDegreeCrossMap R Z Y B k) hcomp (hp k).injective

set_option backward.isDefEq.respectTransparency false in
/-- The relative cross product for one adjacent-skeleton pair is an isomorphism
once it is an isomorphism for the characteristic disk-boundary pair.
Source: Hatcher Proposition 3.17, p.217. Characteristic-cell excision identifies
the skeletal pair with the finite family of standard cell pairs, compatibly
with product by Y, and the finite-family assembly lemma applies. -/
private theorem relativeDegreeCrossMap_skeleton_bijective
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [_root_.Topology.CWComplex (Set.univ : Set X)]
    [_root_.Topology.RelCWComplex.Finite (Set.univ : Set X)]
    [_root_.Topology.CWComplex (Set.univ : Set Y)]
    [_root_.Topology.RelCWComplex.Finite (Set.univ : Set Y)]
    (m : ℕ)
    (hD : ∀ n, Function.Bijective (relativeDegreeCrossMap R
      (TopCat.of (HolomorphicAnosov.CharacteristicCellComparison.CellDisk.{u} m)) Y
      (HolomorphicAnosov.CharacteristicCellComparison.cellBoundary m) n)) (k : ℕ) :
    Function.Bijective (relativeDegreeCrossMap R
      (TopCat.of (HolomorphicAnosov.CharacteristicCellComparison.Skeleton X m)) Y
      (HolomorphicAnosov.CharacteristicCellComparison.lowerSkeleton X m) k) := by
  classical
  let : Finite (_root_.Topology.RelCWComplex.cell (Set.univ : Set X) m) :=
    _root_.Topology.RelCWComplex.FiniteType.finite_cell m
  let := Fintype.ofFinite (_root_.Topology.RelCWComplex.cell (Set.univ : Set X) m)
  exact relativeDegreeCrossMap_bijective_of_family R
    (fun _ : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) m ↦
      TopCat.of (HolomorphicAnosov.CharacteristicCellComparison.CellDisk.{u} m))
    (fun _ ↦ HolomorphicAnosov.CharacteristicCellComparison.cellBoundary m)
    (TopCat.of (HolomorphicAnosov.CharacteristicCellComparison.Skeleton X m)) Y
    (HolomorphicAnosov.CharacteristicCellComparison.lowerSkeleton X m)
    (fun i ↦ TopCat.ofHom (HolomorphicAnosov.CharacteristicCellComparison.characteristicCell X m i))
    (HolomorphicAnosov.CharacteristicCellComparison.characteristicCell_mapsTo X m)
    (fun n ↦ (HolomorphicAnosov.CharacteristicCellComparison.finite_cw_characteristic_cell_cohomology_comparison X R Y m n).1)
    (fun n ↦ (HolomorphicAnosov.CharacteristicCellComparison.finite_cw_characteristic_cell_cohomology_comparison X R Y m n).2)
    (fun _ ↦ hD) k

private theorem degreeTensorMap_bijective (A B D : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (f : ∀ n, A n →ₗ[R] B n) (hf : ∀ n, Function.Bijective (f n)) (k : ℕ) :
    Function.Bijective (degreeTensorMap R A B D f k) := by
  let E := DirectSum.congrLinearEquiv (fun i : degreePairs k ↦
    (LinearEquiv.ofBijective (f i.val.1) (hf i.val.1)).rTensor (D i.val.2))
  exact E.bijective

set_option backward.isDefEq.respectTransparency false in
private theorem absoluteCrossHomogeneous_natural {X Z : TopCat.{u}} (Y : TopCat.{u})
    (f : X ⟶ Z) (p q : ℕ) (a : cohomology R Z p) (b : cohomology R Y q) :
    cohomologyPullback R (crossProductMap f Y) (p + q)
      (absoluteCrossHomogeneous R Z Y p q a b) =
    absoluteCrossHomogeneous R X Y p q (cohomologyPullback R f p a) b := by
  have h := MixedCup.descended_cup_naturality R (crossProductMap f Y) ∅ ∅
    (Set.mapsTo_empty _ _) false false p q
    (cohomologyPullback R (crossProductFst Z Y) p a)
    (cohomologyPullback R (crossProductSnd Z Y) q b)
  change cohomologyPullback R _ (p + q) _ =
    MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false p q
      (cohomologyPullback R _ p (cohomologyPullback R (crossProductFst Z Y) p a))
      (cohomologyPullback R _ q (cohomologyPullback R (crossProductSnd Z Y) q b)) at h
  have ha := actualPullback_comp_apply R (crossProductMap f Y) (crossProductFst Z Y) p a
  have hb := actualPullback_comp_apply R (crossProductFst X Y) f p a
  apply h.trans
  exact congrArg₂ (fun aa bb ↦ MixedCup.descended_cup R (crossProductSpace X Y)
    ∅ false false p q aa bb) (ha.trans hb.symm)
    (actualPullback_comp_apply R (crossProductMap f Y) (crossProductSnd Z Y) q b)

set_option backward.isDefEq.respectTransparency false in
private theorem degreeCrossMap_natural {X Z : TopCat.{u}} (Y : TopCat.{u})
    (f : X ⟶ Z) (k : ℕ) :
    (cohomologyPullback R (crossProductMap f Y) k).hom.comp (degreeCrossMap R Z Y k) =
    (degreeCrossMap R X Y k).comp
      (degreeTensorMap R (fun n ↦ cohomology R Z n) (fun n ↦ cohomology R X n)
        (fun n ↦ cohomology R Y n) (fun n ↦ (cohomologyPullback R f n).hom) k) :=
  degreeTensorLift_natural R
    (fun n ↦ cohomology R Z n) (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n)
    (fun n ↦ cohomology R (crossProductSpace Z Y) n)
    (fun n ↦ cohomology R (crossProductSpace X Y) n)
    (absoluteCrossHomogeneous R Z Y) (absoluteCrossHomogeneous R X Y)
    (fun n ↦ (cohomologyPullback R f n).hom)
    (fun n ↦ (cohomologyPullback R (crossProductMap f Y) n).hom)
    (absoluteCrossHomogeneous_natural R Y f) k

set_option backward.isDefEq.respectTransparency false in
/-- Cross-product bijectivity is invariant under a homeomorphism of the first
factor. Source: Hatcher p.216, naturality. Pullbacks along the homeomorphism
and its product are isomorphisms, so the commuting cross-product square
transfers bijectivity. -/
private theorem degreeCrossMap_homeomorph_bijective {X Z : TopCat.{u}} (Y : TopCat.{u})
    (e : X ≃ₜ Z) (k : ℕ) (h : Function.Bijective (degreeCrossMap R Z Y k)) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  let f := (TopCat.isoOfHomeo e).hom
  let E (n : ℕ) := ((actualCohomologyFunctor R n).mapIso (TopCat.isoOfHomeo e).op).toLinearEquiv
  let ep : crossProductSpace X Y ≃ₜ crossProductSpace Z Y := e.prodCongr (Homeomorph.refl Y)
  let P := ((actualCohomologyFunctor R k).mapIso (TopCat.isoOfHomeo ep).op).toLinearEquiv
  have hF := degreeTensorMap_bijective R (fun n ↦ cohomology R Z n)
    (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n)
    (fun n ↦ (cohomologyPullback R f n).hom) (fun n ↦ (E n).bijective) k
  have hs := degreeCrossMap_natural R Y f k
  have hp : Function.Bijective
      ((cohomologyPullback R (crossProductMap f Y) k).hom.comp (degreeCrossMap R Z Y k)) :=
    P.bijective.comp h
  rw [hs] at hp
  exact (Function.Bijective.of_comp_iff (degreeCrossMap R X Y k) hF).mp hp

set_option backward.isDefEq.respectTransparency false in
/-- Empty spaces have zero actual singular cohomology in every degree.
Source: Hatcher p.198. There is no singular simplex, so every cochain is zero,
and the cocycle submodule and its quotient are both zero. -/
private theorem empty_cohomology (X : TopCat.{u}) [IsEmpty X] (n : ℕ) :
    Subsingleton (cohomology R X n) := by
  let S := TopCat.toSSet.obj X
  have hc : Subsingleton (cochains R X n) := by
    constructor
    intro a b
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim ((TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) (Convexity.StdSimplex.single (0 : Fin (n + 1))))
  let : Subsingleton (cycles R (complex R X) n) :=
    ⟨fun a b ↦ Subtype.ext (hc.elim a.val b.val)⟩
  change Subsingleton (cycles R (complex R X) n ⧸ boundaries R (complex R X) n)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem degreeCrossMap_empty_bijective (X Y : TopCat.{u}) [IsEmpty X] (k : ℕ) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  let (n : ℕ) := empty_cohomology R X n
  let := empty_cohomology R (crossProductSpace X Y) k
  have hdom : Subsingleton (crossProductDegreeDomain R X Y k) := inferInstance
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

open _root_.Topology in
private theorem skeletonLT_carrier_bounded (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] [RelCWComplex.Finite (Set.univ : Set X)]
    (m : ℕ) (x0 : (CWComplex.skeletonLT (Set.univ : Set X) m : Set X)) :
    ∃ cw : CWComplex (Set.univ : Set (CWComplex.skeletonLT (Set.univ : Set X) m : Set X)),
      letI := cw
      RelCWComplex.Finite (Set.univ : Set (CWComplex.skeletonLT (Set.univ : Set X) m : Set X)) ∧
      ∀ n, m ≤ n → IsEmpty (RelCWComplex.cell
        (Set.univ : Set (CWComplex.skeletonLT (Set.univ : Set X) m : Set X)) n) := by
  let C : Set X := CWComplex.skeletonLT (Set.univ : Set X) m
  let : CWComplex C := CWComplex.Subcomplex.instCWComplex (CWComplex.skeletonLT _ m)
  let : RelCWComplex.Finite C := RelCWComplex.Subcomplex.finite_subcomplex_of_finite _
  let := cwCarrierStructureG6 C x0
  refine ⟨inferInstance, HolomorphicAnosov.Cubical.cwCarrier_finite C x0, ?_⟩
  intro n hn
  refine ⟨fun i ↦ ?_⟩
  have hi := i.property
  change i.val ∈ (CWComplex.skeletonLT (Set.univ : Set X) m).I n at hi
  have hlt : (n : ℕ∞) < m := by
    simpa only [RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hi
  exact (not_lt_of_ge (show (m : ℕ∞) ≤ n by exact_mod_cast hn)) hlt

open _root_.Topology in
private def lowerSkeletonHomeo (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (m : ℕ) :
    TopCat.of (CharacteristicCellComparison.lowerSkeleton X m) ≃ₜ
      TopCat.of (CWComplex.skeletonLT (Set.univ : Set X) m : Set X) where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, RelCWComplex.skeletonLT_mono (by exact_mod_cast Nat.le_succ m) z.property⟩,
    z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def cellBoundarySphereHomeo (m : ℕ) :
    TopCat.of (CharacteristicCellComparison.cellBoundary m) ≃ₜ
      TopCat.of (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1)) where
  toFun z := ULift.up ⟨z.val.down.val, z.property⟩
  invFun z := ⟨ULift.up ⟨z.down.val, Metric.sphere_subset_closedBall z.down.property⟩,
    z.down.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_uliftUp.comp
    ((continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    (continuous_uliftUp.comp ((continuous_subtype_val.comp continuous_uliftDown).subtype_mk _)).subtype_mk _

open _root_.Topology in
private theorem full_skeleton (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] (m : ℕ)
    (hbound : ∀ n, m + 1 ≤ n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n)) :
    (CWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ n, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
      RelCWComplex.openCell n i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    trivial
  obtain ⟨n, i, hi⟩ := Set.mem_iUnion₂.mp hx
  have hn : n < m + 1 := by
    by_contra h
    exact (hbound n (by omega)).false i
  exact CWComplex.mem_skeletonLT_iff.mpr ⟨n, by exact_mod_cast hn, i, hi⟩

open _root_.Topology in
private theorem empty_of_cell_bound_zero (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (hbound : ∀ n, IsEmpty (RelCWComplex.cell (Set.univ : Set X) n)) : IsEmpty X := by
  constructor
  intro x
  have hx : x ∈ ⋃ n, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
      RelCWComplex.openCell n i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    trivial
  obtain ⟨n, i, _⟩ := Set.mem_iUnion₂.mp hx
  exact (hbound n).false i

set_option maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false in
open _root_.Topology in
private theorem degreeCrossMap_bounded_bijective (Y : TopCat.{u}) [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] [RelCWComplex.Finite (Set.univ : Set Y)]
    [∀ n, Module.Free R (cohomology R Y n)]
    (hsphere : ∀ m, 0 < m →
      ∃ cw : CWComplex (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))),
        letI := cw
        RelCWComplex.Finite (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))) ∧
        ∀ n, m ≤ n → IsEmpty (RelCWComplex.cell
          (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))) n)) :
    ∀ N (X : TopCat.{u}) [T2Space X]
      [Topology.CWComplex (Set.univ : Set X)]
      [RelCWComplex.Finite (Set.univ : Set X)],
      (∀ n, N ≤ n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n)) →
      ∀ k, Function.Bijective (degreeCrossMap R X Y k) := by
  intro N
  induction N with
  | zero =>
      intro X _ _ _ hbound k
      let (n : ℕ) : IsEmpty (RelCWComplex.cell (Set.univ : Set X) n) := hbound n (Nat.zero_le n)
      let : IsEmpty X := empty_of_cell_bound_zero X (fun n ↦ inferInstance)
      exact degreeCrossMap_empty_bijective R X Y k
  | succ m ih =>
      intro X _ _ _ hbound k
      classical
      have hA : ∀ n, Function.Bijective (degreeCrossMap R
          (TopCat.of (CharacteristicCellComparison.lowerSkeleton X m)) Y n) := by
        let L := (CWComplex.skeletonLT (Set.univ : Set X) m : Set X)
        cases isEmpty_or_nonempty L with
        | inl he =>
            let : IsEmpty L := he
            intro n
            exact degreeCrossMap_homeomorph_bijective R Y
              (lowerSkeletonHomeo X m) n
              (degreeCrossMap_empty_bijective R (TopCat.of L) Y n)
        | inr he =>
            obtain ⟨cw, hfin, hcells⟩ := skeletonLT_carrier_bounded X m (Classical.choice he)
            let := cw
            let := hfin
            have hi : ∀ n, m ≤ n → IsEmpty (RelCWComplex.cell (Set.univ : Set L) n) := hcells
            intro n
            exact degreeCrossMap_homeomorph_bijective R Y
              (lowerSkeletonHomeo X m) n
              (ih (TopCat.of L) hi n)
      have hB : ∀ n, Function.Bijective (degreeCrossMap R
          (TopCat.of (CharacteristicCellComparison.cellBoundary m)) Y n) := by
        cases m with
        | zero =>
            intro n
            let : IsEmpty (CharacteristicCellComparison.cellBoundary 0) := by
              refine ⟨fun z ↦ ?_⟩
              have hz := z.property
              change dist z.val.down.val (0 : Fin 0 → ℝ) = 1 at hz
              have hz0 : z.val.down.val = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
              rw [hz0, dist_self] at hz
              exact zero_ne_one hz
            exact degreeCrossMap_empty_bijective R _ Y n
        | succ m =>
            obtain ⟨cw, hfin, hcells⟩ := hsphere (m + 1) (Nat.succ_pos m)
            let := cw
            let := hfin
            intro n
            exact degreeCrossMap_homeomorph_bijective R Y
              (cellBoundarySphereHomeo (m + 1)) n
              (ih (TopCat.of (ULift.{u} (Metric.sphere (0 : Fin (m + 1) → ℝ) 1))) hcells n)
      have hD : ∀ n, Function.Bijective (relativeDegreeCrossMap R
          (TopCat.of (CharacteristicCellComparison.CellDisk.{u} m)) Y
          (CharacteristicCellComparison.cellBoundary m) n) :=
        relativeDegreeCrossMap_bijective_of_absolute R _ Y _
          (fun n ↦ degreeCrossMap_cellDisk_bijective R m Y n) hB
      have hrel : ∀ n, Function.Bijective (relativeDegreeCrossMap R
          (TopCat.of (CharacteristicCellComparison.Skeleton X m)) Y
          (CharacteristicCellComparison.lowerSkeleton X m) n) := by
        intro n
        exact relativeDegreeCrossMap_skeleton_bijective R X Y m hD n
      have hs : ∀ n, Function.Bijective (degreeCrossMap R
          (TopCat.of (CharacteristicCellComparison.Skeleton X m)) Y n) :=
        degreeCrossMap_bijective_of_relative R _ Y
          (CharacteristicCellComparison.lowerSkeleton X m) hrel hA
      have hskel : (CWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = Set.univ :=
        full_skeleton X m hbound
      let e : X ≃ₜ TopCat.of (CharacteristicCellComparison.Skeleton X m) := {
        toFun x := ⟨x, by rw [hskel]; trivial⟩
        invFun z := z.val
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := continuous_id.subtype_mk (fun x ↦ by rw [hskel]; trivial)
        continuous_invFun := continuous_subtype_val }
      exact degreeCrossMap_homeomorph_bijective R Y e k (hs k)



/-- Hatcher, Algebraic Topology, Theorem 3.15 pp.216–218 and the finite-dimensional
part of Proposition 3.17 p.217, applied to the explicitly defined cross map.

Fix Y. For each pair (U,A), form h^n(U,A) as the sum over p+q=n of
H^p(U,A;R) tensor H^q(Y;R), and t^n(U,A)=H^n(U×Y,A×Y;R). Choose finite free
bases in H^q(Y;R); tensoring each long exact row is then a finite sum of the
ordinary row, hence exact. Summing the shifted rows is exact because each
input has finite support, so finitely many component preimages suffice.
Restriction gives finite-disjoint-union splitting on both sides, by commuting
the two finite indices. Homotopy invariance follows from the ordinary singular
pair theorem. The characteristic-cell comparison supplies the excision step
for skeleton pairs with the ordinary product topology.

Define the relative cross maps using the mixed cup product. Pullback naturality
makes their squares for maps of pairs commute. For the connecting square, lift
an A-cocycle α to an ambient cochain αbar. If b is a Y-cocycle, the product
p_U^*αbar cup p_Y^*b extends the subspace cross cocycle. Its coboundary is
p_U^*dαbar cup p_Y^*b, since db=0, by the cup Leibniz identity. This is exactly
the cross image of the connecting class, with no additional sign. Linearity
extends the equality from generators to the entire degree sum.

At a point the singular chain complex has one generator in every degree,
with boundary alternating between zero and identity. Thus ordinary H^0 is R
and higher cohomology vanishes; the cross map is R tensor H^n(Y) → H^n(Y),
r tensor b ↦ r b, with inverse b ↦ 1 tensor b. Homotopy invariance gives the
disk case. Finite disjoint-union splitting gives the zero-skeleton case.

Induct on the maximum cell dimension. The boundary of an m-disk is a finite
CW complex of dimension m−1, and its cross map is bijective by induction.
The five lemma in the disk-pair long exact rows therefore proves bijectivity
for (D^m,∂D^m) in every degree. Finite sums give the disjoint union of disk
pairs. The characteristic-cell comparison and naturality transport this to
the skeleton pair (X^m,X^(m−1)). Finally use the five-term exact window
h^(n−1)(X^(m−1)) → h^n(X^m,X^(m−1)) → h^n(X^m) → h^n(X^(m−1)) →
h^(n+1)(X^m,X^(m−1)), with the corresponding t row. Four outer maps are
bijective, so the middle one is bijective. For n=0 the negative-degree terms
are zero and the same argument applies. Finite CW dimension ends the induction.
All maps are the original relative cross maps; at A empty their formula is
`degreeCrossMap`, so the result concerns this fixed map, not an arbitrary
isomorphism. Empty cell sets, empty spaces and the zero ring give zero modules
and require no nontriviality or connectedness assumption. -/


private theorem degreeCrossMap_bijective (R : Type u) [CommRing R]
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set Y)]
    [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (hfree : ∀ q : ℕ,
      Module.Free R (cohomology R Y q) ∧ Module.Finite R (cohomology R Y q)) (k : ℕ) :
    Function.Bijective (degreeCrossMap R X Y k) := by
  let (q : ℕ) : Module.Free R (cohomology R Y q) := (hfree q).1
  have hSphere : ∀ m, 0 < m →
      ∃ cw : _root_.Topology.CWComplex (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))),
        letI := cw
        _root_.Topology.RelCWComplex.Finite (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))) ∧
        ∀ n, m ≤ n → IsEmpty (_root_.Topology.RelCWComplex.cell
          (Set.univ : Set (ULift.{u} (Metric.sphere (0 : Fin m → ℝ) 1))) n) := by
    intro m hm
    obtain ⟨cw, hfin, hbound⟩ :=
      StandardDiskBoundaryCW.sphere_finite_cw_bounded m hm
    let : _root_.Topology.CWComplex (Set.univ : Set (Metric.sphere (0 : Fin m → ℝ) 1)) := cw
    let : _root_.Topology.RelCWComplex.Finite (Set.univ : Set (Metric.sphere (0 : Fin m → ℝ) 1)) := hfin
    obtain ⟨cwU, hfinU, ⟨liftIndex, hmap⟩⟩ :=
      finite_cw_ulift_characteristic_maps
        (Metric.sphere (0 : Fin m → ℝ) 1)
    let := cwU
    refine ⟨cwU, hfinU, ?_⟩
    intro n hn
    exact ⟨fun i ↦ (hbound n hn).false ((liftIndex n).symm i).down⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (_root_.Topology.RelCWComplex.FiniteDimensional.eventually_isEmpty_cell
      (C := (Set.univ : Set X)) (D := (∅ : Set X)))
  exact degreeCrossMap_bounded_bijective R Y hSphere N X hN k

/-- The degreewise Künneth cross-product equivalences for finite CW spaces.

Source: Hatcher, *Algebraic Topology*, Theorem 3.15 and Proposition 3.17,
pp. 214--218.  The proof is the finite skeleton induction: the disk and
zero-skeleton cases are compared through the relative singular long exact
sequence, finite free bases identify tensor rows with finite direct sums, and
the characteristic-cell comparison transports the pair isomorphism to each
finite skeleton. The preceding bijectivity theorem records that induction.
Here `LinearEquiv.ofBijective` packages the concrete degree cross map, and
uniqueness on cocycle representatives identifies its product with the chosen
graded multiplication. No Künneth isomorphism is added as a hypothesis to
the public target.

The product's graded ring must satisfy its actual cocycle representative equations.
Otherwise, for X = Y = S¹ over ℚ, replace the torus ring by the square-zero extension
of ℚ by its positive-degree graded vector space. This is a graded ring on the same
cohomology modules, but every degree-(1,1) cross product vanishes. The proposed
degree-two equivalence would then be the zero map ℚ → ℚ. The `hP` hypothesis
excludes this counterexample and is supplied by `cohomology_graded_ring_data`.
-/
private theorem degreewise_cross_product_kunneth
    (R : Type u) [CommRing R] (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set Y)]
    [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (hfree : ∀ q : ℕ,
      Module.Free R (cohomology R Y q) ∧ Module.Finite R (cohomology R Y q))
    [_GX : DirectSum.GRing (fun n ↦ cohomology R X n)]
    [_GY : DirectSum.GRing (fun n ↦ cohomology R Y n)]
    [GP : DirectSum.GRing (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    (hP : IsCochainGradedRing R (crossProductSpace X Y)) :
    ∀ k : ℕ,
      ∃ μ : crossProductDegreeDomain R X Y k ≃ₗ[R]
          cohomology R (crossProductSpace X Y) k,
        ∀ (i : {i : ℕ × ℕ // i.1 + i.2 = k})
          (a : cohomology R X i.val.1) (b : cohomology R Y i.val.2),
          μ (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) =
            cast (congrArg
              (fun n ↦ (cohomology R (crossProductSpace X Y) n : Type u)) i.property)
              (GradedMonoid.GMul.mul
                (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
                ((cohomologyPullback R (crossProductFst X Y) i.val.1).hom a)
                ((cohomologyPullback R (crossProductSnd X Y) i.val.2).hom b)) := by
  intro k
  refine ⟨LinearEquiv.ofBijective (degreeCrossMap R X Y k)
    (degreeCrossMap_bijective R X Y hfree k), ?_⟩
  intro i a b
  change degreeCrossMap R X Y k (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) = _
  rw [degreeCrossMap_pure]
  have heq := cochain_graded_mul_eq R (crossProductSpace X Y) hP
    (MixedCup.descended_cup R (crossProductSpace X Y) ∅ false false) (by
      intro p q a b
      refine ⟨MixedCup.tagged_cup_linear R (crossProductSpace X Y) ∅ false false p q a b,
        ?_, MixedCup.descended_cup_representatives R _ ∅ false false p q a b⟩
      exact MixedCup.tagged_cochain_cup_inclusion R _ ∅ false false p q a.val b.val)
    i.val.1 i.val.2
    ((cohomologyPullback R (crossProductFst X Y) i.val.1).hom a)
    ((cohomologyPullback R (crossProductSnd X Y) i.val.2).hom b)
  exact congrArg (cast (congrArg
    (fun n ↦ (cohomology R (crossProductSpace X Y) n : Type u)) i.property)) heq.symm

/-- Multiplicativity, the unit identity, and the transported tensor ring
structure for the total cross-product map.

Source: Hatcher, *Algebraic Topology*, pp. 216--218.  On homogeneous pure
tensors this is the cup-product associativity/naturality calculation; moving
the middle factors gives the Koszul sign.  Bilinearity extends the identity to
finite-support sums, the degree-zero constant cocycle gives the tensor unit,
and `koszul_tensor_ring` supplies the displayed transported ring.  The source
calculation is isolated here so the degreewise finite-CW induction above is
not hidden inside the final interface theorem.
-/
private theorem total_cross_product_ring_data
    (R : Type u) [CommRing R] (X Y : TopCat.{u})
    [DirectSum.GRing (fun n ↦ cohomology R X n)]
    [DirectSum.GRing (fun n ↦ cohomology R Y n)]
    [DirectSum.GRing (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R X n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R Y n)]
    [DirectSum.GAlgebra R (fun n ↦ cohomology R (crossProductSpace X Y) n)]
    (hX : IsCochainGradedRing R X) (hY : IsCochainGradedRing R Y)
    (hP : IsCochainGradedRing R (crossProductSpace X Y))
    (μ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃ₗ[R]
      gradedCohomology R (crossProductSpace X Y))
    (hpure : ∀ (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q),
      μ ((DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a) ⊗ₜ[R]
          (DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)) =
        DirectSum.lof R ℕ (fun n ↦ cohomology R (crossProductSpace X Y) n) (p + q)
          (GradedMonoid.GMul.mul
            (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
            ((cohomologyPullback R (crossProductFst X Y) p).hom a)
            ((cohomologyPullback R (crossProductSnd X Y) q).hom b))) :
    (∀ u v, μ (TensorProduct.gradedMul R
        (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) = μ u * μ v) ∧
      μ ((1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y)) = 1 ∧
      ∃ rt : Ring (gradedCohomology R X ⊗[R] gradedCohomology R Y),
        (∀ u v, rt.add u v = u + v) ∧ rt.zero = 0 ∧ (∀ u, rt.neg u = -u) ∧
        (∀ u v, rt.mul u v = TensorProduct.gradedMul R
          (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) ∧
        rt.one = (1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y) ∧
        (letI := rt
         letI : Mul (gradedCohomology R X ⊗[R] gradedCohomology R Y) := rt.toMul
         ∃ Φ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃+*
             gradedCohomology R (crossProductSpace X Y),
           ∀ u, Φ u = μ u) := by
  obtain ⟨hmul, hone⟩ := total_cross_product_mul_unit R X Y hX hY hP μ hpure
  obtain ⟨rt, hadd, hzero, hneg, hmulrt, honert⟩ :=
    koszul_tensor_ring_data R (fun n ↦ cohomology R X n)
      (fun n ↦ cohomology R Y n)
  have hΦ := total_cross_product_ring_equiv R X Y μ hmul hone rt hmulrt honert
  exact ⟨hmul, hone, ⟨rt, hadd, hzero, hneg, hmulrt, honert, hΦ⟩⟩

/-- **Finite-CW cohomological Künneth theorem with the original cup cross product.**
Source: Hatcher, Algebraic Topology, Theorem 3.15 and its proof, pp.214–218,
including the finite-dimensional induction in Proposition 3.17, p.217.
DAG node: `topo.finite_cw_cohomology_cross_product_kunneth_g3`.

The canonical graded-ring data are constructed in the CONCLUSION and pinned to
actual cocycle representatives through `cupCochain`; they are not hypotheses.
The scalar structures, degreewise equivalences and total ring equivalence are
also conclusions. The total tensor multiplication is exactly Mathlib's Koszul
`TensorProduct.gradedMul`, including the sign (-1)^(|b||c|).
No field, PID, connectivity, nonempty-space or nonzero-ring assumption is made.
Finite CW structures are on the full Hausdorff spaces, as in Hatcher
(Appendix Proposition A.3). Mathlib's weak CW class does not include T2, so
T2Space is explicit here. Their product uses its ordinary product topology. The hypothesis on Y is precisely finitely generated and free
in every nonnegative degree, expressed by Module.Finite and Module.Free.

Complete natural-language proof relative to the current direct prerequisites:

1. For homogeneous a∈H^p(X;R), b∈H^q(Y;R), define a×b=p_X*a∪p_Y*b. Cup bilinearity and the
tensor lift give μ on each degree sum, and tensor/direct-sum distribution gives the graded map.
For homogeneous c,d, graded commutativity moves p_Y*b past p_X*c with exactly (−1)^(|b||c|);
naturality and associativity then give μ((a⊗b)(c⊗d))=μ(a⊗b)μ(c⊗d). The degree0 units pull back
to the product unit. This works over every commutative ring; no inference that odd squares
vanish from twice a square being zero is used.

2. Fix Y. For any pair (U,A) define h^n(U,A)=⊕_(p+q=n,p,q≥0) H^p(U,A;R)⊗_R H^q(Y;R),
t^n(U,A)=H^n(U×Y,A×Y;R), and negative degrees zero. The relative singular pair theorem gives
long exact sequences, homotopy invariance, excision and finite disjoint-union splitting for t,
since an ordinary product preserves continuous pair maps/homotopies and open-cover excision
domains. For h choose a finite basis of each free H^q(Y;R). Tensoring with it identifies each
degree with finitely many copies of the original module via m⊗Σ_jr_j e_j↦(r_jm)_j, inverse
(m_j)↦Σ_jm_j⊗e_j. Exactness remains componentwise, and summing the q-shifted sequences remains
exact because every element has finite support and component preimages retain finite support.
The connecting map on the q summand is ∂⊗id with no extra sign. For a finite union, the
component cohomology product and finite tensor-copy description commute by interchanging finite
indices. These are proved properties of the actual singular functors; they are not added
assumptions on X,Y.

3. The mixed relative/absolute cup product defines μ:h^n(U,A)→t^n(U,A). It is natural for
continuous maps of pairs by cup pullback naturality. For the connecting square take an A-cocycle
α of degree p and a Y-cocycle b of degree q. Extend α by zero on singular p-simplices of U whose
image is not contained in A, giving ᾱ on U. This is a degreewise extension, not a cochain map.
On U×Y use η=p_U♯ᾱ∪p_Y♯b, a permissible extension of the corresponding cocycle on A×Y. It need
not be the zero extension on product simplices: a product simplex not wholly in A×Y can have its
front U-face inside A. The connecting map permits any extension. The cochain Leibniz equation
gives δη=p_U♯(δᾱ)∪p_Y♯b+(−1)^p p_U♯ᾱ∪p_Y♯(δb)=p_U♯(δᾱ)∪p_Y♯b. This is a relative cocycle, and
exactly represents μ((∂[α])⊗[b]). Thus the full LES diagram commutes with the actual ∂
convention; linearity extends the equality from pure tensors to all sums.

4. At a point, each singular chain degree has the one constant simplex as basis, and the
boundary is multiplication by Σ_(i=0)^n(−1)^i for n>0: zero in odd chain degrees and identity in
positive even degrees. Its dual cochain complex gives H^0(point;R)=R and all positive cohomology
zero. The cross product map reduces to R⊗_R H^n(Y;R)→H^n(Y;R), r⊗b↦rb, inverse b↦1⊗b; the
balancing relation proves both inverse identities. Homotopy invariance extends this case to a
disk. A finite 0-skeleton is a finite disjoint union of points, so the previous finite-union
property gives its μ isomorphism. The empty skeleton has zero cohomology and causes no
exception.

5. Prove simultaneously for all degrees that μ is an isomorphism for every finite CW complex of
dimension≤m. The 0-dimensional case was just established. For m≥1, the boundary ∂D^m has a
finite CW structure of dimension m−1 (for m=1 it is two points), so its maps are isomorphisms by
the induction hypothesis. For a disk, contractibility gives the absolute point case. In the
commuting long exact sequences of the disk pair, the five-term window
h^(n−1)(D^m)→h^(n−1)(∂D^m)→h^n(D^m,∂D^m)→h^n(D^m)→h^n(∂D^m), and the corresponding t row, has
four outer isomorphisms. The module five lemma proves the middle relative μ is an isomorphism in
every degree; for n=0 the negative-degree groups are zero and the same window applies. Finite
disjoint unions then give the result for the disjoint union of all m-cell disk pairs.

6. For a finite CW m-skeleton, use the actual characteristic-cell pullback Φ and Φ×id_Y. The
named comparison theorem identifies t*(X^m,X^(m−1)) with the finite product of disk-product
relative groups and ordinary relative H*(X^m,X^(m−1)) with the disk-pair product. Tensoring this
finite-product comparison with each finite free H^q(Y;R) and summing degree shifts identifies h
with the disk-pair h groups. The cross-product square commutes by the already proved pullback
naturality, so the disk-pair μ isomorphism implies the skeleton-pair μ isomorphism. The
comparison theorem uses open cell collars and ordinary product excision and does not substitute
a product CW topology or presume characteristic maps injective on their attaching boundaries.

7. Now compare the skeleton-pair long exact rows in the window
h^n(X^m,X^(m−1))→h^n(X^m)→h^n(X^(m−1))→h^(n+1)(X^m,X^(m−1))→h^(n+1)(X^m). To put the unknown
absolute term in the middle of a five-term window, instead use
h^(n−1)(X^(m−1))→h^n(X^m,X^(m−1))→h^n(X^m)→h^n(X^(m−1))→h^(n+1)(X^m,X^(m−1)). The four outer
vertical maps are isomorphisms by the pair result and the induction hypothesis. The module five
lemma therefore gives μ for X^m in every degree. A finite CW complex has a largest cell
dimension, so finitely many steps reach X; no infinite-CW telescope, inverse limit, or eventual-
degree stabilization is needed.

8. The preceding isomorphisms are the original cup cross-product maps in every degree. Their
direct sum is consequently an R-linear graded isomorphism, with inverse the degreewise inverse
applied to the finite support of an element. The first step proves it preserves multiplication
and unit, so it is the asserted graded ring isomorphism with the displayed Koszul sign. If R is
the zero ring, all modules are zero and the same proof applies. Empty X or Y gives zero
modules/rings on both sides; disconnected finite complexes are handled by finite-union
splitting. No field, PID, orientability, connectedness, reduced cohomology or cross-product-
isomorphism hypothesis has been introduced.

The first step also constructs the graded ring on each original H*(Z;R), with
its homogeneous product given by the actual representative cup formula and
its unit the class of the actual constant-one zero-cochain. The usual quotient
descent is supplied by the existing cup-product source theorem. Its R-bilinearity
gives GAlgebra for X, Y and their ordinary product. On the tensor of the direct
sums, Koszul gradedMul is associative, distributes over the original tensor
addition and has the tensor of the two units as unit; its existing Mathlib
identities supply the stated compatible Ring structure. The degreewise and
total maps agree on each pure homogeneous tensor by the definition of cross
product. Their linear equivalence and multiplication/unit identities give the
final RingEquiv, with exactly that underlying cross-product function.
-/
theorem finite_cw_cohomology_cross_product_kunneth
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set Y)]
    [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (hfree : ∀ q : ℕ,
      Module.Free R (cohomology R Y q) ∧ Module.Finite R (cohomology R Y q)) :
    ∃ G : ∀ Z : TopCat.{u}, DirectSum.GRing (fun n ↦ cohomology R Z n),
      (∀ Z : TopCat.{u},
        letI := G Z
        (∀ (p q : ℕ) (a : cycles R (complex R Z) p)
          (b : cycles R (complex R Z) q),
          ∃ hc : cupCochain R Z a.val b.val ∈ cycles R (complex R Z) (p + q),
            GradedMonoid.GMul.mul (A := fun n : ℕ ↦ cohomology R Z n)
              (cocycleClass R (complex R Z) p a) (cocycleClass R (complex R Z) q b) =
              cocycleClass R (complex R Z) (p + q) ⟨cupCochain R Z a.val b.val, hc⟩) ∧
        (∃ hu : oneCochain R Z ∈ cycles R (complex R Z) 0,
          GradedMonoid.GOne.one (A := fun n : ℕ ↦ cohomology R Z n) =
            cocycleClass R (complex R Z) 0 ⟨oneCochain R Z, hu⟩)) ∧
      (letI := G X
       letI := G Y
       letI := G (crossProductSpace X Y)
       ∃ (AX : DirectSum.GAlgebra R (fun n ↦ cohomology R X n))
         (AY : DirectSum.GAlgebra R (fun n ↦ cohomology R Y n))
         (AP : DirectSum.GAlgebra R (fun n ↦ cohomology R (crossProductSpace X Y) n)),
         letI := AX
         letI := AY
         letI := AP
         (∀ k : ℕ,
           ∃ μ : crossProductDegreeDomain R X Y k ≃ₗ[R]
               cohomology R (crossProductSpace X Y) k,
             ∀ (i : {i : ℕ × ℕ // i.1 + i.2 = k})
               (a : cohomology R X i.val.1) (b : cohomology R Y i.val.2),
               μ (DirectSum.lof R _ _ i (a ⊗ₜ[R] b)) =
                 cast (congrArg
                   (fun n ↦ (cohomology R (crossProductSpace X Y) n : Type u)) i.property)
                   (GradedMonoid.GMul.mul
                     (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
                     ((cohomologyPullback R (crossProductFst X Y) i.val.1).hom a)
                     ((cohomologyPullback R (crossProductSnd X Y) i.val.2).hom b))) ∧
         (∃ μ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃ₗ[R]
               gradedCohomology R (crossProductSpace X Y),
           (∀ (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q),
             μ ((DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a) ⊗ₜ[R]
                 (DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)) =
               DirectSum.lof R ℕ (fun n ↦ cohomology R (crossProductSpace X Y) n) (p + q)
                 (GradedMonoid.GMul.mul
                   (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
                   ((cohomologyPullback R (crossProductFst X Y) p).hom a)
                   ((cohomologyPullback R (crossProductSnd X Y) q).hom b))) ∧
           (∀ u v, μ (TensorProduct.gradedMul R
               (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) = μ u * μ v) ∧
           μ ((1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y)) = 1 ∧
           ∃ rt : Ring (gradedCohomology R X ⊗[R] gradedCohomology R Y),
             (∀ u v, rt.add u v = u + v) ∧ rt.zero = 0 ∧ (∀ u, rt.neg u = -u) ∧
             (∀ u v, rt.mul u v = TensorProduct.gradedMul R
               (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n) u v) ∧
             rt.one = (1 : gradedCohomology R X) ⊗ₜ[R] (1 : gradedCohomology R Y) ∧
             (letI := rt
              letI : Mul (gradedCohomology R X ⊗[R] gradedCohomology R Y) := rt.toMul
              ∃ Φ : (gradedCohomology R X ⊗[R] gradedCohomology R Y) ≃+*
                  gradedCohomology R (crossProductSpace X Y),
                ∀ u, Φ u = μ u))) := by
  classical
  obtain ⟨G, hG, hA⟩ := cohomology_graded_ring_data R
  refine ⟨G, hG, ?_⟩
  let := G X
  let := G Y
  let := G (crossProductSpace X Y)
  let AX := (hA X).some
  let AY := (hA Y).some
  let AP := (hA (crossProductSpace X Y)).some
  refine ⟨AX, AY, AP, ?_⟩
  have hfinite : ∀ q : ℕ, ∃ (ι : Type u) (_ : Fintype ι),
      Nonempty (Module.Basis ι R (cohomology R Y q)) := by
    intro q
    let : Module.Free R (cohomology R Y q) := (hfree q).1
    let : Module.Finite R (cohomology R Y q) := (hfree q).2
    exact HolomorphicAnosov.AlgebraicTopology.finite_basis_of_free_finite R
      (cohomology R Y q)
  have hdegree := degreewise_cross_product_kunneth R X Y hfree (hG (crossProductSpace X Y))
  refine ⟨hdegree, ?_⟩
  choose μ hμ using hdegree
  obtain ⟨ν, hν⟩ :=
    HolomorphicAnosov.AlgebraicTopology.total_equiv_of_degree_equivs R
      (fun n ↦ cohomology R X n) (fun n ↦ cohomology R Y n)
      (fun n ↦ cohomology R (crossProductSpace X Y) n) μ
  have hpure : ∀ (p q : ℕ) (a : cohomology R X p) (b : cohomology R Y q),
      ν ((DirectSum.lof R ℕ (fun n ↦ cohomology R X n) p a) ⊗ₜ[R]
          (DirectSum.lof R ℕ (fun n ↦ cohomology R Y n) q b)) =
        DirectSum.lof R ℕ (fun n ↦ cohomology R (crossProductSpace X Y) n) (p + q)
          (GradedMonoid.GMul.mul
            (A := fun n : ℕ ↦ cohomology R (crossProductSpace X Y) n)
            ((cohomologyPullback R (crossProductFst X Y) p).hom a)
            ((cohomologyPullback R (crossProductSnd X Y) q).hom b)) := by
    intro p q a b
    rw [hν p q a b]
    rw [hμ (p + q) ⟨(p, q), rfl⟩ a b]
    congr 1
  obtain ⟨hmul, hone, hring⟩ := total_cross_product_ring_data R X Y (hG X) (hG Y)
    (hG (crossProductSpace X Y)) ν hpure
  exact ⟨ν, hpure, hmul, hone, hring⟩

end HolomorphicAnosov.SingularCochain

