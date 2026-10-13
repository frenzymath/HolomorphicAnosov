import HolomorphicAnosov.Topology.EuclideanPositiveLocalClass
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceAvoidsZero
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.IntegralReducedHomologyIsoOfHomotopyEquiv
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Unique_reduced_zero
import Mathlib.Analysis.Convex.Contractible

/-! The actual signed boundary of the positive local simplex under the relative
connecting isomorphism. Source: Hatcher, Algebraic Topology, pp.108,116–118,
233–234. All chains and their classes have the original integral coefficients. -/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov
open GoodPair

/-- The i-th face of the prescribed positive simplex as a singular simplex in
punctured Euclidean space. Its missing barycentric weight prevents it from
meeting the origin (Hatcher's local orientation construction, pp.233–234). -/
def euclideanPositivePuncturedFace (n : ℕ) (i : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)),
      ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))
  exact ⟨fun t ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t,
    euclideanPositiveSimplex_face_avoids_zero n i t⟩,
    (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩

/-- The alternating, coefficient-one boundary chain in the punctured space.
Source: Hatcher p.108. Augmented index n+1 denotes ordinary chain degree n. -/
def euclideanPositiveBoundaryChain (n : ℕ) :
    (augmentedIntegralSingularChains
      (TopCat.of (↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)))).X (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (TopCat.toSSet.obj (TopCat.of (↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)))).ιChainComplex
      (R := reducedSingularIntegralCoefficients)
      (((TopCat.of (↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ))).toSSetObjEquiv
        (op ⦋n⦌)).symm (euclideanPositivePuncturedFace n i)) (ULift.up 1)

/-- Inclusion takes the signed punctured face chain to the boundary of the
specified simplex, with exactly the usual positive connecting sign.
Source: Hatcher p.108 and pp.116–118. This follows termwise from naturality
of singular generators under inclusion and the alternating boundary formula. -/
theorem euclideanPositiveBoundaryChain_inclusion (n : ℕ) :
    (augmentedIntegralSingularChainsMap (singularSubspaceInclusion
      (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ)).f (n + 1)
      (euclideanPositiveBoundaryChain n) =
    (augmentedIntegralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))).d
      (n + 2) (n + 1)
      ((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))).ιChainComplex
        (R := reducedSingularIntegralCoefficients)
        (((TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))).toSSetObjEquiv
          (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))) (ULift.up 1)) := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := {0}ᶜ
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))
  let τ (i : Fin (n + 2)) := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm
    (euclideanPositivePuncturedFace n i)
  have hτ (i : Fin (n + 2)) :
      (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ (τ i) =
        (TopCat.toSSet.obj X).δ i σ := by
    apply (X.toSSetObjEquiv _).injective
    ext t
    rfl
  have hf (i : Fin (n + 2)) :
      (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) (τ i) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A)) R).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) ((TopCat.toSSet.obj X).δ i σ) := by
    rw [SSet.ι_chainComplexMap_f, hτ]
  have hd := SSet.ιChainComplex_d (TopCat.toSSet.obj X) R σ
  change (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A)) R).f n
      (∑ i, (-1 : ℤ) ^ i.val •
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) (τ i)) (ULift.up 1)) = _
  simp only [map_sum, map_zsmul]
  change _ = ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
    ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n) (ULift.up 1)
  rw [hd]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z ↦ (-1 : ℤ) ^ i.val • z)
    (congrArg (fun f ↦ f (ULift.up 1)) (hf i))


/-- The signed face chain is a cycle in the augmented punctured-space complex,
including the augmentation-kernel case n=0. Source: Hatcher pp.108,110,116–118.
After the injective subspace chain map its differential is the second boundary
of the original simplex, hence zero. -/
theorem euclideanPositiveBoundaryChain_cycle (n : ℕ) :
    ((augmentedIntegralSingularChains
      (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ))).sc (n + 1)).g.hom
      (euclideanPositiveBoundaryChain n) = 0 := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := {0}ᶜ
  let K := augmentedIntegralSingularChains (TopCat.of A)
  let L := augmentedIntegralSingularChains X
  let f := augmentedIntegralSingularChainsMap (singularSubspaceInclusion X A)
  have hf : Mono f := (augmentedPairShortComplex_shortExact X A).mono_f
  have hfn : Mono (f.f n) := by infer_instance
  change K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) _ = 0
  rw [ChainComplex.next_nat_succ]
  apply (ModuleCat.mono_iff_injective (f.f n)).mp hfn
  rw [map_zero]
  change (K.d (n + 1) n ≫ f.f n) (euclideanPositiveBoundaryChain n) = 0
  rw [← f.comm]
  change L.d (n + 1) n (f.f (n + 1) (euclideanPositiveBoundaryChain n)) = 0
  rw [euclideanPositiveBoundaryChain_inclusion]
  change (L.d (n + 2) (n + 1) ≫ L.d (n + 1) n) _ = 0
  rw [L.d_comp_d]
  rfl

/-- The specified alternating boundary class in reduced punctured-space
homology. Source: Hatcher pp.108–110,116–118. Its data are the actual signed
face chain, with the proved cycle certificate, not a chosen generator. -/
def euclideanPositiveBoundaryClass (n : ℕ) :
    integralReducedSingularHomology
      (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n :=
  integralChainCycleClass _ (n + 1)
    ⟨euclideanPositiveBoundaryChain n, euclideanPositiveBoundaryChain_cycle n⟩

/-- The augmented relative cycle representing the SAME positive local class.
The shift changes the index only; the underlying chain is unchanged. -/
def euclideanPositiveAugmentedLocalCycle (n : ℕ) :
    LinearMap.ker ((augmentedRelativeChains
      (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ).sc (n + 2)).g.hom := by
  refine ⟨euclideanPositiveLocalChain (n + 1), ?_⟩
  change (augmentedRelativeChains
    (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ).d
      (n + 2) ((ComplexShape.down ℕ).next (n + 2)) _ = 0
  rw [ChainComplex.next_nat_succ]
  have h := euclideanPositiveLocalChain_cycle (n + 1)
  change ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
    {0}ᶜ).chainComplex reducedSingularIntegralCoefficients).d
      (n + 1) ((ComplexShape.down ℕ).next (n + 1)) _ = 0 at h
  rw [ChainComplex.next_nat_succ] at h
  exact h

/-- Relative connecting sends the coefficient-one positive local class to its
actual signed face class, with positive boundary sign. Source: Hatcher
pp.116–118. Use the original simplex as a lift of the quotient cycle and
its explicit alternating boundary in the punctured space; the augmented
cycle formula and grading isomorphism preserve precisely these classes. -/
theorem euclideanPositiveLocalClass_connecting (n : ℕ) :
    ((augmentedRelativeHomologyIso
      (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ (n + 1)).inv ≫
      augmentedPairConnecting
        (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ n)
      (euclideanPositiveLocalClass (n + 1)) = euclideanPositiveBoundaryClass n := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := {0}ᶜ
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))
  let c := (TopCat.toSSet.obj X).ιChainComplex (R := R) σ (ULift.up 1)
  let a : LinearMap.ker ((augmentedIntegralSingularChains (TopCat.of A)).sc (n + 1)).g.hom :=
    ⟨euclideanPositiveBoundaryChain n, euclideanPositiveBoundaryChain_cycle n⟩
  let rc := euclideanPositiveAugmentedLocalCycle n
  have hshift := augmentedRelativeHomologyIso_cycle X A (n + 1) rc
    ⟨euclideanPositiveLocalChain (n + 1), euclideanPositiveLocalChain_cycle (n + 1)⟩ rfl
  have hclass : (augmentedRelativeHomologyIso X A (n + 1)).inv
      (euclideanPositiveLocalClass (n + 1)) =
      integralChainCycleClass (augmentedRelativeChains X A) (n + 2) rc := by
    rw [← (show (augmentedRelativeHomologyIso X A (n + 1)).hom
      (integralChainCycleClass (augmentedRelativeChains X A) (n + 2) rc) =
      euclideanPositiveLocalClass (n + 1) from hshift)]
    exact (augmentedRelativeHomologyIso X A (n + 1)).hom_inv_id_apply _
  change augmentedPairConnecting X A n
    ((augmentedRelativeHomologyIso X A (n + 1)).inv
      (euclideanPositiveLocalClass (n + 1))) = _
  rw [hclass]
  exact augmented_pair_connecting_cycle X A n c a rc rfl
    (euclideanPositiveBoundaryChain_inclusion n)


/-- The positive-dimensional local connecting map is an isomorphism onto
reduced homology of punctured Euclidean space. Source: Hatcher pp.116–118,126.
Euclidean space contracts to a point, so the two adjacent reduced homology
terms vanish; exactness makes the connecting map both injective and surjective.
This includes n=0, whose target is reduced H₀ of the punctured line. -/
theorem euclideanPositiveLocalConnecting_isIso (n : ℕ) :
    IsIso ((augmentedRelativeHomologyIso
      (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ (n + 1)).inv ≫
      augmentedPairConnecting
        (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ n) := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := {0}ᶜ
  have hzero (q : ℕ) : IsZero (integralReducedSingularHomology X q) := by
    obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
    exact IsZero.of_iso
      (HolomorphicAnosov.Topology.Homology.unique_reduced_zero (TopCat.of Unit) q)
      (HolomorphicAnosov.Topology.Homology.integralReducedHomologyIsoOfHomotopyEquiv e q)
  have hmono : Mono (augmentedPairConnecting X A n) :=
    ((augmentedPairShortComplex_shortExact X A).homology_exact₃
      (n + 2) (n + 1) (by simp)).mono_g ((hzero (n + 1)).eq_of_src _ _)
  have hepi : Epi (augmentedPairConnecting X A n) :=
    ((augmentedPairShortComplex_shortExact X A).homology_exact₁
      (n + 2) (n + 1) (by simp)).epi_f ((hzero n).eq_of_tgt _ _)
  have : IsIso (augmentedPairConnecting X A n) := isIso_of_mono_of_epi _
  infer_instance

/-- Freeness of the specified local class is exactly freeness of its signed
punctured boundary class. Source: Hatcher pp.116–118,233–234. The connecting
isomorphism sends one class to the other and commutes with integer multiples,
so it transports bijectivity of their coefficient maps. -/
theorem euclideanPositiveLocalClass_free_generator_iff_boundary (n : ℕ) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass (n + 1))) ↔
    Function.Bijective (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveBoundaryClass n)) := by
  let f := (augmentedRelativeHomologyIso
      (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ (n + 1)).inv ≫
      augmentedPairConnecting (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) {0}ᶜ n
  have hf : IsIso f := euclideanPositiveLocalConnecting_isIso n
  have hbij : Function.Bijective f := (ConcreteCategory.isIso_iff_bijective f).mp hf
  have heq : (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveBoundaryClass n)) =
      f.hom.comp (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass (n + 1))) := by
    apply LinearMap.ext_ring
    simp only [LinearMap.toSpanSingleton_apply, LinearMap.comp_apply, one_smul]
    exact (euclideanPositiveLocalClass_connecting n).symm
  rw [heq]
  change Function.Bijective _ ↔ Function.Bijective (f ∘ _)
  exact (Function.Bijective.of_comp_iff' hbij _).symm

end HolomorphicAnosov
