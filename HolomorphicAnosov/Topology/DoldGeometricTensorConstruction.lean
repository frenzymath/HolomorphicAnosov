import HolomorphicAnosov.Topology.DoldSupportOperatorG1
import HolomorphicAnosov.Topology.SingularChainsULiftDegreeComparison
import HolomorphicAnosov.Topology.SingularChainsULiftBoundary
import HolomorphicAnosov.Topology.SingularChainsULiftNaturality
import HolomorphicAnosov.Topology.ChainComplexIsoHomology
import HolomorphicAnosov.Topology.FiniteFixedPointIndexSum
import HolomorphicAnosov.Topology.FunctorialTraceConjugacy
import Mathlib.LinearAlgebra.Trace

/-!
# The geometric tensor in Dold's compact ENR formula

Dold (1965), (4.3)–(4.4), pp.5–6. The imported support identity is Lemma (4.2).
The diagonal's pure Künneth summands give the signed trace by linearity;
its displacement evaluation is the canonical index. The final tensor is the
unique inverse image of the prescribed signed endomorphism under dualTensorHom.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open scoped TensorProduct
namespace HolomorphicAnosov.FixedPointIndexInterface
universe u
namespace DoldConstruction
open RationalRelativeKunneth

/-- Transport an absolute homology class along equality of its degree. -/
def regradeHomology (X : TopCat.{u}) {n m : ℕ} (h : n = m) :
    homology X n →ₗ[ℚ] homology X m := by
  subst m
  exact LinearMap.id

lemma regradeHomology_cycleClass_map (X : TopCat.{u})
    {C : ChainComplex (ModuleCat.{u} ℚ) ℕ} (f : C ⟶ chains X)
    {n m : ℕ} (h : n = m) (a : cycles C m) (b : cycles (chains X) n)
    (hb : HEq b.val ((f.f m).hom a.val)) :
    regradeHomology X h (cycleClass (chains X) n b) =
      (HomologicalComplex.homologyMap f m).hom (cycleClass C m a) := by
  subst m
  exact (cycleClass_map f n a b (eq_of_heq hb).symm).symm

set_option backward.isDefEq.respectTransparency false in
lemma absoluteCross_swap (X Z : TopCat.{u}) (p q : ℕ)
    (a : homology X p) (b : homology Z q) :
    (homologyMap (swapMap X Z) (p + q)).hom (absoluteCross X Z p q a b) =
      (-1 : ℚ) ^ (p * q) • regradeHomology (TopCat.of (Z × X)) (Nat.add_comm q p)
        (absoluteCross Z X q p b a) := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (chains X) p a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (chains Z) q b
  simp only [absoluteCross, absoluteCrossTensor, quotientTensor_cycleClass,
    absoluteCycleClasses, LinearMap.compr₂_apply]
  rw [← (regradeHomology (TopCat.of (Z × X)) (Nat.add_comm q p)).map_smul]
  rw [← (cycleClass (chains (TopCat.of (Z × X))) (q + p)).map_smul]
  symm
  apply regradeHomology_cycleClass_map
  change HEq ((-1 : ℚ) ^ (p * q) • SignedShuffle.shuffleBilinear Z X q p b.val a.val)
    ((SSet.chainComplexMap (TopCat.toSSet.map (swapMap X Z)) coefficients.{u}).f (p + q)
      (SignedShuffle.shuffleBilinear X Z p q a.val b.val))
  erw [SignedShuffle.shuffleBilinear_swap X Z p q a.val b.val]
  rw [← (SignedShuffle.regrade (TopCat.of (Z × X)) (Nat.add_comm q p)).map_smul]
  have hh {i j : ℕ} (h : i = j) (c : (chains (TopCat.of (Z × X))).X i) :
      HEq c (SignedShuffle.regrade (TopCat.of (Z × X)) h c) := by
    subst j
    rfl
  exact hh _ _

lemma cross_regrade_right (X Z : TopCat.{u}) (A : Set X) (p : ℕ) {q r : ℕ} (h : q = r)
    (a : relativeHomology X A p) (b : homology Z q) :
    cross X Z A p r a (regradeHomology Z h b) =
      regradeRelative (TopCat.of (X × Z)) (productSubspace X Z A)
        (congrArg (p + ·) h) (cross X Z A p q a b) := by
  subst r
  rfl

lemma regradeRelative_comp (X : TopCat.{u}) (A : Set X) {i j k : ℕ}
    (h : i = j) (h' : j = k) (a : relativeHomology X A i) :
    regradeRelative X A h' (regradeRelative X A h a) = regradeRelative X A (h.trans h') a := by
  subst j
  subst k
  rfl


set_option backward.isDefEq.respectTransparency false in
lemma cross_middle_swap (X Z W : TopCat.{u}) (A : Set X) (hA : IsOpen A)
    (p q r : ℕ) (a : relativeHomology X A p) (b : homology Z q) (c : homology W r) :
    (relativeMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A))
      (productSubspace (TopCat.of (X × W)) Z (productSubspace X W A))
      (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + r)).hom
      (cross (TopCat.of (X × Z)) W (productSubspace X Z A) (p + q) r
        (cross X Z A p q a b) c) =
    (-1 : ℚ) ^ (q * r) •
      regradeRelative (TopCat.of ((X × W) × Z))
        (productSubspace (TopCat.of (X × W)) Z (productSubspace X W A))
        (n := (p + r) + q) (m := (p + q) + r) (by omega)
        (cross (TopCat.of (X × W)) Z (productSubspace X W A) (p + r) q
          (cross X W A p r a c) b) := by
  let A₁ := productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A)
  let A₂ := productSubspace (TopCat.of (X × W)) Z (productSubspace X W A)
  let B₁ := productSubspace X (TopCat.of (Z × W)) A
  let B₂ := productSubspace X (TopCat.of (W × Z)) A
  let M := relativeMap A₁ A₂ (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + r)
  let J₁ := relativeMap A₁ B₁ (associatorMap X Z W) (fun _ hx ↦ hx) ((p + q) + r)
  let J₂ := relativeMap A₂ B₂ (associatorMap X W Z) (fun _ hx ↦ hx) ((p + q) + r)
  let F := productMap (𝟙 X) (swapMap Z W)
  have : IsIso J₂ := rationalPairHomeomorph_isIso
    (X := TopCat.of ((X × W) × Z)) (Y := TopCat.of (X × (W × Z)))
    (Homeomorph.prodAssoc X W Z) A₂ B₂ (fun _ ↦ Iff.rfl) ((p + q) + r)
  have hcomm : M ≫ J₂ = J₁ ≫ relativeMap B₁ B₂ F (fun _ hx ↦ hx) ((p + q) + r) := by
    rw [← relativeMap_comp A₁ A₂ B₂ (middleSwapMap X Z W) (fun _ hx ↦ hx)
      (associatorMap X W Z) (fun _ hx ↦ hx),
      ← relativeMap_comp A₁ B₁ B₂ (associatorMap X Z W) (fun _ hx ↦ hx) F (fun _ hx ↦ hx)]
    rfl
  have h₁ := (rational_relative_homology_cross_product_kunneth X Z A hA).2.2.2.2.2.2.2.2.2.1
    W p q r a b c
  have h₂ := (rational_relative_homology_cross_product_kunneth X W A hA).2.2.2.2.2.2.2.2.2.1
    Z p r q a c b
  apply (ModuleCat.mono_iff_injective J₂).mp inferInstance
  change J₂.hom (M.hom _) = J₂.hom ((-1 : ℚ) ^ (q * r) • _)
  rw [map_smul]
  change (M ≫ J₂).hom _ = _
  rw [hcomm]
  change (relativeMap B₁ B₂ F (fun _ hx ↦ hx) ((p + q) + r)).hom (J₁.hom _) = _
  change J₁.hom _ = _ at h₁
  rw [h₁]
  dsimp only [J₂]
  rw [relativeMap_regrade B₁ B₂ F (fun _ hx ↦ hx),
    relativeMap_regrade A₂ B₂ (associatorMap X W Z) (fun _ hx ↦ hx), h₂]
  have hn := cross_naturality A hA A (𝟙 X) (fun _ hx ↦ hx) (swapMap Z W)
    p (q + r) a (absoluteCross Z W q r b c)
  rw [relativeMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  change (relativeMap B₁ B₂ F (fun _ hx ↦ hx) (p + (q + r))).hom _ = _ at hn
  rw [hn, absoluteCross_swap]
  have hsmul {i j : ℕ} (a : relativeHomology X A i) (b : homology (TopCat.of (W × Z)) j) (s : ℚ) :
      cross X (TopCat.of (W × Z)) A i j a (s • b) =
        s • cross X (TopCat.of (W × Z)) A i j a b := by
    simp only [cross, TensorProduct.tmul_smul, map_smul]
  rw [hsmul, map_smul, cross_regrade_right, regradeRelative_comp, regradeRelative_comp]

set_option backward.isDefEq.respectTransparency false in
lemma exchangeEvaluation_cross_general {X Z W Y : TopCat.{u}} (A : Set X) (hA : IsOpen A)
    (D : Set Y) (d : TopCat.of (X × W) ⟶ Y)
    (hd : Set.MapsTo d (productSubspace X W A) D)
    (p q r : ℕ) (a : relativeHomology X A p) (b : homology Z q) (c : homology W r) :
    (relativeMap (productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A))
      (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
      (fun x hx ↦ hd hx) ((p + q) + r)).hom
      (cross (TopCat.of (X × Z)) W (productSubspace X Z A) (p + q) r
        (cross X Z A p q a b) c) =
    (-1 : ℚ) ^ (q * r) • regradeRelative (TopCat.of (Y × Z)) (productSubspace Y Z D)
      (n := (p + r) + q) (m := (p + q) + r) (by omega) (cross Y Z D (p + r) q
        ((relativeMap (productSubspace X W A) D d hd (p + r)).hom (cross X W A p r a c)) b) := by
  let A₁ := productSubspace (TopCat.of (X × Z)) W (productSubspace X Z A)
  let A₂ := productSubspace (TopCat.of (X × W)) Z (productSubspace X W A)
  have hc : relativeMap A₁ (productSubspace Y Z D) (exchangeEvaluationMap (Z := Z) d)
      (fun x hx ↦ hd hx) ((p + q) + r) =
    relativeMap A₁ A₂ (middleSwapMap X Z W) (fun _ hx ↦ hx) ((p + q) + r) ≫
    relativeMap A₂ (productSubspace Y Z D) (productMap d (𝟙 Z)) (fun x hx ↦ hd hx)
      ((p + q) + r) :=
    relativeMap_comp A₁ A₂ (productSubspace Y Z D) (middleSwapMap X Z W) (fun _ hx ↦ hx)
      (productMap d (𝟙 Z)) (fun x hx ↦ hd hx) ((p + q) + r)
  rw [hc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cross_middle_swap X Z W A hA, map_smul, relativeMap_regrade]
  have hn := cross_naturality (productSubspace X W A) (hA.preimage continuous_fst) D d hd (𝟙 Z)
    (p + r) q (cross X W A p r a c) b
  rw [homologyMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  exact congrArg ((-1 : ℚ) ^ (q * r) • ·) (congrArg (regradeRelative _ _ _) hn)

/-- The diagonal followed by contraction of its first and third factors. -/
def supportFromDiagonal (n q : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (z : homology (TopCat.of K) q) :
    kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n →ₗ[ℚ]
      homology (TopCat.of U) q :=
  (localProductCoordinate n (TopCat.of U) q).comp
    ((relativeMap (X := TopCat.of ((U × U) × K))
      (Y := TopCat.of ((EuclideanSpace ℝ (Fin n)) × U))
      (productSubspace (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)))
      (productSubspace (TopCat.of (EuclideanSpace ℝ (Fin n))) (TopCat.of U) ({0} : Set _)ᶜ)
      (exchangeEvaluationMap (X := TopCat.of U) (Z := TopCat.of U)
        (W := TopCat.of K) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
        (TopCat.ofHom (difference U K))) (fun _ hx ↦ difference_mapsTo U K hx) (n + q)).hom.comp
      ((crossTensor (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) n q).comp
          ((TensorProduct.mk ℚ _ _).flip z)))

lemma supportFromDiagonal_orientation (n q : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (z : homology (TopCat.of K) q) :
    supportFromDiagonal n q U K z
      ((relativeMap (X := TopCat.of U) (Y := TopCat.of (U × U)) (supportComplement U K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
        (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) n).hom
        (rationalSupportOrientation n U K hU hK hKU)) =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom z := by
  have h := congrArg (localProductCoordinate n (TopCat.of U) q)
    (supportValue_diagonal U K hK.isClosed n q
      (rationalSupportOrientation n U K hU hK hKU) z)
  change supportOperator n U K hU hK hKU q z = supportFromDiagonal n q U K z _ at h
  rw [supportOperator_identity] at h
  exact h.symm


set_option backward.isDefEq.respectTransparency false in
/-- A diagonal Künneth summand of the wrong second degree contributes zero. -/
lemma supportFromDiagonal_cross_ne (n p r q : ℕ) (hn : p + r = n) (hrq : r ≠ q)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (b : homology (TopCat.of U) r) (z : homology (TopCat.of K) q) :
    supportFromDiagonal n q U K z
      (regradeRelative (TopCat.of (U × U))
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) hn
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p r a b)) = 0 := by
  subst n
  change localProductCoordinate (p + r) (TopCat.of U) q
    ((relativeMap _ _ _ _ ((p + r) + q)).hom
      (cross (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) (p + r) q
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p r a b) z)) = 0
  rw [exchangeEvaluation_cross_general (X := TopCat.of U) (Z := TopCat.of U)
    (W := TopCat.of K) (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + r))))
    (supportComplement U K) (hK.isOpen_compl.preimage continuous_subtype_val)
    ({0} : Set (EuclideanSpace ℝ (Fin (p + r))))ᶜ (TopCat.ofHom (difference U K))
    (difference_mapsTo U K)]
  have : Subsingleton (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (p + r))))
      ({0} : Set _)ᶜ (p + q)) :=
    ModuleCat.subsingleton_of_isZero (rationalLocalHomology_isZero (p + r) (p + q) (by omega))
  have hz : (relativeMap (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
      ({0} : Set (EuclideanSpace ℝ (Fin (p + r))))ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom
      (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q a z) = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  simp only [cross, TensorProduct.zero_tmul, map_zero, smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The matching diagonal summand is contraction against the local difference
pairing, with precisely the degree-square Koszul sign. -/
lemma supportFromDiagonal_cross_eq (p q : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin (p + q)))) (hK : IsClosed K)
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (b : homology (TopCat.of U) q) (z : homology (TopCat.of K) q) :
    supportFromDiagonal (p + q) q U K z
      (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b) =
      (-1 : ℚ) ^ (q * q) • (rationalLocalCoordinate (p + q)
        ((relativeMap (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
          ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
          (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom
          (cross (TopCat.of U) (TopCat.of K) (supportComplement U K) p q a z))) • b := by
  change localProductCoordinate (p + q) (TopCat.of U) q
    ((relativeMap _ _ _ _ ((p + q) + q)).hom
      (cross (TopCat.of (U × U)) (TopCat.of K)
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) (p + q) q
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b) z)) = _
  rw [exchangeEvaluation_cross (X := TopCat.of U) (Z := TopCat.of U)
    (W := TopCat.of K) (Y := TopCat.of (EuclideanSpace ℝ (Fin (p + q))))
    (supportComplement U K) (hK.isOpen_compl.preimage continuous_subtype_val)
    ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ (TopCat.ofHom (difference U K))
    (difference_mapsTo U K), map_smul, localProductCoordinate_cross]


/-- Bilinear form of the diagonal support operation. -/
def diagonalOperator (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) :
    kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n →ₗ[ℚ]
      homology (TopCat.of K) q →ₗ[ℚ] homology (TopCat.of U) q where
  toFun t := {
    toFun z := supportFromDiagonal n q U K z t
    map_add' z w := by simp [supportFromDiagonal]
    map_smul' r z := by simp [supportFromDiagonal] }
  map_add' t v := by ext z; exact map_add (supportFromDiagonal n q U K z) t v
  map_smul' r t := by ext z; exact map_smul (supportFromDiagonal n q U K z) r t

/-- Difference pairing with a class of complementary relative degree. -/
def differenceFunctional (p q : ℕ) (U K : Set (EuclideanSpace ℝ (Fin (p + q))))
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p) :
    Module.Dual ℚ (homology (TopCat.of K) q) :=
  (rationalLocalCoordinate (p + q)).toLinearMap.comp
    ((relativeMap (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
      ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
      (TopCat.ofHom (difference U K)) (difference_mapsTo U K) (p + q)).hom.comp
        ((crossTensor (TopCat.of U) (TopCat.of K) (supportComplement U K) p q).comp
          (TensorProduct.mk ℚ _ _ a)))

/-- Evaluation of the diagonal after applying the map in its second factor. -/
def diagonalEvaluation (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) (G : C(U, K)) :
    kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n →ₗ[ℚ] ℚ :=
  (rationalLocalCoordinate n).toLinearMap.comp
    ((relativeMap (X := TopCat.of (U × U)) (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
      ({0} : Set _)ᶜ (productMap (𝟙 (TopCat.of U)) (TopCat.ofHom G) ≫
        TopCat.ofHom (difference U K)) (fun _x hx ↦ difference_mapsTo U K hx) n).hom)

/-- Degree-q trace of the diagonal support operation followed by the map. -/
def diagonalTrace (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) (G : C(U, K)) (q : ℕ) :
    kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n →ₗ[ℚ] ℚ :=
  (LinearMap.trace ℚ (homology (TopCat.of K) q)).comp
    ((LinearMap.compRight ℚ
      (homologyMap (TopCat.ofHom G) q).hom).comp (diagonalOperator n U K q))

set_option backward.isDefEq.respectTransparency false in
lemma diagonalEvaluation_cross (p q : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin (p + q)))) (hK : IsClosed K) (G : C(U, K))
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (b : homology (TopCat.of U) q) :
    diagonalEvaluation (p + q) U K G
      (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b) =
      differenceFunctional p q U K a ((homologyMap (TopCat.ofHom G) q).hom b) := by
  have hn := cross_naturality (X := TopCat.of U) (Z := TopCat.of U)
    (X' := TopCat.of U) (Z' := TopCat.of K)
    (supportComplement U K) (hK.isOpen_compl.preimage continuous_subtype_val)
    (supportComplement U K) (𝟙 (TopCat.of U)) (fun _ hx ↦ hx) (TopCat.ofHom G) p q a b
  rw [relativeMap_identity] at hn
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at hn
  dsimp only [targetMap] at hn
  dsimp only [diagonalEvaluation, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
    differenceFunctional]
  rw [relativeMap_comp (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
    (productSubspace (TopCat.of U) (TopCat.of K) (supportComplement U K))
    ({0} : Set (EuclideanSpace ℝ (Fin (p + q))))ᶜ
    (productMap (𝟙 (TopCat.of U)) (TopCat.ofHom G)) (fun _ hx ↦ hx)
    (TopCat.ofHom (difference U K)) (difference_mapsTo U K)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hn]
  rfl

lemma diagonalTrace_cross_ne (n p r q : ℕ) (hn : p + r = n) (hrq : r ≠ q)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K) (G : C(U, K))
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (b : homology (TopCat.of U) r) :
    diagonalTrace n U K G q
      (regradeRelative (TopCat.of (U × U))
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) hn
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p r a b)) = 0 := by
  have he : diagonalOperator n U K q
      (regradeRelative (TopCat.of (U × U))
        (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K)) hn
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p r a b)) = 0 := by
    ext z
    exact supportFromDiagonal_cross_ne n p r q hn hrq U K hK a b z
  simp only [diagonalTrace, LinearMap.comp_apply, he, map_zero]

lemma diagonalTrace_cross_eq (p q : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin (p + q)))) (hK : IsClosed K) (G : C(U, K))
    [FiniteDimensional ℚ (homology (TopCat.of K) q)]
    (a : relativeHomology (TopCat.of U) (supportComplement U K) p)
    (b : homology (TopCat.of U) q) :
    diagonalTrace (p + q) U K G q
      (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b) =
      (-1 : ℚ) ^ (q * q) * differenceFunctional p q U K a
        ((homologyMap (TopCat.ofHom G) q).hom b) := by
  have he : (homologyMap (TopCat.ofHom G) q).hom.comp
      (diagonalOperator (p + q) U K q
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b)) =
      (-1 : ℚ) ^ (q * q) • (differenceFunctional p q U K a).smulRight
        ((homologyMap (TopCat.ofHom G) q).hom b) := by
    ext z
    change (homologyMap (TopCat.ofHom G) q).hom
      (supportFromDiagonal (p + q) q U K z
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b)) = _
    rw [supportFromDiagonal_cross_eq p q U K hK, map_smul, map_smul]
    rfl
  change LinearMap.trace ℚ (homology (TopCat.of K) q)
    ((homologyMap (TopCat.ofHom G) q).hom.comp
      (diagonalOperator (p + q) U K q
        (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b))) = _
  rw [he, map_smul, LinearMap.trace_smulRight]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The signed sum of the diagonal operators is the diagonal difference
pairing. This is the finite-dimensional contraction identity in Dold (4.4). -/
lemma diagonal_signed_trace (n d : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K) (G : C(U, K))
    [∀ k, FiniteDimensional ℚ (homology (TopCat.of K) k)]
    (hz : ∀ k, d < k → Subsingleton (homology (TopCat.of K) k))
    (t : kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n) :
    ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) * diagonalTrace n U K G k t =
      diagonalEvaluation n U K G t := by
  classical
  let L : kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n →ₗ[ℚ] ℚ :=
    ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) • diagonalTrace n U K G k
  suffices h : L t = diagonalEvaluation n U K G t by
    simpa only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
  obtain ⟨s, rfl⟩ := (kunnethMap_bijective (TopCat.of U) (TopCat.of U)
    (supportComplement U K) n).2 t
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | of pq s =>
    induction s using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rcases pq with ⟨⟨p, q⟩, hpq⟩
      dsimp only at hpq
      subst n
      change L (kunnethMap (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q)
        (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b))) = _
      have hc : kunnethMap (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q)
          (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b)) =
          cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b := by
        simp [kunnethMap, cross, regradeRelative]
      change L (kunnethMap (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q)
        (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b))) =
        diagonalEvaluation (p + q) U K G (kunnethMap (TopCat.of U) (TopCat.of U) (supportComplement U K) (p + q)
          (DirectSum.lof ℚ (bidegree (p + q)) _ ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b)))
      rw [hc]
      dsimp only [L]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [diagonalEvaluation_cross p q U K hK G]
      have hne (k : ℕ) (hk : q ≠ k) :
          diagonalTrace (p + q) U K G k
            (cross (TopCat.of U) (TopCat.of U) (supportComplement U K) p q a b) = 0 := by
        simpa only [regradeRelative, LinearMap.id_apply] using
          diagonalTrace_cross_ne (p + q) p q k rfl hk U K hK G a b
      by_cases hqd : q ≤ d
      · rw [Finset.sum_eq_single q]
        · rw [diagonalTrace_cross_eq p q U K hK G]
          have hs : (-1 : ℚ) ^ (q * q) * (-1 : ℚ) ^ (q * q) = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]
            norm_num
          rw [← mul_assoc, hs, one_mul]
        · intro k hk hkq
          rw [hne k (Ne.symm hkq), mul_zero]
        · intro hq
          exact False.elim (hq (Finset.mem_range.mpr (by omega)))
      · have hzero := hz q (by omega)
        have hb : (homologyMap (TopCat.ofHom G) q).hom b = 0 := hzero.elim _ _
        rw [hb, map_zero]
        apply Finset.sum_eq_zero
        intro k hk
        rw [hne k (by have := Finset.mem_range.mp hk; omega), mul_zero]

/-- The oriented diagonal class used in Dold's construction. -/
def orientedDiagonal (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    kunnethTarget (TopCat.of U) (TopCat.of U) (supportComplement U K) n :=
  (relativeMap (X := TopCat.of U) (Y := TopCat.of (U × U)) (supportComplement U K)
    (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement U K))
    (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx) n).hom
    (rationalSupportOrientation n U K hU hK hKU)

lemma diagonalTrace_orientation (n q : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (G : C(U, K)) :
    diagonalTrace n U K G q (orientedDiagonal n U K hU hK hKU) =
      LinearMap.trace ℚ (homology (TopCat.of K) q)
        (homologyMap (TopCat.ofHom (G.comp (ContinuousMap.inclusion hKU))) q).hom := by
  have he : diagonalOperator n U K q (orientedDiagonal n U K hU hK hKU) =
      (homologyMap (TopCat.ofHom (ContinuousMap.inclusion hKU)) q).hom := by
    ext z
    exact supportFromDiagonal_orientation n q U K hU hK hKU z
  simp only [diagonalTrace, LinearMap.comp_apply, he, LinearMap.compRight_apply]
  rw [show TopCat.ofHom (G.comp (ContinuousMap.inclusion hKU)) =
    TopCat.ofHom (ContinuousMap.inclusion hKU) ≫ TopCat.ofHom G from rfl,
    homologyMap_comp, ModuleCat.hom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the oriented diagonal reads the original integral displacement index,
with compact support enlarged from the fixed set to the image-containing set K. -/
lemma diagonalEvaluation_orientation (n : ℕ) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ U)
    (G : C(U, K))
    (hF : IsCompact (euclideanFixedSet
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin n))).comp G))) :
    diagonalEvaluation n U K G (orientedDiagonal n U K U.isOpen hK hKU) =
      (euclideanFixedPointIndex
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin n))).comp G) hF : ℚ) := by
  let f : C(U, EuclideanSpace ℝ (Fin n)) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin n))).comp G
  let F := euclideanAmbientFixedSet f
  have hFK : F ⊆ K := by
    rintro x ⟨y, hy, rfl⟩
    change f y = y.val at hy
    rw [← hy]
    exact (G y).property
  have hFc : IsCompact F := hF.image continuous_subtype_val
  have hFU : F ⊆ U := by rintro x ⟨y, hy, rfl⟩; exact y.property
  have hdF : Set.MapsTo (TopCat.ofHom (euclideanDisplacement f))
      (supportComplement (U : Set _) F) ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ := by
    intro x hx hz
    exact hx ⟨x, (sub_eq_zero.mp hz).symm, rfl⟩
  have hdK : Set.MapsTo (TopCat.ofHom (euclideanDisplacement f))
      (supportComplement (U : Set _) K) ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ := by
    intro x hx
    exact hdF (fun h ↦ hx (hFK h))
  have hor := rationalSupportOrientation_support n U F K U.isOpen hFc hK hFK hKU
  have hindex := congrArg (rationalLocalCoordinate n) (rational_displacement_index f hF)
  rw [map_smul, rationalLocalCoordinate_positive, smul_eq_mul, mul_one] at hindex
  change rationalLocalCoordinate n
    ((relativeMap (supportComplement (U : Set _) F) ({0} : Set _)ᶜ
      (TopCat.ofHom (euclideanDisplacement f)) hdF n).hom
      (rationalSupportOrientation n U F U.isOpen hFc hFU)) = _ at hindex
  rw [← hor] at hindex
  dsimp only [diagonalEvaluation, orientedDiagonal, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have hcomp := relativeMap_comp (supportComplement (U : Set _) K)
    (productSubspace (TopCat.of U) (TopCat.of U) (supportComplement (U : Set _) K))
    ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
    (diagonalMap (TopCat.of U)) (fun _ hx ↦ hx)
    (productMap (𝟙 (TopCat.of U)) (TopCat.ofHom G) ≫ TopCat.ofHom (difference U K))
    (fun _ hx ↦ difference_mapsTo U K hx) n
  have hm : diagonalMap (TopCat.of U) ≫
      (productMap (𝟙 (TopCat.of U)) (TopCat.ofHom G) ≫ TopCat.ofHom (difference U K)) =
      TopCat.ofHom (euclideanDisplacement f) := rfl
  change relativeMap (supportComplement (U : Set _) K) ({0} : Set _)ᶜ
    (TopCat.ofHom (euclideanDisplacement f)) hdK n = _ at hcomp
  change rationalLocalCoordinate n
    ((relativeMap _ _ _ _ n ≫ relativeMap _ _ _ _ n).hom _) = _
  erw [← hcomp]
  have hc := relativeMap_comp (supportComplement (U : Set _) K)
    (supportComplement (U : Set _) F) ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
    (𝟙 (TopCat.of U)) (fun _ hx h ↦ hx (hFK h))
    (TopCat.ofHom (euclideanDisplacement f)) hdF n
  simp only [Category.id_comp] at hc
  rw [hc]
  exact hindex

/-- Dold's Lefschetz identity for a map from an open Euclidean neighborhood into
its compact support. All coefficients come from the fixed positive orientation. -/
lemma compactImage_trace_index (n d : ℕ) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ U)
    (G : C(U, K))
    [∀ k, FiniteDimensional ℚ (homology (TopCat.of K) k)]
    (hz : ∀ k, d < k → Subsingleton (homology (TopCat.of K) k))
    (hF : IsCompact (euclideanFixedSet
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin n))).comp G))) :
    ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
      LinearMap.trace ℚ (homology (TopCat.of K) k)
        (homologyMap (TopCat.ofHom (G.comp (ContinuousMap.inclusion hKU))) k).hom =
      (euclideanFixedPointIndex
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin n))).comp G) hF : ℚ) := by
  have h := diagonal_signed_trace n d U K hK.isClosed G hz
    (orientedDiagonal n U K U.isOpen hK hKU)
  simp only [diagonalTrace_orientation] at h
  exact h.trans (diagonalEvaluation_orientation n U K hK hKU G hF)

/-- Canonical comparison between the rational homology of a universe lift and
its small native model, commuting with the actual self-map. -/
lemma homology_ulift_comparison (X : TopCat.{0}) (f : C(X, X)) (k : ℕ) :
    let upf : C(ULift.{u} X, ULift.{u} X) :=
      ⟨fun y ↦ ULift.up (f y.down),
        Homeomorph.ulift.symm.continuous.comp (f.continuous.comp Homeomorph.ulift.continuous)⟩
    ∃ e : homology (TopCat.of (ULift.{u} X)) k ≃ₗ[ℚ] homology X k,
      ∀ z, e ((homologyMap (TopCat.ofHom upf) k).hom z) =
        (homologyMap (TopCat.ofHom f) k).hom (e z) := by
  classical
  dsimp only
  let K (Y : TopCat.{0}) := (TopCat.toSSet.obj (TopCat.of (ULift.{u} Y))).chainComplex
    (ModuleCat.of ℚ (ULift.{u} ℚ))
  let L (Y : TopCat.{0}) := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)
  choose e he using (fun (Y : TopCat.{0}) (j : ℕ) ↦
    singular_chains_ulift_degree_comparison.{u} Y j)
  have hd (Y : TopCat.{0}) : ∀ j x,
      (e Y j) ((K Y).d (j + 1) j x) = (L Y).d (j + 1) j ((e Y (j + 1)) x) :=
    singular_chains_ulift_boundary.{u} Y (fun j ↦ (e Y j).toLinearMap) (he Y)
  obtain ⟨_, _, h⟩ := chain_complex_ulift_comparison K L e hd
  obtain ⟨h, hh⟩ := h k
  let upf : C(ULift.{u} X, ULift.{u} X) :=
    ⟨fun y ↦ ULift.up (f y.down),
      Homeomorph.ulift.symm.continuous.comp (f.continuous.comp Homeomorph.ulift.continuous)⟩
  have hn : ∀ z, h X ((homologyMap (TopCat.ofHom upf) k).hom z) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
        (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)).hom (h X z) := by
    apply hh X X
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom upf))
        (ModuleCat.of ℚ (ULift.{u} ℚ)))
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℚ ℚ))
    intro j c
    exact singular_chains_ulift_naturality.{u} X X f j
      (e X j).toLinearMap (e X j).toLinearMap (he X j) (he X j) c
  let c := (ordinaryRationalHomologyIso X k).toLinearEquiv
  refine ⟨(h X).trans c.symm, ?_⟩
  intro z
  apply c.injective
  change c (c.symm (h X ((homologyMap (TopCat.ofHom upf) k).hom z))) =
    c ((homologyMap (TopCat.ofHom f) k).hom (c.symm (h X z)))
  erw [c.apply_symm_apply, hn]
  have hc := congrArg (fun m ↦ m.hom (c.symm (h X z)))
    (ordinaryRationalHomologyIso_naturality (TopCat.ofHom f) k)
  change c ((homologyMap (TopCat.ofHom f) k).hom (c.symm (h X z))) =
    _ at hc
  rw [hc]
  change _ = (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)).hom (c (c.symm (h X z)))
  erw [c.apply_symm_apply]

/-- Homeomorphic models in different universes have conjugate native rational
homology endomorphisms; the equivalence also transports finiteness and vanishing. -/
lemma homology_homeomorph_comparison {X : Type u} [TopologicalSpace X]
    {Z : Type} [TopologicalSpace Z] (E : X ≃ₜ Z) (f : C(X, X)) (g : C(Z, Z))
    (hfg : ∀ x, E (f x) = g (E x)) (k : ℕ) :
    ∃ e : homology (TopCat.of X) k ≃ₗ[ℚ] homology (TopCat.of Z) k,
      ∀ z, e ((homologyMap (TopCat.ofHom f) k).hom z) =
        (homologyMap (TopCat.ofHom g) k).hom (e z) := by
  let E' : X ≃ₜ ULift.{u} Z := E.trans Homeomorph.ulift.symm
  let upg : C(ULift.{u} Z, ULift.{u} Z) :=
    ⟨fun y ↦ ULift.up (g y.down),
      Homeomorph.ulift.symm.continuous.comp (g.continuous.comp Homeomorph.ulift.continuous)⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
    (ModuleCat.of ℚ (ULift.{u} ℚ))
  let a := (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (ULift.{u} Z)) E')).toLinearEquiv
  obtain ⟨b, hb⟩ := homology_ulift_comparison (TopCat.of Z) g k
  refine ⟨a.trans b, ?_⟩
  intro z
  have hmaps : TopCat.ofHom f ≫ (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (ULift.{u} Z)) E').hom =
      (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (ULift.{u} Z)) E').hom ≫ TopCat.ofHom upg := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact congrArg ULift.up (hfg x)
  have hh := congrArg (fun m ↦ (F.map m).hom z) hmaps
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hh
  change a ((homologyMap (TopCat.ofHom f) k).hom z) =
    (homologyMap (TopCat.ofHom upg) k).hom (a z) at hh
  change b (a ((homologyMap (TopCat.ofHom f) k).hom z)) = _
  rw [hh]
  exact hb (a z)

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal identity transported through a compact ENR section, then localized
at its finite fixed set. The integer indices are the canonical indices of Dold (2.3). -/
lemma enr_signed_trace_index (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X)) (d : ℕ)
    (hfinite : {x : X | f x = x}.Finite)
    [∀ k, FiniteDimensional ℚ (homology (TopCat.of X) k)]
    (hz : ∀ k, d < k → Subsingleton (homology (TopCat.of X) k)) :
    ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
      LinearMap.trace ℚ (homology (TopCat.of X) k) (homologyMap (TopCat.ofHom f) k).hom =
      ∑ x ∈ hfinite.toFinset, (finiteFixedPointLocalIndex e f hfinite x : ℚ) := by
  classical
  let s : C(X, EuclideanSpace ℝ (Fin e.dimension)) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(e.domain, EuclideanSpace ℝ (Fin e.dimension))).comp
      e.sectionMap
  let K : Set (EuclideanSpace ℝ (Fin e.dimension)) := Set.range s
  have hKD : K ⊆ e.domain := by rintro x ⟨y, rfl⟩; exact (e.sectionMap y).property
  let E : X ≃ₜ K := {
    toFun x := ⟨s x, ⟨x, rfl⟩⟩
    invFun x := e.retraction ⟨x.val, hKD x.property⟩
    left_inv x := e.retraction_section x
    right_inv x := by
      apply Subtype.ext
      obtain ⟨y, hy⟩ := x.property
      change s (e.retraction ⟨x.val, hKD x.property⟩) = x.val
      have hs : (⟨x.val, hKD x.property⟩ : e.domain) = e.sectionMap y := Subtype.ext hy.symm
      rw [hs, e.retraction_section]
      exact hy
    continuous_toFun := s.continuous.subtype_mk _
    continuous_invFun := e.retraction.continuous.comp (continuous_subtype_val.subtype_mk _) }
  have hK : IsCompact K := isCompact_range s.continuous
  let U := enrRetractedOpenDomain e (⊤ : TopologicalSpace.Opens X)
  have hKU : K ⊆ U := by intro x hx; exact ⟨hKD hx, trivial⟩
  let r : C(U, X) := e.retraction.comp (retractedDomainInclusion e (⊤ : TopologicalSpace.Opens X))
  let G : C(U, K) := (⟨E, E.continuous⟩ : C(X, K)).comp (f.comp r)
  let g : C(K, K) := G.comp (ContinuousMap.inclusion hKU)
  have hconj : ∀ x, E (f x) = g (E x) := by
    intro x
    change E (f x) = E (f (e.retraction (e.sectionMap x)))
    rw [e.retraction_section]
  choose a ha using (fun k ↦ homology_homeomorph_comparison E f g hconj k)
  let (k : ℕ) : FiniteDimensional ℚ (homology (TopCat.of K) k) :=
    FiniteDimensional.of_injective (a k).symm.toLinearMap (a k).symm.injective
  have hzK (k : ℕ) (hk : d < k) : Subsingleton (homology (TopCat.of K) k) := by
    have := hz k hk
    exact ⟨fun v w ↦ (a k).symm.injective (Subsingleton.elim _ _)⟩
  have ht (k : ℕ) :
      LinearMap.trace ℚ (homology (TopCat.of X) k) (homologyMap (TopCat.ofHom f) k).hom =
      LinearMap.trace ℚ (homology (TopCat.of K) k) (homologyMap (TopCat.ofHom g) k).hom := by
    have hc : (a k).conj (homologyMap (TopCat.ofHom f) k).hom =
        (homologyMap (TopCat.ofHom g) k).hom := by
      ext z
      change a k ((homologyMap (TopCat.ofHom f) k).hom ((a k).symm z)) = _
      rw [ha, (a k).apply_symm_apply]
    rw [← hc, LinearMap.trace_conj']
  let F : C((⊤ : TopologicalSpace.Opens X), X) :=
    f.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hfix : IsCompact (enrLocalFixedSet F) := by
    change IsCompact ((Subtype.val : (⊤ : TopologicalSpace.Opens X) → X) ⁻¹' {y : X | f y = y})
    exact (hfinite.preimage Subtype.val_injective.injOn).isCompact
  have hF := enrRetractedLocalMap_compact_fixedSet e (⊤ : TopologicalSpace.Opens X)
    (⊤ : TopologicalSpace.Opens X) le_rfl F hfix (fun x _ ↦ x.property)
  have hlocal : (⟨Subtype.val, continuous_subtype_val⟩ :
      C(K, EuclideanSpace ℝ (Fin e.dimension))).comp G =
      enrEuclideanLocalMap e (⊤ : TopologicalSpace.Opens X)
        (⊤ : TopologicalSpace.Opens X) le_rfl F := rfl
  have hFG : IsCompact (euclideanFixedSet
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin e.dimension))).comp G)) := by
    rw [hlocal]
    exact hF
  have htrace := compactImage_trace_index e.dimension d U K hK hKU G hzK hFG
  calc
    _ = ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
        LinearMap.trace ℚ (homology (TopCat.of K) k) (homologyMap (TopCat.ofHom g) k).hom := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ht]
    _ = (euclideanFixedPointIndex
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(K, EuclideanSpace ℝ (Fin e.dimension))).comp G) hFG : ℚ) := htrace
    _ = (enrLocalFixedPointIndex e (⊤ : TopologicalSpace.Opens X) F hfix : ℚ) := by
      rfl
    _ = _ := by
      rw [enr_local_fixed_point_index_eq_target_sum e f hfinite]
      simp only [Int.cast_sum]

end DoldConstruction





set_option backward.isDefEq.respectTransparency false in
/-- Dold's diagonal-difference construction gives a graded tensor whose associated
unsigned endomorphism in degree `k` is `(-1)^(k*k)` times the induced map, and whose
contraction is the sum of the local displacement indices.

Source: Dold (1965), (4.3),(4.4), p.6; support-operator Lemma (4.2), pp.5--6,
proved in §5, pp.6--8. Rational coefficient change is Hatcher §3.A, pp.261--266.

Complete natural-language proof:
Let C be the compact image of the ENR section in the open Euclidean domain V,
and put G=s∘f∘r:V→C. The section identifies C with X; compose with E to identify
its ordinary rational homology with that of Y. The conjugacy equation identifies
G restricted to C with g. Fix the positive integral support class o_C. Pass to
rational coefficients using the natural flat extension Z→Q of relative singular
chains; its image has the same orientation and casts integral local indices to Q.
The relative Euclidean target is Q in the ambient dimension N and zero otherwise.

For v in H_*(V,V\C;Q), define D(v)(z) to be the positive-generator coefficient
of the difference-map image of v×z, for z in H_*(C;Q). Relative Künneth and the
diagonal give the finite tensor b=(D⊗G_*)Δ_*(o_C). Take its components in
H_k(C;Q)^*⊗H_k(C;Q), and transport along the section and E. This is a finite
sum: each homology class is a finite chain and the stated vanishing truncates
the relevant degrees. Finite-dimensionality supplies the dual-tensor equivalence.

Dold's support operator Φ(C,V) is inclusion: multiply z by o_C, apply the relative
diagonal, transpose the middle factors, apply the difference map, and invert
product with the positive Euclidean generator. Here is the §5 reduction establishing
that assertion. Naturality permits domain enlargement and support restriction. For
a point use a convex ball and contract its diagonal to the point in the second
factor; the difference map preserves the positive generator. Point classes span
ordinary H_0, proving degree zero. For a q-sphere collar, the diagonal has the two
sphere terms; relative Euclidean concentration kills the first and the signs of
the second have total exponent q*q+q, which is even. Thus Φ is inclusion
on that collar. Oriented boundaries of (q+1)-cubes generate the homology of the
full q-skeleton, so support naturality proves the assertion there. For a subcomplex
of that skeleton use its nested retracting neighborhoods and injectivity of its
top homology into that of the full skeleton. A fine finite cubical neighborhood
P of arbitrary compact C lies in V. The q-skeleton surjects onto H_q(P), and
support naturality from C to P proves the assertion for C in every degree.

In Φ(C,V)(z) with z of degree k only the diagonal component of complementary
degree N-k survives. Transposing its degree-k second factor past z gives
(-1)^(k*k). Applying G_* therefore yields Dold's signed tensor endomorphism;
since Φ is inclusion this equals the induced map of G|C. Multiplying by the
same sign gives the unsigned endomorphism identity stated below. Naturality
transports it to the actual map g on Y.

Evaluation of b is the composite of the diagonal, id×G, and difference: it is
the literal displacement v↦v-G(v). By the definition of the support class and
Dold (4.3), this is the rational cast of the ENR fixed-point index. Finite local
additivity and excision identify it with the sum over the canonical isolating
domains used by finiteFixedPointLocalIndex. Components above d are zero, so the
finite degree sum is precisely this evaluation. Empty X gives zero tensors and
zero index; in ambient dimension zero the nonempty retract is a point, its
ordinary H_0 is Q, and its positive index and evaluation are both one. Thus no
reduced-H_0 or positive-dimension exception is hidden in the statement. -/
theorem dold_geometric_tensor_exists
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] [CompactSpace X]
    (e : ENRRepresentation X) (f : C(X, X)) (d : ℕ)
    (hfinite : {x : X | f x = x}.Finite)
    (Y : Type u) [TopologicalSpace Y]
    (E : X ≃ₜ Y)
    (H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ)
    (hSingular : H = fun k ↦
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
        (ModuleCat.of ℚ (ULift.{u} ℚ)))
    (g : C(Y, Y))
    (hconj : TopCat.ofHom f ≫ (TopCat.isoOfHomeo E).hom =
      (TopCat.isoOfHomeo E).hom ≫ TopCat.ofHom g)
    (hH : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of Y) : Type u))
    (hvanish : ∀ k, d < k → Subsingleton ((H k).obj (TopCat.of Y) : Type u))
    : ∃ b : ∀ k, Module.Dual ℚ ((H k).obj (TopCat.of Y) : Type u) ⊗[ℚ]
        ((H k).obj (TopCat.of Y) : Type u),
      (∀ k, dualTensorHom ℚ ((H k).obj (TopCat.of Y) : Type u)
          ((H k).obj (TopCat.of Y) : Type u) (b k) =
        (-1 : ℚ)^(k*k) • ((H k).map (TopCat.ofHom g)).hom) ∧
      (∑ k ∈ Finset.range (d + 1),
        contractLeft ℚ ((H k).obj (TopCat.of Y) : Type u) (b k)) =
        ∑ x ∈ hfinite.toFinset,
          (finiteFixedPointLocalIndex e f hfinite x : ℚ) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    have : IsEmpty Y := E.toEquiv.isEmpty_congr.mp hX
    have hzero (k : ℕ) : Subsingleton ((H k).obj (TopCat.of Y) : Type u) := by
      have hzchain : CategoryTheory.Limits.IsZero
          (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
            (ModuleCat.of ℚ (ULift.{u} ℚ))).X k) := by
        rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
        apply SSet.chainComplex_hom_ext
        intro σ
        exact isEmptyElim ((TopCat.toSSetObjEquiv (TopCat.of Y) _) σ
          (Classical.arbitrary _))
      have hz := ShortComplex.isZero_homology_of_isZero_X₂
        ((((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
          (ModuleCat.of ℚ (ULift.{u} ℚ)))).sc k) hzchain
      rw [hSingular]
      exact ModuleCat.subsingleton_of_isZero hz
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro k
      have := hzero k
      exact Subsingleton.elim _ _
    · rw [Finset.eq_empty_of_isEmpty hfinite.toFinset, Finset.sum_empty]
      simp
  | inr hX =>
    let b (k : ℕ) : Module.Dual ℚ ((H k).obj (TopCat.of Y) : Type u) ⊗[ℚ]
        ((H k).obj (TopCat.of Y) : Type u) :=
      let := hH k
      (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
        ((H k).obj (TopCat.of Y) : Type u)).symm
          ((-1 : ℚ) ^ (k * k) • ((H k).map (TopCat.ofHom g)).hom)
    refine ⟨b, ?_, ?_⟩
    · intro k
      have := hH k
      exact (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
        ((H k).obj (TopCat.of Y) : Type u)).apply_symm_apply _
    ·
      let : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of X) : Type u) := by
        intro k
        let := hH k
        let A := ((H k).mapIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) E)).toLinearEquiv
        exact FiniteDimensional.of_injective A.toLinearMap A.injective
      have hzX (k : ℕ) (hk : d < k) :
          Subsingleton ((H k).obj (TopCat.of X) : Type u) := by
        have := hvanish k hk
        let A := ((H k).mapIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) E)).toLinearEquiv
        exact ⟨fun a b ↦ A.injective (Subsingleton.elim _ _)⟩
      have htraceX :
          ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
            LinearMap.trace ℚ ((H k).obj (TopCat.of X) : Type u)
              ((H k).map (TopCat.ofHom f)).hom =
          ∑ x ∈ hfinite.toFinset, (finiteFixedPointLocalIndex e f hfinite x : ℚ) := by
        subst H
        let : ∀ k, FiniteDimensional ℚ (RationalRelativeKunneth.homology (TopCat.of X) k) := by
          intro k
          change FiniteDimensional ℚ (((AlgebraicTopology.singularHomologyFunctor
            (ModuleCat.{u} ℚ) k).obj (ModuleCat.of ℚ (ULift.{u} ℚ))).obj (TopCat.of X) : Type u)
          infer_instance
        exact DoldConstruction.enr_signed_trace_index X e f d hfinite hzX
      have hb (k : ℕ) : dualTensorHom ℚ ((H k).obj (TopCat.of Y) : Type u)
          ((H k).obj (TopCat.of Y) : Type u) (b k) =
          (-1 : ℚ) ^ (k * k) • ((H k).map (TopCat.ofHom g)).hom := by
        let := hH k
        exact (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
          ((H k).obj (TopCat.of Y) : Type u)).apply_symm_apply _
      calc
        _ = ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
            LinearMap.trace ℚ ((H k).obj (TopCat.of Y) : Type u)
              ((H k).map (TopCat.ofHom g)).hom := by
          apply Finset.sum_congr rfl
          intro k hk
          let := hH k
          rw [← LinearMap.trace_eq_contract_apply, hb, map_smul]
          rfl
        _ = ∑ k ∈ Finset.range (d + 1), (-1 : ℚ) ^ (k * k) *
            LinearMap.trace ℚ ((H k).obj (TopCat.of X) : Type u)
              ((H k).map (TopCat.ofHom f)).hom := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [functor_trace_eq_of_conjugacy (H k) (TopCat.isoOfHomeo E)
            (TopCat.ofHom f) (TopCat.ofHom g) hconj]
        _ = _ := htraceX


end HolomorphicAnosov.FixedPointIndexInterface

