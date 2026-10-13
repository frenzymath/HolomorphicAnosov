import HolomorphicAnosov.Topology.Homology.IntegralChainRationalization
import HolomorphicAnosov.Topology.Homology.IntegralRelativeProductData
import HolomorphicAnosov.Topology.SignedCrossProductUnitGenerators
import HolomorphicAnosov.Topology.Homology.SignedShuffleOneOneBoundary
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRows
import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryAssembly
import HolomorphicAnosov.Topology.AdjacentStaircaseFace
import HolomorphicAnosov.Topology.SignedSimplexProductBoundaryExpansion
import HolomorphicAnosov.Topology.Homology.SignedIntegralInitialFace
import HolomorphicAnosov.Topology.Homology.SingularChainSignedExpansion
import HolomorphicAnosov.Topology.SingularChainUnitGeneratorExt

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The two interior (diagonal) faces in the 1×1 staircase product are the same integral unit chain.  -/
theorem integral_cross_product_positive_boundary_generator_middle_cancel
    (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
      (R := singularIntegralCoefficients)
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ (1 : Fin 3)
        (SignedSingularCrossProduct.productSimplex X Y
          SignedShuffle.OneOne.horizontalFirst σ τ))).hom (ULift.up 1) =
    ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
      (R := singularIntegralCoefficients)
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ (1 : Fin 3)
        (SignedSingularCrossProduct.productSimplex X Y
          SignedShuffle.OneOne.verticalFirst σ τ))).hom (ULift.up 1) := by
  rw [SignedShuffle.OneOne.middle_faces_agree]



/-- The two adjacent staircase terms cancel in the alternating boundary sum. -/
theorem integral_cross_product_positive_boundary_generator_adjacent_cancel
    {p q : ℕ} {X Y : TopCat.{u}}
    (w : SignedSingularCrossProduct.GridPath p q)
    (hw : w ∈ SignedSingularCrossProduct.staircases p q)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (SignedSingularCrossProduct.orientation
      (SignedSingularCrossProduct.prependHorizontal
        (SignedSingularCrossProduct.prependVertical w))) •
      ((-1 : ℤ) ^ (1 : ℕ)) •
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients))
        ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
          (1 : Fin ((p + 1) + (q + 1) + 1))
          (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
            (SignedSingularCrossProduct.prependHorizontal
              (SignedSingularCrossProduct.prependVertical w)) σ τ))).hom (ULift.up 1) +
    (SignedSingularCrossProduct.orientation
      (SignedSingularCrossProduct.prependVertical
        (SignedSingularCrossProduct.prependHorizontal w))) •
      ((-1 : ℤ) ^ (1 : ℕ)) •
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients))
        ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
          (1 : Fin ((p + 1) + (q + 1) + 1))
          (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
            (SignedSingularCrossProduct.prependVertical
              (SignedSingularCrossProduct.prependHorizontal w)) σ τ))).hom (ULift.up 1) = 0 := by
  have hmem : SignedSingularCrossProduct.prependHorizontal
      (SignedSingularCrossProduct.prependVertical w) ∈
      SignedSingularCrossProduct.staircases (p + 1) (q + 1) := by
    apply SignedSingularCrossProduct.prependHorizontal_mem
    apply SignedSingularCrossProduct.prependVertical_mem
    exact hw
  have hor : SignedSingularCrossProduct.orientation
      (SignedSingularCrossProduct.prependHorizontal
        (SignedSingularCrossProduct.prependVertical w)) =
      - SignedSingularCrossProduct.orientation
      (SignedSingularCrossProduct.prependVertical
        (SignedSingularCrossProduct.prependHorizontal w)) := by
    exact adjacent_prefix_orientation_neg hw
  have hface := adjacent_prefix_middle_face_agree w σ τ
  rw [hor, hface]
  simp

/-- The complete interior middle-face family cancels after summing all lower staircases. -/
theorem integral_cross_product_positive_boundary_generator_middle_family_cancel
    {p q : ℕ} {X Y : TopCat.{u}}
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    ∑ w ∈ SignedSingularCrossProduct.staircases p q,
      ((SignedSingularCrossProduct.orientation
        (SignedSingularCrossProduct.prependHorizontal
          (SignedSingularCrossProduct.prependVertical w))) •
        ((-1 : ℤ) ^ (1 : ℕ)) •
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
          (R := singularIntegralCoefficients))
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
            (1 : Fin ((p + 1) + (q + 1) + 1))
            (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
              (SignedSingularCrossProduct.prependHorizontal
                (SignedSingularCrossProduct.prependVertical w)) σ τ))).hom (ULift.up 1) +
      (SignedSingularCrossProduct.orientation
        (SignedSingularCrossProduct.prependVertical
          (SignedSingularCrossProduct.prependHorizontal w))) •
        ((-1 : ℤ) ^ (1 : ℕ)) •
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
          (R := singularIntegralCoefficients))
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
            (1 : Fin ((p + 1) + (q + 1) + 1))
            (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
              (SignedSingularCrossProduct.prependVertical
                (SignedSingularCrossProduct.prependHorizontal w)) σ τ))).hom (ULift.up 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  exact integral_cross_product_positive_boundary_generator_adjacent_cancel w hw σ τ

/-- Canonical target-degree transport of the complete interior middle-face cancellation.  -/
theorem integral_cross_product_positive_boundary_generator_middle_family_cancel_cast
    {p q : ℕ} {X Y : TopCat.{u}}
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    castChain (TopCat.of (X × Y)) (n := p + q + 1)
      (by omega : ((p + 1) + (q + 1)) - 1 = p + q + 1)
      (    ∑ w ∈ SignedSingularCrossProduct.staircases p q,
      ((SignedSingularCrossProduct.orientation
        (SignedSingularCrossProduct.prependHorizontal
          (SignedSingularCrossProduct.prependVertical w))) •
        ((-1 : ℤ) ^ (1 : ℕ)) •
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
          (R := singularIntegralCoefficients))
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
            (1 : Fin ((p + 1) + (q + 1) + 1))
            (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
              (SignedSingularCrossProduct.prependHorizontal
                (SignedSingularCrossProduct.prependVertical w)) σ τ))).hom (ULift.up 1) +
      (SignedSingularCrossProduct.orientation
        (SignedSingularCrossProduct.prependVertical
          (SignedSingularCrossProduct.prependHorizontal w))) •
        ((-1 : ℤ) ^ (1 : ℕ)) •
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
          (R := singularIntegralCoefficients))
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ
            (1 : Fin ((p + 1) + (q + 1) + 1))
            (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
              (SignedSingularCrossProduct.prependVertical
                (SignedSingularCrossProduct.prependHorizontal w)) σ τ))).hom (ULift.up 1))) = 0 := by
  have h := integral_cross_product_positive_boundary_generator_middle_family_cancel σ τ
  rw [h]
  have cast_zero {m n : ℕ} (he : m = n) :
      castChain (TopCat.of (X × Y)) he (0 : Chain (TopCat.of (X × Y)) m) =
        (0 : Chain (TopCat.of (X × Y)) n) := by
    subst n
    rfl
  exact cast_zero _



/-- The initial face of an integral staircase product transports to the two exterior staircase families, with the vertical family carrying the Koszul sign.  -/
theorem integral_cross_product_positive_boundary_generator_initial_face_transport
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    HolomorphicAnosov.IntegralSignedCrossProduct.initialFaceChain
        (TopCat.of (X × Y)) (by omega : (p + q + 1) + 1 = (p + 1) + (q + 1))
      (simplexProduct X Y σ τ) =
      HolomorphicAnosov.IntegralSignedCrossProduct.regrade
        (TopCat.of (X × Y)) (by omega : p + (q + 1) = p + q + 1)
        (simplexProduct X Y ((TopCat.toSSet.obj X).δ 0 σ) τ) +
      (-1 : ℤ) ^ (p + 1) • HolomorphicAnosov.IntegralSignedCrossProduct.regrade
        (TopCat.of (X × Y)) (by omega : (p + 1) + q = p + q + 1)
        (simplexProduct X Y σ ((TopCat.toSSet.obj Y).δ 0 τ)) := by
  exact HolomorphicAnosov.IntegralSignedCrossProduct.integral_initialFace_simplexProduct
    X Y p q σ τ

/-- The integral simplex product splits by the first staircase step. -/
theorem integral_cross_product_positive_boundary_generator_simplex_recursion
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    simplexProduct X Y σ τ =
      (∑ w ∈ SignedSingularCrossProduct.staircases p (q + 1),
        SignedSingularCrossProduct.orientation w •
          ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
            (R := singularIntegralCoefficients)
            (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
              (SignedSingularCrossProduct.prependHorizontal w) σ τ)).hom (ULift.up 1)) +
      (-1 : ℤ) ^ (p + 1) •
        (∑ w ∈ SignedSingularCrossProduct.staircases (p + 1) q,
          SignedSingularCrossProduct.orientation w •
            ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
              (R := singularIntegralCoefficients)
              (SignedSingularCrossProduct.productSimplex (p := p + 1) (q := q + 1) X Y
                (SignedSingularCrossProduct.prependVertical w) σ τ)).hom (ULift.up 1)) := by
  unfold simplexProduct
  apply SignedSingularCrossProduct.signed_staircase_sum_recursion

/-- The native integral differential expands the staircase product into the alternating sum of all staircase simplex faces. -/
theorem integral_cross_product_positive_boundary_generator_face_expansion
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
      ((p + 1) + (q + 1)) (((p + 1) + (q + 1)) - 1)
      (simplexProduct X Y σ τ)) =
      ∑ w ∈ SignedSingularCrossProduct.staircases (p + 1) (q + 1),
        SignedSingularCrossProduct.orientation w •
          ∑ i : Fin ((p + 1) + (q + 1) + 1), (-1 : ℤ)^i.val •
            ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
              (R := singularIntegralCoefficients)
              ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i
                (SignedSingularCrossProduct.productSimplex
                  (p := p + 1) (q := q + 1) X Y w σ τ))).hom (ULift.up 1) := by
  exact SignedSingularCrossProduct.simplexProduct_boundary_expansion σ τ

/-- The differential respects the first-step decomposition of the integral simplex product. -/
theorem integral_cross_product_positive_boundary_generator_differential_recursion
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
      ((p + 1) + (q + 1)) (p + q + 1)
      (simplexProduct X Y σ τ)) =
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
        ((p + 1) + (q + 1)) (p + q + 1)
        (∑ w ∈ SignedSingularCrossProduct.staircases p (q + 1),
          SignedSingularCrossProduct.orientation w •
            ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
              (R := singularIntegralCoefficients)
              (SignedSingularCrossProduct.productSimplex
                (p := p + 1) (q := q + 1) X Y
                (SignedSingularCrossProduct.prependHorizontal w) σ τ)).hom (ULift.up 1))) +
      (-1 : ℤ) ^ (p + 1) •
      (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
        ((p + 1) + (q + 1)) (p + q + 1)
        (∑ w ∈ SignedSingularCrossProduct.staircases (p + 1) q,
          SignedSingularCrossProduct.orientation w •
            ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
              (R := singularIntegralCoefficients)
              (SignedSingularCrossProduct.productSimplex
                (p := p + 1) (q := q + 1) X Y
                (SignedSingularCrossProduct.prependVertical w) σ τ)).hom (ULift.up 1))) := by
  let d := (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
      ((p + 1) + (q + 1)) (p + q + 1)).hom
  have h := congrArg d
    (integral_cross_product_positive_boundary_generator_simplex_recursion X Y p q σ τ)
  dsimp [d] at h
  simpa only [map_add, map_zsmul] using h

/-- The positive-face sum for an initially degenerated second input is the finite exterior-family recurrence used by the integral staircase induction.  -/
theorem integral_cross_product_positive_boundary_generator_right_positive_face_degeneracy
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (∑ i : Fin (q + 2), (-1 : ℤ)^i.val •
      simplexProduct (p := p + 1) (q := q + 1) X Y σ
        ((TopCat.toSSet.obj Y).δ i.succ ((TopCat.toSSet.obj Y).σ 0 τ))) =
      simplexProduct (p := p + 1) (q := q + 1) X Y σ τ -
        ∑ i : Fin (q + 1), (-1 : ℤ)^i.val •
          simplexProduct (p := p + 1) (q := q + 1) X Y σ
            ((TopCat.toSSet.obj Y).σ 0 ((TopCat.toSSet.obj Y).δ i.succ τ)) := by
  exact HolomorphicAnosov.SignedShuffle.positiveFace_degeneracy_sum Y q τ
    (M := Chain (TopCat.of (X × Y)) ((p + 1) + (q + 1)))
    (fun υ : Simplex Y (q + 1) ↦ simplexProduct (p := p + 1) (q := q + 1) X Y σ υ)

/-- The positive-face sum for an initially degenerated first input is the symmetric finite exterior-family recurrence used by the integral staircase induction. -/
theorem integral_cross_product_positive_boundary_generator_left_positive_face_degeneracy
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
      simplexProduct (p := p + 1) (q := q + 1) X Y
        ((TopCat.toSSet.obj X).δ i.succ ((TopCat.toSSet.obj X).σ 0 σ)) τ) =
      simplexProduct (p := p + 1) (q := q + 1) X Y σ τ -
        ∑ i : Fin (p + 1), (-1 : ℤ)^i.val •
          simplexProduct (p := p + 1) (q := q + 1) X Y
            ((TopCat.toSSet.obj X).σ 0 ((TopCat.toSSet.obj X).δ i.succ σ)) τ := by
  exact HolomorphicAnosov.SignedShuffle.positiveFace_degeneracy_sum X p σ
    (M := Chain (TopCat.of (X × Y)) ((p + 1) + (q + 1)))
    (fun υ : Simplex X (p + 1) ↦ simplexProduct (p := p + 1) (q := q + 1) X Y υ τ)

/-- Integer bilinearity distributes the first boundary's explicit `a + -b` decomposition through the singular cross product.  -/
theorem integral_cross_product_positive_boundary_generator_left_add_neg
    (X Y : TopCat.{u}) (a b : Chain X 0) (c : Chain Y 1) :
    signedSingularCrossProduct X Y 0 1 (a + -b) c =
      signedSingularCrossProduct X Y 0 1 a c +
        -(signedSingularCrossProduct X Y 0 1 b c) := by
  rw [map_add, map_neg]
  rfl

/-- Integer bilinearity distributes the second boundary's explicit `a + -b` decomposition through the singular cross product.  -/
theorem integral_cross_product_positive_boundary_generator_right_add_neg
    (X Y : TopCat.{u}) (a : Chain X 1) (b c : Chain Y 0) :
    signedSingularCrossProduct X Y 1 0 a (b + -c) =
      signedSingularCrossProduct X Y 1 0 a b +
        -(signedSingularCrossProduct X Y 1 0 a c) := by
  rw [map_add, map_neg]

/-- The integral `(0,q)` unit row is the simplex product with the unique staircase, equivalently insertion of the first factor's point.  -/
theorem integral_cross_product_positive_boundary_generator_left_row
    (X Y : TopCat.{u}) (x : Simplex X 0) (τ : Simplex Y 1) :
    simplexProduct X Y x τ =
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients)
        (SignedShuffle.insertLeft X Y
          ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) x)
            (Convexity.StdSimplex.single (0 : Fin 1))) τ)).hom (ULift.up 1) := by
  classical
  have hpaths : SignedSingularCrossProduct.staircases 0 1 =
      {fun k ↦ (0, Fin.cast (by omega) k)} := by decide
  rw [simplexProduct, hpaths, Finset.sum_singleton]
  have hor : SignedSingularCrossProduct.orientation
      (fun k : Fin (0 + 1 + 1) ↦ (0, Fin.cast (by omega) k)) = 1 := by
    decide
  rw [hor]
  simp only [one_smul]
  have hprod : SignedSingularCrossProduct.productSimplex X Y
      (fun k ↦ (0, Fin.cast (by omega) k)) x τ =
      SignedShuffle.insertLeft X Y
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) x)
          (Convexity.StdSimplex.single (0 : Fin 1))) τ := by
    apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
    simp [SignedSingularCrossProduct.productSimplex, SignedShuffle.insertLeft]
    apply ContinuousMap.ext
    intro z
    apply Prod.ext
    · simp [firstSimplexMap]
    · simp [secondSimplexMap]
      have hid : (fun k : Fin 2 ↦ k) = id := rfl
      rw [hid, Convexity.StdSimplex.map_id]
  rw [hprod]

/-- The integral `(p,0)` unit row is the simplex product with the unique staircase, equivalently insertion of the second factor's point.  -/
theorem integral_cross_product_positive_boundary_generator_right_row
    (X Y : TopCat.{u}) (σ : Simplex X 1) (y : Simplex Y 0) :
    simplexProduct X Y σ y =
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients)
        (SignedShuffle.insertRight X Y σ
          ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) y)
            (Convexity.StdSimplex.single (0 : Fin 1))))).hom (ULift.up 1) := by
  classical
  have hpaths : SignedSingularCrossProduct.staircases 1 0 =
      {fun k ↦ (k, (0 : Fin 1))} := by decide
  rw [simplexProduct, hpaths, Finset.sum_singleton]
  have hor : SignedSingularCrossProduct.orientation
      (fun k : Fin (1 + 0 + 1) ↦ (k, 0)) = 1 := by
    decide
  rw [hor]
  simp only [one_smul]
  have hprod : SignedSingularCrossProduct.productSimplex X Y
      (fun k ↦ (k, 0)) σ y =
      SignedShuffle.insertRight X Y σ
        ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) y)
          (Convexity.StdSimplex.single (0 : Fin 1))) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
    simp [SignedSingularCrossProduct.productSimplex, SignedShuffle.insertRight]
    apply ContinuousMap.ext
    intro z
    apply Prod.ext
    · simp [firstSimplexMap]
      have hid : (fun k : Fin 2 ↦ k) = id := rfl
      rw [hid, Convexity.StdSimplex.map_id]
    · simp [secondSimplexMap]
  rw [hprod]

/-- Point insertion identifies the integral zero-degree left row on arbitrary chains with postcomposition by the coordinate insertion map. -/
theorem integral_cross_product_positive_boundary_generator_left_row_chain
    (X Y : TopCat.{u}) (x : X) (q : ℕ) (b : Chain Y q) :
    castChain (TopCat.of (X × Y)) (Nat.zero_add q)
      (signedSingularCrossProduct X Y 0 q (pointChain X x) b) =
      chainMap (insertLeft X Y x) q b := by
  classical
  let regrade (Z : TopCat.{u}) {n m : ℕ} (h : n = m) :
      Chain Z n →ₗ[ℤ] Chain Z m := by
    subst m
    exact LinearMap.id
  have hregrade (Z : TopCat.{u}) {n m : ℕ} (h : n = m) (a : Chain Z n) :
      regrade Z h a = castChain Z h a := by
    subst m
    rfl
  let L := (regrade (TopCat.of (X × Y)) (Nat.zero_add q)).comp
    (signedSingularCrossProduct X Y 0 q (pointChain X x))
  have h : ModuleCat.ofHom L = chainMap (insertLeft X Y x) q := by
    apply singularChain_unitGenerator_ext Y q
    intro τ
    change regrade (TopCat.of (X × Y)) (Nat.zero_add q)
      (signedSingularCrossProduct X Y 0 q
        (((TopCat.toSSet.obj X).ιChainComplex
          (R := singularIntegralCoefficients) (SignedShuffle.pointSimplex X x))
            (ULift.up 1))
        (((TopCat.toSSet.obj Y).ιChainComplex
          (R := singularIntegralCoefficients) τ) (ULift.up 1))) = _
    rw [hregrade, signedSingularCrossProduct_unit_generators]
    simp only [simplexProduct, SignedShuffle.staircases_zero_left, Finset.sum_singleton]
    simp only [orientation, inversionCount]
    simp
    have transport (Z : TopCat.{u}) (n m : ℕ) (h : n = m)
        (σ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Z)) :
        castChain Z h
          (((TopCat.toSSet.obj Z).ιChainComplex
            (R := singularIntegralCoefficients)
            ((TopCat.toSSetObjEquiv Z (Opposite.op ⦋n⦌)).symm
              (σ.comp ⟨Convexity.StdSimplex.map
                (Fin.cast (congrArg (· + 1) h)),
                Convexity.StdSimplex.continuous_map ℝ _⟩))) (ULift.up 1)) =
          ((TopCat.toSSet.obj Z).ιChainComplex
            (R := singularIntegralCoefficients)
            ((TopCat.toSSetObjEquiv Z (Opposite.op ⦋m⦌)).symm σ))
            (ULift.up 1) := by
      subst m
      have hid : (⟨Convexity.StdSimplex.map
          (Fin.cast (congrArg (· + 1) (rfl : n = n))),
          Convexity.StdSimplex.continuous_map ℝ _⟩ :
          C(Convexity.StdSimplex ℝ (Fin (n + 1)), _)) =
          ContinuousMap.id _ := by
        apply ContinuousMap.ext
        intro z
        change Convexity.StdSimplex.map id z = z
        exact Convexity.StdSimplex.map_id z
      rw [hid, ContinuousMap.comp_id]
      rfl
    have hmap := congrArg (fun k : singularIntegralCoefficients ⟶
        Chain (TopCat.of (X × Y)) q ↦ k (ULift.up 1))
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj Y)
        (TopCat.toSSet.obj (TopCat.of (X × Y)))
        (TopCat.toSSet.map (insertLeft X Y x)) singularIntegralCoefficients τ)
    apply Eq.trans ?_ hmap.symm
    unfold productSimplex SignedShuffle.pointSimplex
    simp only [Equiv.apply_symm_apply]
    convert transport (TopCat.of (X × Y)) (0 + q) q (Nat.zero_add q)
      ((ContinuousMap.const _ x).prodMk
        (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)) using 1
    · congr 2
    · rfl
  exact (hregrade _ _ _).symm.trans (congrArg (fun k ↦ k b) h)

/-- The symmetric point-insertion identity for the integral right row.  -/
theorem integral_cross_product_positive_boundary_generator_right_row_chain
    (X Y : TopCat.{u}) (y : Y) (p : ℕ) (a : Chain X p) :
    signedSingularCrossProduct X Y p 0 a (pointChain Y y) =
      chainMap (insertRight X Y y) p a := by
  classical
  let left : Chain X p →+ Chain (TopCat.of (X × Y)) p :=
    { toFun := fun a ↦ signedSingularCrossProduct X Y p 0 a (pointChain Y y)
      map_zero' := by simp
      map_add' := by intro a b; simp }
  let leftLinear : Chain X p →ₗ[ℤ] Chain (TopCat.of (X × Y)) p :=
    { toFun := left
      map_add' := left.map_add
      map_smul' := by
        intro r a
        change left ((Chain X p).isModule.smul r a) =
          (Chain (TopCat.of (X × Y)) p).isModule.smul r (left a)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact left.map_zsmul r a }
  have h : ModuleCat.ofHom leftLinear = chainMap (insertRight X Y y) p := by
    apply singularChain_unitGenerator_ext X p
    intro σ
    change signedSingularCrossProduct X Y p 0
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := singularIntegralCoefficients) σ) (ULift.up 1))
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := singularIntegralCoefficients) (SignedShuffle.pointSimplex Y y))
          (ULift.up 1)) = _
    rw [signedSingularCrossProduct_unit_generators]
    have hprod : SignedSingularCrossProduct.productSimplex X Y
        (fun k : Fin (p + 1) ↦ (k, (0 : Fin 1))) σ
        (SignedShuffle.pointSimplex Y y) =
        (TopCat.toSSet.map (insertRight X Y y)).app (Opposite.op ⦋p⦌) σ := by
      apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y))
        (Opposite.op ⦋p⦌)).injective
      apply ContinuousMap.ext
      intro z
      change ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
        (Convexity.StdSimplex.map id z), y) =
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ) z, y)
      rw [Convexity.StdSimplex.map_id]
    have hmap := congrArg (fun k : singularIntegralCoefficients ⟶
        Chain (TopCat.of (X × Y)) p ↦ k (ULift.up 1))
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X)
        (TopCat.toSSet.obj (TopCat.of (X × Y)))
        (TopCat.toSSet.map (insertRight X Y y)) singularIntegralCoefficients σ)
    simp only [simplexProduct, SignedShuffle.right_staircase,
      Finset.sum_singleton, orientation, inversionCount]
    simp only [hprod]
    convert hmap.symm using 1
    simp
  exact congrArg (fun k ↦ k a) h

/- The (1,1) square is the base case of the source's staircase induction. -/
theorem integral_cross_product_positive_boundary_generator_base
    (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d 2 1 (simplexProduct X Y σ τ)) =
      castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 0 1
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj X).ιChainComplex
              (R := singularIntegralCoefficients) σ) (ULift.up 1)))
          (((TopCat.toSSet.obj Y).ιChainComplex
            (R := singularIntegralCoefficients) τ) (ULift.up 1))) +
      (-1 : ℤ) • castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 1 0
          (((TopCat.toSSet.obj X).ιChainComplex
            (R := singularIntegralCoefficients) σ) (ULift.up 1))
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj Y).ιChainComplex
          (R := singularIntegralCoefficients) τ) (ULift.up 1)))) := by
  have hex := simplexProduct_boundary_expansion (X := X) (Y := Y)
    (p := 1) (q := 0) σ τ
  simp only [Nat.reduceAdd] at hex
  rw [hex, SignedShuffle.OneOne.staircases_one_one]
  have hne : SignedShuffle.OneOne.horizontalFirst ≠ SignedShuffle.OneOne.verticalFirst := by decide
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    pow_zero, one_smul]
  norm_num only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero,
    Fin.val_one, Fin.val_two, add_zero, pow_one, neg_one_sq, one_smul,
    neg_one_smul]
  have hmem : SignedShuffle.OneOne.horizontalFirst ∉
      ({SignedShuffle.OneOne.verticalFirst} : Finset _) := by simpa using hne
  rw [Finset.sum_insert hmem, Finset.sum_singleton]
  rw [SignedShuffle.OneOne.horizontalFirst_face_zero,
    SignedShuffle.OneOne.horizontalFirst_face_two,
    SignedShuffle.OneOne.verticalFirst_face_zero,
    SignedShuffle.OneOne.verticalFirst_face_two,
    SignedShuffle.OneOne.middle_faces_agree,
    SignedShuffle.OneOne.orientation_horizontalFirst,
    SignedShuffle.OneOne.orientation_verticalFirst]
  have hdσ :
      (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d 1 0).hom
        (((TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients) σ).hom
          (ULift.up 1)) =
      (((TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients)
        ((TopCat.toSSet.obj X).δ (0 : Fin 2) σ)).hom (ULift.up 1)) -
      (((TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients)
        ((TopCat.toSSet.obj X).δ (1 : Fin 2) σ)).hom (ULift.up 1)) := by
    have hδ := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ)))
      (SSet.ιChainComplex_d (TopCat.toSSet.obj X)
        (R := singularIntegralCoefficients) σ)
    simpa [SSet.ιChainComplex, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      sub_eq_add_neg] using hδ
  have hdτ :
      (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d 1 0).hom
        (((TopCat.toSSet.obj Y).ιChainComplex (R := singularIntegralCoefficients) τ).hom
          (ULift.up 1)) =
      (((TopCat.toSSet.obj Y).ιChainComplex (R := singularIntegralCoefficients)
        ((TopCat.toSSet.obj Y).δ (0 : Fin 2) τ)).hom (ULift.up 1)) -
      (((TopCat.toSSet.obj Y).ιChainComplex (R := singularIntegralCoefficients)
        ((TopCat.toSSet.obj Y).δ (1 : Fin 2) τ)).hom (ULift.up 1)) := by
    have hδ := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ)))
      (SSet.ιChainComplex_d (TopCat.toSSet.obj Y)
        (R := singularIntegralCoefficients) τ)
    simpa [SSet.ιChainComplex, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      sub_eq_add_neg] using hδ
  rw [hdσ, hdτ]
  simp only [sub_eq_add_neg]
  rw [integral_cross_product_positive_boundary_generator_left_add_neg,
    integral_cross_product_positive_boundary_generator_right_add_neg]
  rw [signedSingularCrossProduct_unit_generators,
    signedSingularCrossProduct_unit_generators,
    signedSingularCrossProduct_unit_generators,
    signedSingularCrossProduct_unit_generators]
  have hleft (υ : Simplex X 0) :
      simplexProduct X Y υ τ =
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients)
        (SignedShuffle.insertLeft X Y
          ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) υ)
            (Convexity.StdSimplex.single (0 : Fin 1))) τ)).hom (ULift.up 1) :=
    integral_cross_product_positive_boundary_generator_left_row X Y υ τ
  have hright (υ : Simplex Y 0) :
      simplexProduct X Y σ υ =
      ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
        (R := singularIntegralCoefficients)
        (SignedShuffle.insertRight X Y σ
          ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) υ)
            (Convexity.StdSimplex.single (0 : Fin 1))))).hom (ULift.up 1) :=
    integral_cross_product_positive_boundary_generator_right_row X Y σ υ
  rw [hleft, hleft, hright, hright]
  simp only [one_smul]
  simp only [castChain]
  try simp only [smul_add, neg_smul, one_smul]
  simp; abel_nf

/- The generator-level face cancellation is kept in this module because it is
the mathematical child of the held positive-boundary claim. -/

/-- Base case of the exterior-face induction, at input degrees `(1,1)`.  -/
theorem integral_cross_product_positive_boundary_generator_exterior_face_induction_base
    (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d 2 1 (simplexProduct X Y σ τ)) =
      castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 0 1
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj X).ιChainComplex
              (R := singularIntegralCoefficients) σ) (ULift.up 1)))
          (((TopCat.toSSet.obj Y).ιChainComplex
            (R := singularIntegralCoefficients) τ) (ULift.up 1))) +
      (-1 : ℤ) • castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 1 0
          (((TopCat.toSSet.obj X).ιChainComplex
            (R := singularIntegralCoefficients) σ) (ULift.up 1))
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj Y).ιChainComplex
              (R := singularIntegralCoefficients) τ) (ULift.up 1)))) := by
  exact integral_cross_product_positive_boundary_generator_base X Y σ τ

/-- Canonical target-degree transport of the alternating staircase face expansion.  -/
theorem integral_cross_product_positive_boundary_generator_exterior_face_expansion
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega : ((p + 1) + (q + 1)) - 1 = p + q + 1)
        ((((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d ((p + 1) + (q + 1))
            (((p + 1) + (q + 1)) - 1) (simplexProduct X Y σ τ))) =
      castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega : ((p + 1) + (q + 1)) - 1 = p + q + 1)
        (∑ w ∈ SignedSingularCrossProduct.staircases (p + 1) (q + 1),
          SignedSingularCrossProduct.orientation w •
            ∑ i : Fin ((p + 1) + (q + 1) + 1), (-1 : ℤ)^i.val •
              ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
                (R := singularIntegralCoefficients)
                ((TopCat.toSSet.obj (TopCat.of (X × Y))).δ i
                  (SignedSingularCrossProduct.productSimplex
                    (p := p + 1) (q := q + 1) X Y w σ τ))).hom (ULift.up 1)) := by
  exact congrArg (castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega : ((p + 1) + (q + 1)) - 1 = p + q + 1))
    (integral_cross_product_positive_boundary_generator_face_expansion X Y p q σ τ)

/-- The all-degree exterior-face induction remaining in the integral staircase boundary proof.  -/
theorem integral_cross_product_positive_boundary_generator_exterior_face_induction
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d ((p + 1) + (q + 1))
            (((p + 1) + (q + 1)) - 1)
            (simplexProduct X Y σ τ)) =
      castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y p (q + 1)
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d
            (p + 1) p
            (((TopCat.toSSet.obj X).ιChainComplex
              (R := singularIntegralCoefficients) σ) (ULift.up 1)))
          (((TopCat.toSSet.obj Y).ιChainComplex
            (R := singularIntegralCoefficients) τ) (ULift.up 1))) +
      (-1 : ℤ) ^ (p + 1) • castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y (p + 1) q
          (((TopCat.toSSet.obj X).ιChainComplex
            (R := singularIntegralCoefficients) σ) (ULift.up 1))
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
            (q + 1) q
            (((TopCat.toSSet.obj Y).ιChainComplex
              (R := singularIntegralCoefficients) τ) (ULift.up 1)))) := by
  apply IntegralChainRationalization.toRational_injective
  rw [map_add, map_zsmul, IntegralChainRationalization.toRational_cast,
    IntegralChainRationalization.toRational_cast, IntegralChainRationalization.toRational_cast,
    IntegralChainRationalization.toRational_boundary _ _ (by omega),
    IntegralChainRationalization.toRational_simplexProduct,
    IntegralChainRationalization.toRational_crossProduct,
    IntegralChainRationalization.toRational_crossProduct,
    IntegralChainRationalization.toRational_generator,
    IntegralChainRationalization.toRational_generator]
  rw [IntegralChainRationalization.toRational_boundary_succ X p,
    IntegralChainRationalization.toRational_boundary_succ Y q,
    IntegralChainRationalization.toRational_generator,
    IntegralChainRationalization.toRational_generator]
  have h := SignedShuffle.shuffle_positive_boundary_generator X Y (p + 1) (q + 1)
    (by omega) (by omega) σ τ
  rw [h]
  simp only [SignedShuffle.firstBoundaryTerm, SignedShuffle.secondBoundaryTerm,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
    map_add, map_smul, SignedShuffle.regrade_trans,
    ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simp [SignedShuffle.regrade]

/-- The signed integral staircase product satisfies the Leibniz boundary law on a pair of positive-degree unit simplex generators. -/
theorem integral_cross_product_positive_boundary_generator
    (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d ((p + 1) + (q + 1))
            (((p + 1) + (q + 1)) - 1)
            (simplexProduct X Y σ τ)) =
      castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y p (q + 1)
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d
            (p + 1) p
            (((TopCat.toSSet.obj X).ιChainComplex
              (R := singularIntegralCoefficients) σ) (ULift.up 1)))
          (((TopCat.toSSet.obj Y).ιChainComplex
            (R := singularIntegralCoefficients) τ) (ULift.up 1))) +
      (-1 : ℤ) ^ (p + 1) • castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y (p + 1) q
          (((TopCat.toSSet.obj X).ιChainComplex
            (R := singularIntegralCoefficients) σ) (ULift.up 1))
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
            (q + 1) q
            (((TopCat.toSSet.obj Y).ιChainComplex
              (R := singularIntegralCoefficients) τ) (ULift.up 1)))) := by
  exact integral_cross_product_positive_boundary_generator_exterior_face_induction X Y p q σ τ

/-- Base case for the staircase induction: the signed product of two one-simplices has the boundary formula obtained by cancelling the common diagonal face of the two square triangles.  -/
theorem integral_cross_product_positive_boundary_generator_one_one
    (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d 2 1 (simplexProduct X Y σ τ)) =
      castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 0 1
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj X).ιChainComplex
              (R := singularIntegralCoefficients) σ) (ULift.up 1)))
          (((TopCat.toSSet.obj Y).ιChainComplex
            (R := singularIntegralCoefficients) τ) (ULift.up 1))) +
      (-1 : ℤ) • castChain (TopCat.of (X × Y)) (n := 1) (by omega)
        (signedSingularCrossProduct X Y 1 0
          (((TopCat.toSSet.obj X).ιChainComplex
            (R := singularIntegralCoefficients) σ) (ULift.up 1))
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d 1 0
            (((TopCat.toSSet.obj Y).ιChainComplex
              (R := singularIntegralCoefficients) τ) (ULift.up 1)))) := by
  exact integral_cross_product_positive_boundary_generator_base X Y σ τ

set_option maxHeartbeats 800000 in
/-- For integral singular chains of positive degrees p+1 and q+1, the boundary of their signed staircase product is the product of the first boundary plus (-1)^(p+1) times the product of the second boundary. -/
theorem integral_cross_product_positive_boundary :
    (∀ (X Y : TopCat.{u}) (p q : ℕ) (a : Chain X (p + 1)) (b : Chain Y (q + 1)),
      castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex
          singularIntegralCoefficients).d ((p + 1) + (q + 1))
            (((p + 1) + (q + 1)) - 1)
            (signedSingularCrossProduct X Y (p + 1) (q + 1) a b)) =
      castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y p (q + 1)
          (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p a) b) +
      (-1 : ℤ) ^ (p + 1) • castChain (TopCat.of (X × Y)) (n := p + q + 1) (by omega)
        (signedSingularCrossProduct X Y (p + 1) q a
          (((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d (q + 1) q b))) := by
  intro X Y p q a b
  classical
  have cast_sum {m n : ℕ} (h : m = n) {ι : Type} (s : Finset ι)
      (f : ι → Chain (TopCat.of (X × Y)) m) :
      castChain (TopCat.of (X × Y)) h (∑ i ∈ s, f i) =
        ∑ i ∈ s, castChain (TopCat.of (X × Y)) h (f i) := by
    subst n
    rfl
  have cast_smul {m n : ℕ} (h : m = n) (r : ℤ)
      (c : Chain (TopCat.of (X × Y)) m) :
      castChain (TopCat.of (X × Y)) h (r • c) =
        r • castChain (TopCat.of (X × Y)) h c := by
    subst n
    rfl
  obtain ⟨ma, σ, ε, _, ha⟩ := integralSingularChainSignedExpansion X (p + 1) a
  obtain ⟨mb, τ, η, _, hb⟩ := integralSingularChainSignedExpansion Y (q + 1) b
  have eval_zsmul {m n : ℕ} (f : Chain Y m →ₗ[ℤ] Chain (TopCat.of (X × Y)) n)
      (r : ℤ) (c : Chain Y m) : (r • f) c = r • f c :=
    map_zsmul (LinearMap.applyₗ (R := ℤ) c) r f
  rw [ha, hb]
  simp only [map_sum, map_zsmul, eval_zsmul, LinearMap.sum_apply,
    cast_sum, cast_smul, ← Finset.sum_zsmul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hgen := integral_cross_product_positive_boundary_generator X Y p q (σ i) (τ j)
  rw [← signedSingularCrossProduct_unit_generators] at hgen
  have hscaled := congrArg (fun c ↦ η j • ε i • c) hgen
  simpa only [zsmul_add, zsmul_comm _ ((-1 : ℤ) ^ (p + 1)) (η j),
    zsmul_comm _ ((-1 : ℤ) ^ (p + 1)) (ε i)] using hscaled

end HolomorphicAnosov.Topology

