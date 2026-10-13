import HolomorphicAnosov.Topology.SignedSingularCrossProduct
import HolomorphicAnosov.Topology.Homology.SignedShuffleStaircaseRecursion
import HolomorphicAnosov.Topology.Homology.SignedShuffleInitialFace
import HolomorphicAnosov.Topology.Homology.NativeChainActionTransportExplicit

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.IntegralSignedCrossProduct
universe u
open HolomorphicAnosov.SignedSingularCrossProduct

abbrev Chain (X : TopCat.{u}) (n : ℕ) :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n

def generator (X : TopCat.{u}) {n : ℕ} (σ : Simplex X n) : Chain X n :=
  ((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ).hom (ULift.up 1)

def initialFaceSimplex (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m)
    (σ : Simplex X m) : Simplex X n :=
  (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌) σ).comp
      ⟨Convexity.StdSimplex.map (fun i : Fin (n + 1) ↦
        (⟨i.val + 1, by omega⟩ : Fin (m + 1))),
        Convexity.StdSimplex.continuous_map ℝ _⟩)

def regrade (X : TopCat.{u}) {n m : ℕ} (h : n = m) (a : Chain X n) : Chain X m := h ▸ a

def initialFaceChain (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m) :
    Chain X m →ₗ[ℤ] Chain X n :=
  (Sigma.desc fun σ : Simplex X m ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℤ ℕ _).symm
      (generator X (initialFaceSimplex X h σ))).comp
        (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)).hom

/-- The integral initial-face operator sends a native unit simplex generator
to the unit generator of the geometrically deleted simplex.

Source: EM1953 §2 p.56. The proof uses the coproduct injection/desc equation,
then the coefficient transport and the chain-module unit action. -/
theorem initialFaceChain_generator (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m)
    (σ : Simplex X m) :
    HolomorphicAnosov.IntegralSignedCrossProduct.initialFaceChain X h
        (HolomorphicAnosov.IntegralSignedCrossProduct.generator X σ) =
      HolomorphicAnosov.IntegralSignedCrossProduct.generator X
        (HolomorphicAnosov.IntegralSignedCrossProduct.initialFaceSimplex X h σ) := by
  unfold initialFaceChain generator
  let f : (s : Simplex X m) → ModuleCat.of ℤ (ULift.{u} ℤ) ⟶ Chain X n := fun s ↦
    ModuleCat.ofHom (((LinearMap.ringLmapEquivSelf ℤ ℕ _).symm
      (generator X (initialFaceSimplex X h s))).comp
        (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)
  have hd := CategoryTheory.Limits.Sigma.ι_comp_desc f σ
  have hdh := congrArg ModuleCat.Hom.hom hd
  rw [← ModuleCat.comp_apply]
  change (ModuleCat.Hom.hom (Sigma.ι (fun _ : Simplex X m => ModuleCat.of ℤ (ULift.{u} ℤ)) σ ≫ Sigma.desc f))
      (ULift.up (1 : ℤ)) = _
  rw [hdh]
  simp [f, generator]
  exact @native_integral_chain_one_smul_explicit X n (DistribMulAction.toMulAction) _

theorem initialFaceChain_prependHorizontal_generator (X Y : TopCat.{u}) {p q n : ℕ}
    (h : n + 1 = p + 1 + q) (w : GridPath p q) (σ : Simplex X (p + 1)) (τ : Simplex Y q) :
    initialFaceChain (TopCat.of (X × Y)) h
      (generator (TopCat.of (X × Y)) (productSimplex X Y (prependHorizontal w) σ τ)) =
    regrade (TopCat.of (X × Y)) (by omega : p + q = n)
      (generator (TopCat.of (X × Y))
        (productSimplex X Y w ((TopCat.toSSet.obj X).δ 0 σ) τ)) := by
  have hn : n = p + q := by omega
  subst n
  rw [initialFaceChain_generator]
  have hface : initialFaceSimplex (TopCat.of (X × Y)) (by omega)
        (productSimplex X Y (prependHorizontal w) σ τ) =
      productSimplex X Y w ((TopCat.toSSet.obj X).δ 0 σ) τ := by
    simpa only [initialFaceSimplex, HolomorphicAnosov.SignedShuffle.initialFaceSimplex] using
      HolomorphicAnosov.SignedShuffle.initialFace_prependHorizontal X Y w σ τ
  rw [hface]
  simp [regrade]

theorem initialFaceChain_prependVertical_generator (X Y : TopCat.{u}) {p q n : ℕ}
    (h : n + 1 = p + (q + 1)) (w : GridPath p q) (σ : Simplex X p) (τ : Simplex Y (q + 1)) :
    initialFaceChain (TopCat.of (X × Y)) h
      (generator (TopCat.of (X × Y)) (productSimplex X Y (prependVertical w) σ τ)) =
    regrade (TopCat.of (X × Y)) (by omega : p + q = n)
      (generator (TopCat.of (X × Y))
        (productSimplex X Y w σ ((TopCat.toSSet.obj Y).δ 0 τ))) := by
  have hn : n = p + q := by omega
  subst n
  rw [initialFaceChain_generator]
  have hface : initialFaceSimplex (TopCat.of (X × Y)) (by omega)
        (productSimplex X Y (prependVertical w) σ τ) =
      productSimplex X Y w σ ((TopCat.toSSet.obj Y).δ 0 τ) := by
    simpa only [initialFaceSimplex, HolomorphicAnosov.SignedShuffle.initialFaceSimplex] using
      HolomorphicAnosov.SignedShuffle.initialFace_prependVertical X Y w σ τ
  rw [hface]
  simp [regrade]

theorem regrade_sum {X : TopCat.{u}} {n m : ℕ} (h : n = m) {ι : Type*}
    (s : Finset ι) (f : ι → Chain X n) :
    regrade X h (∑ i ∈ s, f i) = ∑ i ∈ s, regrade X h (f i) := by
  subst m
  rfl

theorem regrade_smul {X : TopCat.{u}} {n m : ℕ} (h : n = m)
    (a : ℤ) (v : Chain X n) :
    regrade X h (a • v) = a • regrade X h v := by
  subst m
  rfl

/-- The initial face of the integral staircase product is the sum of the two
first input faces, with the signed vertical term. This is the integral form of
Eilenberg--Mac Lane (1953), equations (5.6), (5.7), (5.12), pp.65--66.
Proof: expand `simplexProduct` as its finite signed sum over monotone grid
staircases. Partition those paths by their first horizontal or vertical step.
The staircase recursion identifies the horizontal part with the product using the
first face of `σ`, and the vertical part with the product using the first face of
`τ`, carrying the sign `(-1)^(p+1)`. On each prefixed path, compose the affine
barycentric map with the map deleting the initial vertex. The horizontal
composition is the first face map on `σ` and leaves `τ` unchanged; the vertical
composition leaves `σ` unchanged and is the first face map on `τ`. The native
coproduct chain map sends each unit simplex generator to the corresponding
unit generator, so these affine equalities extend linearly over integer chains.
The finite sum is reduced exactly by the signed staircase recursion; no
interior-face cancellation remains because the operator is evaluated on each
generator and the two prefix families are identified term by term. -/
theorem integral_initialFace_simplexProduct (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    initialFaceChain (TopCat.of (X × Y)) (by omega : (p + q + 1) + 1 = (p + 1) + (q + 1))
      (simplexProduct X Y σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + (q + 1) = p + q + 1)
        (simplexProduct X Y ((TopCat.toSSet.obj X).δ 0 σ) τ) +
        (-1 : ℤ) ^ (p + 1) • regrade (TopCat.of (X × Y))
          (by omega : (p + 1) + q = p + q + 1)
          (simplexProduct X Y σ ((TopCat.toSSet.obj Y).δ 0 τ)) := by
  classical
  unfold simplexProduct
  simp only [map_sum, map_zsmul]
  rw [signed_staircase_sum_recursion]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    change orientation w • initialFaceChain (TopCat.of (X × Y)) _
      (generator (TopCat.of (X × Y)) (productSimplex X Y (prependHorizontal w) σ τ)) = _
    rw [initialFaceChain_prependHorizontal_generator]
    rfl
  · have hdeg : (p + 1) + q = p + q + 1 := by omega
    simp only [regrade_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    change orientation w • initialFaceChain (TopCat.of (X × Y)) _
      (generator (TopCat.of (X × Y)) (productSimplex X Y (prependVertical w) σ τ)) = _
    rw [initialFaceChain_prependVertical_generator]
    rw [← regrade_smul]
    rfl

end HolomorphicAnosov.IntegralSignedCrossProduct
