import HolomorphicAnosov.Topology.SignedSingularCrossProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The prescribed rational singular shuffle chain map

Hatcher, Algebraic Topology, §3.B pp.277–278; Eilenberg–Mac Lane,
On the Groups H(Π,n), I (1953), §5 pp.63–67. The finite staircase, sign,
and affine simplex data are the existing integral-product definition. Here
we apply that same generator formula in Mathlib's native unnormalized rational
singular chain modules. All data are explicit; only the theorem laws are postponed.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle

universe u

/-- Mathlib's ordinary, unnormalized rational singular n-chain module.
The universe lift changes only the coefficient universe, not the rational ring. -/
abbrev Chain (X : TopCat.{u}) (n : ℕ) :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ (ULift.{u} ℚ))).X n

/-- The actual native singular n-simplex type; it includes degenerate simplices. -/
abbrev Simplex (X : TopCat.{u}) (n : ℕ) := SignedSingularCrossProduct.Simplex X n

/-- Inclusion of a singular simplex with its coefficient 1 in the native free module. -/
def generator (X : TopCat.{u}) {n : ℕ} (σ : Simplex X n) : Chain X n :=
  ((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ).hom (ULift.up 1)

/-- The exact prescribed signed staircase sum, now with rational coefficients.
The integral sign is mapped to ℚ, and every affine simplex is the original one. -/
def shuffleGenerator (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) : Chain (TopCat.of (X × Y)) (p + q) :=
  ∑ w ∈ SignedSingularCrossProduct.staircases p q, (SignedSingularCrossProduct.orientation w : ℚ) •
    generator (TopCat.of (X × Y)) (SignedSingularCrossProduct.productSimplex X Y w σ τ)

/-- Right free-module extension of the prescribed finite generator formula. -/
def rightLinear (X Y : TopCat.{u}) {p q : ℕ} (σ : Simplex X p) :
    Chain Y q →ₗ[ℚ] Chain (TopCat.of (X × Y)) (p + q) :=
  (Sigma.desc fun τ : Simplex Y q ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℚ ℕ _).symm (shuffleGenerator X Y σ τ)).comp
      (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap)).hom

/-- The actual rational bilinear operation, by the two native coproduct descents.
Its data are not chosen from any chain-map or acyclic-model existence theorem. -/
def shuffleBilinear (X Y : TopCat.{u}) (p q : ℕ) :
    Chain X p →ₗ[ℚ] Chain Y q →ₗ[ℚ] Chain (TopCat.of (X × Y)) (p + q) :=
  (Sigma.desc fun σ : Simplex X p ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℚ ℕ _).symm (rightLinear X Y σ)).comp
      (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap)).hom

/-- The same prescribed bilinear operation as a map from the tensor component. -/
def shuffle (X Y : TopCat.{u}) (p q : ℕ) :
    Chain X p ⊗[ℚ] Chain Y q →ₗ[ℚ] Chain (TopCat.of (X × Y)) (p + q) :=
  TensorProduct.lift (shuffleBilinear X Y p q)

/-- The native alternating-face differential; its degree-zero value is zero. -/
def boundary (X : TopCat.{u}) (n : ℕ) : Chain X n →ₗ[ℚ] Chain X (n - 1) :=
  (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ (ULift.{u} ℚ))).d n (n - 1)).hom

/-- Transport only a proved equality of degree indices; no chain data are changed. -/
def regrade (X : TopCat.{u}) {n m : ℕ} (h : n = m) : Chain X n →ₗ[ℚ] Chain X m := by
  subst m
  exact LinearMap.id

/-- First tensor-boundary term, omitted in degree zero, as required by the source. -/
def firstBoundaryTerm (X Y : TopCat.{u}) (p q : ℕ) (a : Chain X p) (b : Chain Y q) :
    Chain (TopCat.of (X × Y)) (p + q - 1) :=
  if hp : p = 0 then 0 else
    regrade (TopCat.of (X × Y)) (by omega : p - 1 + q = p + q - 1)
      (shuffleBilinear X Y (p - 1) q (boundary X p a) b)

/-- Second tensor-boundary term without its external Koszul coefficient.
The term is omitted when q=0; the theorem multiplies it by (-1)^p. -/
def secondBoundaryTerm (X Y : TopCat.{u}) (p q : ℕ) (a : Chain X p) (b : Chain Y q) :
    Chain (TopCat.of (X × Y)) (p + q - 1) :=
  if hq : q = 0 then 0 else
    regrade (TopCat.of (X × Y)) (by omega : p + (q - 1) = p + q - 1)
      (shuffleBilinear X Y p (q - 1) a (boundary Y q b))

/-- Native degreewise continuous postcomposition on ordinary rational singular chains. -/
def pushforward {X Y : TopCat.{u}} (f : C(X, Y)) (n : ℕ) : Chain X n →ₗ[ℚ] Chain Y n :=
  ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
    (ModuleCat.of ℚ (ULift.{u} ℚ))).f n).hom

/-- A degree-zero singular point, as an actual native singular simplex. -/
def pointSimplex (X : TopCat.{u}) (x : X) : Simplex X 0 :=
  (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)).symm (ContinuousMap.const _ x)

/-- Point insertion in the first coordinate, without a triangulation choice. -/
def insertLeft (X Y : TopCat.{u}) (x : X) {q : ℕ} (τ : Simplex Y q) :
    Simplex (TopCat.of (X × Y)) q :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋q⦌)).symm
    ((ContinuousMap.const _ x).prodMk (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ))

/-- Point insertion in the second coordinate. -/
def insertRight (X Y : TopCat.{u}) {p : ℕ} (σ : Simplex X p) (y : Y) :
    Simplex (TopCat.of (X × Y)) p :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋p⦌)).symm
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ).prodMk (ContinuousMap.const _ y))


end HolomorphicAnosov.SignedShuffle
