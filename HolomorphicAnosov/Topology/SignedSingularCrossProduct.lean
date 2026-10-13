import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# The signed singular simplex product

Hatcher, *Algebraic Topology*, Section 3.B, pp.277–278, defines the integral
singular-chain product by signed staircase triangulation. Bredon,
*Topology and Geometry*, IV Section 16, pp.220–222, gives the associated natural
chain product and relative descent.

All data here are explicit. The finite grid paths, their affine barycentric maps,
the number of squares below a path, and the finite signed sum are constructed.
The integral bilinear extension uses the universal property of the native
Mathlib singular chain modules, not a product supplied as a hypothesis.
Boundary, naturality, and relative-homology compatibility belong to the parent
`topo.bredon_integral_relative_cross_product_g6`; none is assumed in this definition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace HolomorphicAnosov.SignedSingularCrossProduct

universe u

/-- The native unnormalized integral singular chain module in degree `n`.
Source: Hatcher, p.108 and pp.277–278. -/
abbrev Chain (X : TopCat.{u}) (n : ℕ) :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n

/-- The actual native singular `n`-simplex type.
Source: Hatcher, p.108 and p.277. -/
abbrev Simplex (X : TopCat.{u}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)

/-- A grid-vertex sequence, before imposing the staircase conditions.
Source: Hatcher, pp.277–278. -/
abbrev GridPath (p q : ℕ) := Fin (p + q + 1) → Fin (p + 1) × Fin (q + 1)

/-- The finite set of rightward/upward unit grid paths from `(0,0)` to `(p,q)`.
The endpoint and step tests are explicit; no triangulation theorem is an input.
Source: Hatcher, p.277. -/
def staircases (p q : ℕ) : Finset (GridPath p q) :=
  Finset.univ.filter fun w ↦
    w 0 = (0, 0) ∧ w (Fin.last (p + q)) = (Fin.last p, Fin.last q) ∧
    ∀ i : Fin (p + q),
      ((w i.succ).1.val = (w i.castSucc).1.val + 1 ∧
        (w i.succ).2 = (w i.castSucc).2) ∨
      ((w i.succ).1 = (w i.castSucc).1 ∧
        (w i.succ).2.val = (w i.castSucc).2.val + 1)

/-- The number of pairs consisting of an upward step followed by a rightward step.
For a staircase this is the number of grid squares below it, hence its orientation
inversion count. Source: Hatcher, p.278. -/
def inversionCount {p q : ℕ} (w : GridPath p q) : ℕ :=
  (Finset.univ.filter fun ij : Fin (p + q) × Fin (p + q) ↦
    ij.1 < ij.2 ∧
    (w ij.1.succ).2.val = (w ij.1.castSucc).2.val + 1 ∧
    (w ij.2.succ).1.val = (w ij.2.castSucc).1.val + 1).card

/-- The orientation coefficient is the permutation sign `(-1)` to the inversion count.
Source: Hatcher, p.278. -/
def orientation {p q : ℕ} (w : GridPath p q) : ℤ :=
  (-1) ^ inversionCount w

/-- The affine barycentric map to the first simplex, sending vertex `k` to the
first coordinate of the `k`-th grid vertex. Source: Hatcher, pp.277–278.
`StdSimplex.map` sums barycentric weights over equal target vertices. -/
def firstSimplexMap {p q : ℕ} (w : GridPath p q) :
    C(Convexity.StdSimplex ℝ (Fin (p + q + 1)),
      Convexity.StdSimplex ℝ (Fin (p + 1))) :=
  ⟨Convexity.StdSimplex.map (fun k ↦ (w k).1),
    Convexity.StdSimplex.continuous_map ℝ (fun k ↦ (w k).1)⟩

/-- The second affine barycentric projection of the staircase simplex.
Source: Hatcher, pp.277–278. -/
def secondSimplexMap {p q : ℕ} (w : GridPath p q) :
    C(Convexity.StdSimplex ℝ (Fin (p + q + 1)),
      Convexity.StdSimplex ℝ (Fin (q + 1))) :=
  ⟨Convexity.StdSimplex.map (fun k ↦ (w k).2),
    Convexity.StdSimplex.continuous_map ℝ (fun k ↦ (w k).2)⟩

/-- The actual product singular simplex `(σ × τ) ∘ ℓ_w`, represented in the
native singular simplicial set. Source: Hatcher, pp.277–278. -/
def productSimplex (X Y : TopCat.{u}) {p q : ℕ} (w : GridPath p q)
    (σ : Simplex X p) (τ : Simplex Y q) : Simplex (TopCat.of (X × Y)) (p + q) :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋p + q⦌)).symm
    (((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ).comp (firstSimplexMap w)).prodMk
      ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ).comp (secondSimplexMap w)))

/-- The literal finite signed simplex sum, evaluated on unit integral coefficients.
No boundary or chain-map equation is assumed. Source: Hatcher, p.278. -/
def simplexProduct (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) : Chain (TopCat.of (X × Y)) (p + q) :=
  ∑ w ∈ staircases p q, orientation w •
    ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
      (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (productSimplex X Y w σ τ)).hom (ULift.up 1)

/-- Extend the generator product linearly in the right chain coefficient and simplex.
Source: Hatcher, pp.277–278, the extension on free singular chains. -/
def rightLinear (X Y : TopCat.{u}) {p q : ℕ} (σ : Simplex X p) :
    Chain Y q →ₗ[ℤ] Chain (TopCat.of (X × Y)) (p + q) :=
  (Sigma.desc fun τ : Simplex Y q ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℤ ℕ _).symm (simplexProduct X Y σ τ)).comp
      (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)).hom

/-- Hatcher's integral bilinear singular chain product.
Source: Hatcher, p.278; Bredon IV Section 16, pp.220–222.
Each coproduct summand is sent to the explicit signed staircase sum. The two
coproduct descents construct the bilinear extension on the native chain modules.
They use only Mathlib's proved universal properties; this definition contains
no admitted data or assumption of the product's boundary/naturality equations.
When a degree is zero, the same finite path formula has its unique constant
coordinate, and when a space is empty the corresponding coproduct has no generators. -/
def signedSingularCrossProduct (X Y : TopCat.{u}) (p q : ℕ) :
    Chain X p →ₗ[ℤ] Chain Y q →ₗ[ℤ] Chain (TopCat.of (X × Y)) (p + q) :=
  (Sigma.desc fun σ : Simplex X p ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℤ ℕ _).symm (rightLinear X Y σ)).comp
      (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)).hom

end HolomorphicAnosov.SignedSingularCrossProduct
