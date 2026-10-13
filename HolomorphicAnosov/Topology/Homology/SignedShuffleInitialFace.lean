import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Topology.Homology.SignedShuffleStaircaseRecursion

/-! For arbitrary topological spaces X,Y and positive-degree singular simplices σ,τ, the initial face of their prescribed rational signed shuffle is the shuffle of the initial face of σ with τ plus (−1) to the degree of σ times the shuffle of σ with the initial face of τ, with canonical degree transports. This is precisely EM1953 (5.12) in positive degrees.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 equation (3.10), p.60; §5 equations (5.6), p.65, and (5.12) with its proof, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u

/-- Delete the initial vertex, allowing a propositional degree equality.
Source: EM1953 §2, p.56, initial face operator. -/
def initialFaceSimplex (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m)
    (σ : Simplex X m) : Simplex X n :=
  (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌) σ).comp
      ⟨Convexity.StdSimplex.map (fun i : Fin (n + 1) ↦
        (⟨i.val + 1, by omega⟩ : Fin (m + 1))),
        Convexity.StdSimplex.continuous_map ℝ _⟩)

/-- At successive degrees the initial-face construction is the native simplicial face. -/
theorem initialFaceSimplex_eq_delta (X : TopCat.{u}) (n : ℕ) (σ : Simplex X (n + 1)) :
    initialFaceSimplex X rfl σ = (TopCat.toSSet.obj X).δ 0 σ := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (TopCat.toSSetObjEquiv X (Opposite.op ⦋n + 1⦌) σ)
    (Convexity.StdSimplex.map (fun i : Fin (n + 1) ↦ (⟨i.val + 1, _⟩ : Fin (n + 2))) z) =
    (TopCat.toSSetObjEquiv X (Opposite.op ⦋n + 1⦌) σ)
      (Convexity.StdSimplex.map (0 : Fin (n + 2)).succAbove z)
  congr 2

open SignedSingularCrossProduct

/-- Removing the first vertex of a horizontal prefix removes the first vertex
of the first input simplex. Source: EM1953 (5.6), p.65. -/
theorem initialFace_prependHorizontal (X Y : TopCat.{u}) {p q : ℕ}
    (w : GridPath p q) (σ : Simplex X (p + 1)) (τ : Simplex Y q) :
    initialFaceSimplex (TopCat.of (X × Y)) (by omega : p + q + 1 = p + 1 + q)
      (productSimplex X Y (prependHorizontal w) σ τ) =
      productSimplex X Y w ((TopCat.toSSet.obj X).δ 0 σ) τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋p + q⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (prependHorizontal w k).1)
        (Convexity.StdSimplex.map (fun k : Fin (p + q + 1) ↦
          (⟨k.val + 1, by omega⟩ : Fin (p + 1 + q + 1))) z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (prependHorizontal w k).2)
        (Convexity.StdSimplex.map (fun k : Fin (p + q + 1) ↦
          (⟨k.val + 1, by omega⟩ : Fin (p + 1 + q + 1))) z))) =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
      (Convexity.StdSimplex.map (0 : Fin (p + 2)).succAbove
        (Convexity.StdSimplex.map (fun k ↦ (w k).1) z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (w k).2) z))
  simp only [← Convexity.StdSimplex.map_comp]
  apply Prod.ext
  · congr 2
  · congr 2

/-- Removing the first vertex of a vertical prefix removes the first vertex
of the second input simplex. Source: EM1953 (5.6), p.65. -/
theorem initialFace_prependVertical (X Y : TopCat.{u}) {p q : ℕ}
    (w : GridPath p q) (σ : Simplex X p) (τ : Simplex Y (q + 1)) :
    initialFaceSimplex (TopCat.of (X × Y)) (by omega : p + q + 1 = p + (q + 1))
      (productSimplex X Y (prependVertical w) σ τ) =
      productSimplex X Y w σ ((TopCat.toSSet.obj Y).δ 0 τ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋p + q⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (prependVertical w k).1)
        (Convexity.StdSimplex.map (fun k : Fin (p + q + 1) ↦
          (⟨k.val + 1, by omega⟩ : Fin (p + (q + 1) + 1))) z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q + 1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (prependVertical w k).2)
        (Convexity.StdSimplex.map (fun k : Fin (p + q + 1) ↦
          (⟨k.val + 1, by omega⟩ : Fin (p + (q + 1) + 1))) z))) =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (w k).1) z),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q + 1⦌) τ)
      (Convexity.StdSimplex.map (0 : Fin (q + 2)).succAbove
        (Convexity.StdSimplex.map (fun k ↦ (w k).2) z)))
  simp only [← Convexity.StdSimplex.map_comp]
  apply Prod.ext
  · congr 2
  · congr 2

/-- Extend the initial face rational-linearly over the native singular generators.
Source: EM1953 §2 p.56, the FD-complex initial face. -/
def initialFaceChain (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m) :
    Chain X m →ₗ[ℚ] Chain X n :=
  (Sigma.desc fun σ : Simplex X m ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℚ ℕ _).symm
      (generator X (initialFaceSimplex X h σ))).comp
        (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap)).hom

/-- The linear initial face evaluates to the prescribed simplex face. -/
theorem initialFaceChain_generator (X : TopCat.{u}) {n m : ℕ} (h : n + 1 = m)
    (σ : Simplex X m) :
    initialFaceChain X h (generator X σ) = generator X (initialFaceSimplex X h σ) := by
  simp [initialFaceChain, generator, SSet.ιChainComplex]

/-- First-face compatibility with a horizontal prefix, including the degree transport. -/
theorem initialFace_prependHorizontal_generator (X Y : TopCat.{u}) {p q n : ℕ}
    (h : n + 1 = p + 1 + q)
    (w : GridPath p q) (σ : Simplex X (p + 1)) (τ : Simplex Y q) :
    generator (TopCat.of (X × Y))
      (initialFaceSimplex (TopCat.of (X × Y)) h
        (productSimplex X Y (prependHorizontal w) σ τ)) =
    regrade (TopCat.of (X × Y)) (by omega : p + q = n)
      (generator (TopCat.of (X × Y))
        (productSimplex X Y w ((TopCat.toSSet.obj X).δ 0 σ) τ)) := by
  have hn : n = p + q := by omega
  subst n
  rw [initialFace_prependHorizontal]
  rfl

/-- First-face compatibility with a vertical prefix, including the degree transport. -/
theorem initialFace_prependVertical_generator (X Y : TopCat.{u}) {p q n : ℕ}
    (h : n + 1 = p + (q + 1))
    (w : GridPath p q) (σ : Simplex X p) (τ : Simplex Y (q + 1)) :
    generator (TopCat.of (X × Y))
      (initialFaceSimplex (TopCat.of (X × Y)) h
        (productSimplex X Y (prependVertical w) σ τ)) =
    regrade (TopCat.of (X × Y)) (by omega : p + q = n)
      (generator (TopCat.of (X × Y))
        (productSimplex X Y w σ ((TopCat.toSSet.obj Y).δ 0 τ))) := by
  have hn : n = p + q := by omega
  subst n
  rw [initialFace_prependVertical]
  rfl

/-- For arbitrary topological spaces X,Y and positive-degree singular simplices σ,τ, the initial face of their prescribed rational signed shuffle is the shuffle of the initial face of σ with τ plus (−1) to the degree of σ times the shuffle of σ with the initial face of τ, with canonical degree transports. This is precisely EM1953 (5.12) in positive degrees.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 equation (3.10), p.60; §5 equations (5.6), p.65, and (5.12) with its proof, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Define the initial face by the affine map taking each vertex i to i+1 and extend rational-linearly over the native generators. Its simplex formula is exactly the native simplicial face of index zero. For a horizontal prefix, composition with this affine map returns the old path with its first coordinate increased by one, hence the product of the first input face with the second input. The vertical-prefix formula is the corresponding identity in the second coordinate. Both follow by composition of the affine vertex maps.

Expand the shuffle as its finite signed generator sum and move the linear initial-face operator inside. Apply the proved signed first-step recursion. The horizontal-prefix sum becomes the shuffle of the first input face. The vertical-prefix sum becomes the shuffle of the second input face and retains the factor (−1) to the first degree. Linearity carries the canonical degree transports through both sums. -/
theorem initialFace_shuffleGenerator (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    initialFaceChain (TopCat.of (X × Y))
      (by omega : (p + 1 + (q + 1) - 1) + 1 = p + 1 + (q + 1))
      (shuffleGenerator X Y σ τ) =
    regrade (TopCat.of (X × Y)) (by omega : p + (q + 1) = p + 1 + (q + 1) - 1)
      (shuffleGenerator X Y ((TopCat.toSSet.obj X).δ 0 σ) τ) +
    (-1 : ℚ) ^ (p + 1) •
      regrade (TopCat.of (X × Y)) (by omega : p + 1 + q = p + 1 + (q + 1) - 1)
        (shuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ 0 τ)) := by
  classical
  unfold shuffleGenerator
  simp only [map_sum, map_zsmul, initialFaceChain_generator, Int.cast_smul_eq_zsmul]
  rw [signed_staircase_sum_recursion]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    rw [initialFace_prependHorizontal_generator]
  · have hsign : (-1 : ℚ) ^ (p + 1) = (((-1 : ℤ) ^ (p + 1) : ℤ) : ℚ) := by
      simp
    rw [hsign, Int.cast_smul_eq_zsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    rw [initialFace_prependVertical_generator]
end HolomorphicAnosov.SignedShuffle
