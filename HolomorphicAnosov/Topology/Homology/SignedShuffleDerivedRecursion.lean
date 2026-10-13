import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Topology.Homology.SignedShuffleStaircaseRecursion
import HolomorphicAnosov.Topology.Homology.SignedShuffleOperatorModel

/-! For arbitrary positive-degree singular inputs, their prescribed rational signed shuffle is the derived shuffle of the first input with the initial degeneracy of the second, plus (−1) to the first input degree times the derived shuffle of the initial degeneracy of the first input with the second. The derived shuffle primes both paired affine vertex maps. This is precisely EM1953 equation (5.7), with native simplicial initial degeneracies and canonical degree transports.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 priming definition (3.3), p.59; §5 derived shuffle (5.3′), pp.64–65, and exact recursion (5.7), p.65. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
open SignedSingularCrossProduct OperatorModel

/-- The derived shuffle, obtained by priming every paired affine operator.
Source: EM1953 equation (5.3′), p.65. -/
def derivedShuffleGenerator (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    Chain (TopCat.of (X × Y)) (p + q + 1) :=
  ∑ w ∈ staircases p q, (orientation w : ℚ) •
    generator (TopCat.of (X × Y))
      (evaluate X Y (prime (fun i ↦ (w i).1, fun i ↦ (w i).2)) σ τ)

/-- The horizontal-prefix simplex is the derived operator with D₀ in the second input. -/
theorem horizontal_prefix_derived (X Y : TopCat.{u}) {p q : ℕ}
    (w : GridPath p q) (σ : Simplex X (p + 1)) (τ : Simplex Y q) :
    generator (TopCat.of (X × Y)) (productSimplex X Y (prependHorizontal w) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + q + 1 = p + 1 + q)
        (generator (TopCat.of (X × Y))
          (evaluate X Y (prime (fun i ↦ (w i).1, fun i ↦ (w i).2))
            σ ((TopCat.toSSet.obj Y).σ 0 τ))) := by
  rw [evaluate_degeneracyZero_right, regrade_evaluate_generator]
  apply congrArg (generator (TopCat.of (X × Y)))
  rw [← evaluate_gridPath]
  congr 1
  apply Prod.ext <;> funext k
  · by_cases hk : k.val = 0
    · have he : k = 0 := Fin.ext hk
      subst k
      simp [prependHorizontal, prime]
    · have hc : Fin.cast (by omega : p + 1 + q + 1 = p + q + 1 + 1) k =
          (⟨k.val - 1, by omega⟩ : Fin (p + q + 1)).succ := by
        apply Fin.ext
        dsimp
        omega
      simp [prependHorizontal, prime, hk, hc]
  · by_cases hk : k.val = 0
    · have he : k = 0 := Fin.ext hk
      subst k
      simp [prependHorizontal, prime]
    · have hc : Fin.cast (by omega : p + 1 + q + 1 = p + q + 1 + 1) k =
          (⟨k.val - 1, by omega⟩ : Fin (p + q + 1)).succ := by
        apply Fin.ext
        dsimp
        omega
      simp [prependHorizontal, prime, hk, hc]

/-- The vertical-prefix simplex is the derived operator with D₀ in the first input. -/
theorem vertical_prefix_derived (X Y : TopCat.{u}) {p q : ℕ}
    (w : GridPath p q) (σ : Simplex X p) (τ : Simplex Y (q + 1)) :
    generator (TopCat.of (X × Y)) (productSimplex X Y (prependVertical w) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + q + 1 = p + (q + 1))
        (generator (TopCat.of (X × Y))
          (evaluate X Y (prime (fun i ↦ (w i).1, fun i ↦ (w i).2))
            ((TopCat.toSSet.obj X).σ 0 σ) τ)) := by
  rw [evaluate_degeneracyZero_left, regrade_evaluate_generator]
  apply congrArg (generator (TopCat.of (X × Y)))
  rw [← evaluate_gridPath]
  congr 1
  apply Prod.ext <;> funext k <;> cases k using Fin.cases <;>
    simp [prependVertical, prime, Function.comp_def]

/-- For arbitrary positive-degree singular inputs, their prescribed rational signed shuffle is the derived shuffle of the first input with the initial degeneracy of the second, plus (−1) to the first input degree times the derived shuffle of the initial degeneracy of the first input with the second. The derived shuffle primes both paired affine vertex maps. This is precisely EM1953 equation (5.7), with native simplicial initial degeneracies and canonical degree transports.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 priming definition (3.3), p.59; §5 derived shuffle (5.3′), pp.64–65, and exact recursion (5.7), p.65. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Use the proved disjoint first-step recursion of the signed staircase sum. In the horizontal class its coefficient is unchanged, while the vertical class gains (−1) to the horizontal degree.

At the simplex level, priming both coordinate maps and then applying the initial degeneracy to the second input removes the added shift in its coordinate while retaining the first-coordinate shift. The resulting affine vertex maps are exactly the horizontal prefix. Applying the initial degeneracy to the first input instead gives the vertical prefix. These are checked at the initial vertex and every successor vertex.

Apply these two simplex identities termwise to the two sums and move canonical degree transport through the finite sums and scalar multiples. This yields exactly the stated rational native generator recursion. -/
theorem shuffleGenerator_derived_recursion (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    shuffleGenerator X Y σ τ =
      regrade (TopCat.of (X × Y))
        (by omega : p + (q + 1) + 1 = p + 1 + (q + 1))
        (derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).σ 0 τ)) +
      (-1 : ℚ) ^ (p + 1) •
        regrade (TopCat.of (X × Y))
          (by omega : p + 1 + q + 1 = p + 1 + (q + 1))
          (derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) τ) := by
  classical
  unfold shuffleGenerator derivedShuffleGenerator
  simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  rw [signed_staircase_sum_recursion]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    rw [horizontal_prefix_derived]
  · have hsign : (-1 : ℚ) ^ (p + 1) = (((-1 : ℤ) ^ (p + 1) : ℤ) : ℚ) := by simp
    rw [hsign, Int.cast_smul_eq_zsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    rw [vertical_prefix_derived]
end HolomorphicAnosov.SignedShuffle
