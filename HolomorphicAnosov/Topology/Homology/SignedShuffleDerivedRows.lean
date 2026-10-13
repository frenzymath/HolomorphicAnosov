import HolomorphicAnosov.Topology.Homology.SignedShuffleBasic
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRecursion
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedBoundaryTransport
import HolomorphicAnosov.Topology.Homology.SignedShuffleData

/-! The derived shuffle has a single primed affine operator when one underlying shuffle index is zero. Its positive boundary acts only on the other input; the missing degree-one derived boundary term is omitted. If the degree-one input is the initial degeneracy of a point, the derived shuffle equals the ordinary zero-degree shuffle row.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 endpoint recursion (5.7a), p.65, exceptional derived row (5.13), p.66, and the explicit instruction that the opposite edge is treated similarly, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
open SignedSingularCrossProduct OperatorModel

/-- The primed left-row operator has first coordinate zero initially and one
thereafter, and is the identity in the second coordinate. -/
def derivedLeftSimplex (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 1)) : Simplex (TopCat.of (X × Y)) (q + 1) :=
  evaluate X Y (Fin.cases 0 (fun _ ↦ (1 : Fin 2)), id) σ τ

/-- A positive face of the derived left-row operator is the corresponding
positive face of the second input. Source: EM1953 (5.13), p.67. -/
theorem derivedLeftSimplex_positive_face (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 2)) (i : Fin (q + 2)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ i.succ (derivedLeftSimplex X Y (q + 1) σ τ) =
      derivedLeftSimplex X Y q σ ((TopCat.toSSet.obj Y).δ i.succ τ) := by
  unfold derivedLeftSimplex
  rw [evaluate_face, evaluate_face_right]
  congr 1
  apply Prod.ext
  · funext k
    cases k using Fin.cases <;> simp
  · rfl

/-- The positive differential on the derived left row acts only on the second
input. This is the first-degree exceptional row of EM1953 (5.13). -/
theorem derivedLeftSimplex_positive_boundary (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 2)) :
    positiveBoundary (TopCat.of (X × Y)) (q + 1)
      (generator (TopCat.of (X × Y)) (derivedLeftSimplex X Y (q + 1) σ τ)) =
      ∑ i : Fin (q + 2), (-1 : ℤ)^i.val •
        generator (TopCat.of (X × Y))
          (derivedLeftSimplex X Y q σ ((TopCat.toSSet.obj Y).δ i.succ τ)) := by
  rw [positiveBoundary_generator]
  simp only [derivedLeftSimplex_positive_face]

/-- There is exactly one staircase in a grid with no horizontal steps. -/
theorem staircases_zero_left (q : ℕ) : staircases 0 q =
    {fun k ↦ (0, Fin.cast (by omega) k)} := by
  classical
  ext w
  simp only [staircases, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hlast, hstep⟩
    funext k
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply Fin.ext
      induction k using Fin.induction with
      | zero => simpa using congrArg (fun z : Fin 1 × Fin (q + 1) ↦ z.2.val) h0
      | succ i ih =>
        rcases hstep i with ⟨hs, _⟩ | ⟨_, hs⟩
        · have h₁ := (w i.succ).1.isLt
          have h₂ := (w i.castSucc).1.isLt
          omega
        · simpa [ih] using hs
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · apply Prod.ext <;> apply Fin.ext <;> simp
    · intro i
      exact Or.inr ⟨rfl, rfl⟩

/-- The exact derived shuffle in the zero first-index row is its single primed
left-row operator, including the degree transport. -/
theorem derivedShuffleGenerator_left_row (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 1)) :
    regrade (TopCat.of (X × Y)) (by omega : 0 + q + 1 = q + 1)
      (derivedShuffleGenerator X Y σ τ) =
      generator (TopCat.of (X × Y)) (derivedLeftSimplex X Y q σ τ) := by
  classical
  unfold derivedShuffleGenerator
  rw [staircases_zero_left]
  simp only [Finset.sum_singleton]
  have hs : orientation (fun k : Fin (0 + q + 1) ↦ (0, Fin.cast (by omega) k)) = 1 := by
    simp [orientation, inversionCount]
  rw [hs]
  simp only [Int.cast_one, one_smul]
  rw [regrade_evaluate_generator]
  apply congrArg (generator (TopCat.of (X × Y)))
  unfold derivedLeftSimplex
  congr 1
  apply Prod.ext <;> funext k <;> cases k using Fin.cases <;> simp [prime]

/-- The derived shuffle has a single primed affine operator when one underlying shuffle index is zero. Its positive boundary acts only on the other input; the missing degree-one derived boundary term is omitted. If the degree-one input is the initial degeneracy of a point, the derived shuffle equals the ordinary zero-degree shuffle row.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 endpoint recursion (5.7a), p.65, exceptional derived row (5.13), p.66, and the explicit instruction that the opposite edge is treated similarly, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: The staircase with no horizontal steps is unique, since every increment must be vertical. Its sign is one. Its primed affine map has first vertex coordinate zero then one, and second coordinate the identity. The right row is symmetric. This identifies each actual finite derived shuffle sum with the corresponding single generator.

Deleting a positive-index vertex of the primed row deletes the same vertex of the nonconstant input. Apply the native positive-boundary formula to that generator and sum its signs. This proves precisely (5.13), and the symmetric right-row identity, without asserting that the degree-one positive boundary is zero.

Composing the two-valued row coordinate with the initial degeneracy of a point makes it constant. The unique-staircase formula for the ordinary zero-degree row is therefore the same affine generator, including the equality transport of its output degree. This is the endpoint formula (5.7a) used in the edge induction. -/
theorem derivedShuffleGenerator_left_row_boundary (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 2)) :
    positiveBoundary (TopCat.of (X × Y)) (q + 1)
      (regrade (TopCat.of (X × Y)) (by omega : 0 + (q + 1) + 1 = q + 2)
        (derivedShuffleGenerator X Y σ τ)) =
      ∑ i : Fin (q + 2), (-1 : ℤ)^i.val •
        regrade (TopCat.of (X × Y)) (by omega : 0 + q + 1 = q + 1)
          (derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ i.succ τ)) := by
  simp only [derivedShuffleGenerator_left_row, derivedLeftSimplex_positive_boundary]

/-- The primed right-row operator is the identity in its first coordinate and
zero initially, then one, in its second coordinate. -/
def derivedRightSimplex (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y 1) : Simplex (TopCat.of (X × Y)) (p + 1) :=
  evaluate X Y (id, Fin.cases 0 (fun _ ↦ (1 : Fin 2))) σ τ

/-- Positive faces of a derived right-row operator act on the first input only. -/
theorem derivedRightSimplex_positive_face (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y 1) (i : Fin (p + 2)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ i.succ
      (derivedRightSimplex X Y (p + 1) σ τ) =
      derivedRightSimplex X Y p ((TopCat.toSSet.obj X).δ i.succ σ) τ := by
  unfold derivedRightSimplex
  rw [evaluate_face, evaluate_face_left]
  congr 1
  apply Prod.ext
  · rfl
  · funext k
    cases k using Fin.cases <;> simp

/-- The positive differential on the derived right row acts on its first input. -/
theorem derivedRightSimplex_positive_boundary (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y 1) :
    positiveBoundary (TopCat.of (X × Y)) (p + 1)
      (generator (TopCat.of (X × Y)) (derivedRightSimplex X Y (p + 1) σ τ)) =
      ∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
        generator (TopCat.of (X × Y))
          (derivedRightSimplex X Y p ((TopCat.toSSet.obj X).δ i.succ σ) τ) := by
  rw [positiveBoundary_generator]
  simp only [derivedRightSimplex_positive_face]

/-- The exact derived shuffle in the zero second-index row is its single primed
right-row operator. -/
theorem derivedShuffleGenerator_right_row (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y 1) :
    derivedShuffleGenerator X Y σ τ =
      generator (TopCat.of (X × Y)) (derivedRightSimplex X Y p σ τ) := by
  classical
  unfold derivedShuffleGenerator
  rw [right_staircase]
  simp only [Finset.sum_singleton]
  have hs : orientation (fun k : Fin (p + 0 + 1) ↦ (k, 0)) = 1 := by
    simp [orientation, inversionCount]
  rw [hs]
  simp only [Int.cast_one, one_smul]
  apply congrArg (generator (TopCat.of (X × Y)))
  unfold derivedRightSimplex
  congr 1
  apply Prod.ext <;> funext k <;> cases k using Fin.cases <;> simp [prime]

/-- The symmetric degree-one exceptional derived boundary row, with the second
input term omitted because its derived boundary is zero. Source: EM1953 Theorem5.2. -/
theorem derivedShuffleGenerator_right_row_boundary (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y 1) :
    positiveBoundary (TopCat.of (X × Y)) (p + 1)
      (derivedShuffleGenerator X Y (p := p + 1) (q := 0) σ τ) =
      ∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
        derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ := by
  simp only [derivedShuffleGenerator_right_row, derivedRightSimplex_positive_boundary]

/-- Degree transport is injective because it transports along an equality. -/
theorem regrade_injective (X : TopCat.{u}) {n m : ℕ} (h : n = m) :
    Function.Injective (regrade X h) := by
  subst m
  exact Function.injective_id

/-- With an initially degenerated point in its first input, the derived shuffle
is exactly the ordinary zero-degree left row. Source: EM1953 (5.7a). -/
theorem derivedShuffle_degenerate_point_left (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 0) (τ : Simplex Y (q + 1)) :
    derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) τ =
      shuffleGenerator X Y σ τ := by
  classical
  apply regrade_injective (TopCat.of (X × Y)) (by omega : 0 + (q + 1) = q + 1)
  rw [derivedShuffleGenerator_left_row]
  unfold shuffleGenerator
  rw [staircases_zero_left]
  simp only [Finset.sum_singleton]
  have hs : orientation (fun k : Fin (0 + (q + 1) + 1) ↦
      (0, Fin.cast (by omega) k)) = 1 := by simp [orientation, inversionCount]
  rw [hs]
  simp only [Int.cast_one, one_smul]
  rw [← evaluate_gridPath, regrade_evaluate_generator]
  apply congrArg (generator (TopCat.of (X × Y)))
  unfold derivedLeftSimplex
  rw [evaluate_degeneracyZero_left]
  congr 1
  apply Prod.ext
  · funext i
    apply Fin.ext
    omega
  · funext i
    rfl

/-- With an initially degenerated point in its second input, the derived shuffle
is exactly the ordinary zero-degree right row. Source: EM1953 (5.7a). -/
theorem derivedShuffle_degenerate_point_right (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y 0) :
    derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).σ 0 τ) =
      shuffleGenerator X Y σ τ := by
  classical
  rw [derivedShuffleGenerator_right_row]
  unfold shuffleGenerator
  rw [right_staircase]
  simp only [Finset.sum_singleton]
  have hs : orientation (fun k : Fin (p + 1 + 0 + 1) ↦ (k, 0)) = 1 := by
    simp [orientation, inversionCount]
  rw [hs]
  simp only [Int.cast_one, one_smul]
  rw [← evaluate_gridPath]
  apply congrArg (generator (TopCat.of (X × Y)))
  unfold derivedRightSimplex
  rw [evaluate_degeneracyZero_right]
  congr 1
  apply Prod.ext
  · rfl
  · funext i
    apply Fin.ext
    omega
end HolomorphicAnosov.SignedShuffle
