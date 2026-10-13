import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryGenerator
import HolomorphicAnosov.Topology.Homology.SignedShuffleBasic
import HolomorphicAnosov.Topology.Homology.SignedShuffleData

/-! For arbitrary topological spaces X,Y and singular one-simplices σ,τ, the boundary of their rational signed shuffle is the shuffle of ∂[σ] with [τ] minus the shuffle of [σ] with ∂[τ]. Degenerate simplices are included.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 equation (5.4), p.65, and Theorem5.2 instruction to compute the (1,1) case directly, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
noncomputable section
namespace HolomorphicAnosov.SignedShuffle
universe u
namespace OneOne

/-- The right-then-up staircase of the unit square, EM1953 (5.4), p.65. -/
abbrev horizontalFirst : SignedSingularCrossProduct.GridPath 1 1 :=
  fun k ↦ if k = 0 then (0, 0) else if k = 1 then (1, 0) else (1, 1)
/-- The up-then-right staircase of the unit square, EM1953 (5.4), p.65. -/
abbrev verticalFirst : SignedSingularCrossProduct.GridPath 1 1 :=
  fun k ↦ if k = 0 then (0, 0) else if k = 1 then (0, 1) else (1, 1)
theorem staircases_one_one : SignedSingularCrossProduct.staircases 1 1 = {horizontalFirst, verticalFirst} := by
  decide
theorem orientation_horizontalFirst : SignedSingularCrossProduct.orientation horizontalFirst = 1 := by decide
theorem orientation_verticalFirst : SignedSingularCrossProduct.orientation verticalFirst = -1 := by decide
theorem shuffleGenerator_one_one (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    shuffleGenerator X Y σ τ =
      generator (TopCat.of (X × Y)) (SignedSingularCrossProduct.productSimplex X Y horizontalFirst σ τ) -
      generator (TopCat.of (X × Y)) (SignedSingularCrossProduct.productSimplex X Y verticalFirst σ τ) := by
  have hp : SignedSingularCrossProduct.staircases 1 1 = {horizontalFirst, verticalFirst} := by decide
  have hne : horizontalFirst ≠ verticalFirst := by decide
  have hh : SignedSingularCrossProduct.orientation horizontalFirst = 1 := by decide
  have hv : SignedSingularCrossProduct.orientation verticalFirst = -1 := by decide
  simp [shuffleGenerator, hp, Finset.sum_insert, hne, hh, hv, sub_eq_add_neg]
theorem middle_faces_agree (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (1 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y horizontalFirst σ τ) =
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (1 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y verticalFirst σ τ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).1)
        (Convexity.StdSimplex.map (1 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).2)
        (Convexity.StdSimplex.map (1 : Fin 3).succAbove z))) = _
  change _ =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).1)
        (Convexity.StdSimplex.map (1 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).2)
        (Convexity.StdSimplex.map (1 : Fin 3).succAbove z)))
  simp only [← Convexity.StdSimplex.map_comp]
  congr 3 <;> funext i <;> fin_cases i <;> rfl
theorem zero_simplex_eq_point (X : TopCat.{u}) (σ : Simplex X 0) :
    σ = pointSimplex X ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) σ)
      (Convexity.StdSimplex.single (0 : Fin 1))) := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) σ) z =
    (TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) σ) (Convexity.StdSimplex.single (0 : Fin 1))
  congr 1
  exact @Subsingleton.elim (Convexity.StdSimplex ℝ (Fin 1)) inferInstance _ _

theorem horizontalFirst_face_zero (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (0 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y horizontalFirst σ τ) =
      insertLeft X Y ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)
        ((TopCat.toSSet.obj X).δ (0 : Fin 2) σ))
        (Convexity.StdSimplex.single (0 : Fin 1))) τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).1)
        (Convexity.StdSimplex.map (0 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).2)
        (Convexity.StdSimplex.map (0 : Fin 3).succAbove z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  have h1 : (fun k ↦ (horizontalFirst k).1) ∘ (0 : Fin 3).succAbove =
      fun _ ↦ (1 : Fin 2) := by funext i; fin_cases i <;> rfl
  have h2 : (fun k ↦ (horizontalFirst k).2) ∘ (0 : Fin 3).succAbove = id := by
    funext i; fin_cases i <;> rfl
  rw [h1, h2, Convexity.StdSimplex.map_id]
  change ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ) _, _) =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (0 : Fin 2).succAbove
        (Convexity.StdSimplex.single (0 : Fin 1))), _)
  simp only [Convexity.StdSimplex.map_const, Convexity.StdSimplex.map_single]
  rfl
theorem verticalFirst_face_two (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (2 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y verticalFirst σ τ) =
      insertLeft X Y ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌)
        ((TopCat.toSSet.obj X).δ (1 : Fin 2) σ))
        (Convexity.StdSimplex.single (0 : Fin 1))) τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).1)
        (Convexity.StdSimplex.map (2 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).2)
        (Convexity.StdSimplex.map (2 : Fin 3).succAbove z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  have h1 : (fun k ↦ (verticalFirst k).1) ∘ (2 : Fin 3).succAbove =
      fun _ ↦ (0 : Fin 2) := by funext i; fin_cases i <;> rfl
  have h2 : (fun k ↦ (verticalFirst k).2) ∘ (2 : Fin 3).succAbove = id := by
    funext i; fin_cases i <;> rfl
  rw [h1, h2, Convexity.StdSimplex.map_id]
  change ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ) _, _) =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (1 : Fin 2).succAbove
        (Convexity.StdSimplex.single (0 : Fin 1))), _)
  simp only [Convexity.StdSimplex.map_const, Convexity.StdSimplex.map_single]
  rfl
theorem verticalFirst_face_zero (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (0 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y verticalFirst σ τ) =
      insertRight X Y σ ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌)
        ((TopCat.toSSet.obj Y).δ (0 : Fin 2) τ))
        (Convexity.StdSimplex.single (0 : Fin 1))) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).1)
        (Convexity.StdSimplex.map (0 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (verticalFirst k).2)
        (Convexity.StdSimplex.map (0 : Fin 3).succAbove z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  have h1 : (fun k ↦ (verticalFirst k).1) ∘ (0 : Fin 3).succAbove = id := by
    funext i; fin_cases i <;> rfl
  have h2 : (fun k ↦ (verticalFirst k).2) ∘ (0 : Fin 3).succAbove =
      fun _ ↦ (1 : Fin 2) := by funext i; fin_cases i <;> rfl
  rw [h1, h2, Convexity.StdSimplex.map_id]
  change (_, (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ) _) =
    (_, (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (0 : Fin 2).succAbove
        (Convexity.StdSimplex.single (0 : Fin 1))))
  simp only [Convexity.StdSimplex.map_const, Convexity.StdSimplex.map_single]
  rfl
theorem horizontalFirst_face_two (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ (2 : Fin 3)
      (SignedSingularCrossProduct.productSimplex X Y horizontalFirst σ τ) =
      insertRight X Y σ ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌)
        ((TopCat.toSSet.obj Y).δ (1 : Fin 2) τ))
        (Convexity.StdSimplex.single (0 : Fin 1))) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).1)
        (Convexity.StdSimplex.map (2 : Fin 3).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (horizontalFirst k).2)
        (Convexity.StdSimplex.map (2 : Fin 3).succAbove z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  have h1 : (fun k ↦ (horizontalFirst k).1) ∘ (2 : Fin 3).succAbove = id := by
    funext i; fin_cases i <;> rfl
  have h2 : (fun k ↦ (horizontalFirst k).2) ∘ (2 : Fin 3).succAbove =
      fun _ ↦ (0 : Fin 2) := by funext i; fin_cases i <;> rfl
  rw [h1, h2, Convexity.StdSimplex.map_id]
  change (_, (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ) _) =
    (_, (TopCat.toSSetObjEquiv Y (Opposite.op ⦋1⦌) τ)
      (Convexity.StdSimplex.map (1 : Fin 2).succAbove
        (Convexity.StdSimplex.single (0 : Fin 1))))
  simp only [Convexity.StdSimplex.map_const, Convexity.StdSimplex.map_single]
  rfl
end OneOne

open OneOne

set_option backward.isDefEq.respectTransparency false in
/-- For arbitrary topological spaces X,Y and singular one-simplices σ,τ, the boundary of their rational signed shuffle is the shuffle of ∂[σ] with [τ] minus the shuffle of [σ] with ∂[τ]. Degenerate simplices are included.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 equation (5.4), p.65, and Theorem5.2 instruction to compute the (1,1) case directly, p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: The unit square has exactly two monotone staircases, right-then-up and up-then-right. Their vertical-before-horizontal inversion counts are zero and one, respectively. Thus the shuffle is the first product triangle minus the second. The finite enumeration and signs are kernel-checked by decidability.

Use the alternating-face boundary of each triangle. Deleting the middle vertex gives the same diagonal on both triangles, hence cancellation. For the right-then-up triangle its zeroth face inserts the terminal point of σ in the first coordinate, and its second face inserts the initial point of τ in the second. For the up-then-right triangle its zeroth face inserts the terminal point of τ in the second coordinate, and its second face inserts the initial point of σ in the first. These equalities follow by composing affine simplex maps and checking the two resulting vertex maps; constant maps send a simplex to the corresponding vertex.

Every singular zero-simplex is a point because the standard zero-simplex is a singleton. The proved zero-degree shuffle rows identify the four remaining face terms with the products of input faces. Expand the boundaries of σ and τ as terminal point minus initial point and use bilinearity. Additive cancellation gives exactly the displayed Leibniz identity with sign −1. -/
theorem shuffle_one_one_boundary_generator (X Y : TopCat.{u}) (σ : Simplex X 1) (τ : Simplex Y 1) :
    boundary (TopCat.of (X × Y)) 2 (shuffleGenerator X Y σ τ) =
      firstBoundaryTerm X Y 1 1 (generator X σ) (generator Y τ) +
        (-1 : ℚ) ^ 1 • secondBoundaryTerm X Y 1 1 (generator X σ) (generator Y τ) := by
  rw [shuffleGenerator_one_one, map_sub, boundary_generator_succ _ 1, boundary_generator_succ _ 1]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    pow_zero, pow_one, one_smul, neg_one_smul]
  norm_num only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero, pow_one, neg_one_sq, one_smul, neg_one_smul]
  rw [horizontalFirst_face_zero, horizontalFirst_face_two, verticalFirst_face_zero,
    verticalFirst_face_two, middle_faces_agree]
  simp only [firstBoundaryTerm, secondBoundaryTerm, Nat.one_ne_zero, dite_false,
    Nat.reduceAdd, Nat.reduceSub, regrade, LinearMap.id_apply]
  rw [boundary_generator_succ _ 0, boundary_generator_succ _ 0]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, add_zero,
    map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  have hl (υ : Simplex X 0) : shuffleBilinear X Y 0 1 (generator X υ) (generator Y τ) =
      generator (TopCat.of (X × Y)) (insertLeft X Y
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) υ)
          (Convexity.StdSimplex.single (0 : Fin 1))) τ) := by
    rw [zero_simplex_eq_point X υ]
    simpa only [shuffle, TensorProduct.lift.tmul, regrade, LinearMap.id_apply,
      pointSimplex, Equiv.apply_symm_apply, ContinuousMap.const_apply] using
      left_row_point X Y 1 ((TopCat.toSSetObjEquiv X (Opposite.op ⦋0⦌) υ)
        (Convexity.StdSimplex.single (0 : Fin 1))) τ
  have hr (υ : Simplex Y 0) : shuffleBilinear X Y 1 0 (generator X σ) (generator Y υ) =
      generator (TopCat.of (X × Y)) (insertRight X Y σ
        ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) υ)
          (Convexity.StdSimplex.single (0 : Fin 1)))) := by
    rw [zero_simplex_eq_point Y υ]
    simpa only [shuffle, TensorProduct.lift.tmul, regrade, LinearMap.id_apply,
      pointSimplex, Equiv.apply_symm_apply, ContinuousMap.const_apply] using
      right_row_point X Y 1 σ ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋0⦌) υ)
        (Convexity.StdSimplex.single (0 : Fin 1)))
  rw [hl, hl, hr, hr]
  abel
end HolomorphicAnosov.SignedShuffle
