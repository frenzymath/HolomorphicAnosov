import HolomorphicAnosov.Topology.StandardSimplexBarycentricFlagIntersections
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean transport of standard barycentric flag intersections

Source: Schultz, Mathematics 246A §I.2, Theorem 4, pp.23–25, and Mathematics 205B §IV.2,
Lemma 6, p.51. The coordinate flag intersection theorem is transported through the
canonical inverse `WithLp` linear equivalence to the Euclidean model used by the target.
-/

noncomputable section
open Set
open scoped BigOperators

namespace HolomorphicAnosov.BarycentricGeometry

/-- Euclidean images of two coordinate barycentric flag cells meet in the image
of the convex hull of their common coordinate barycenters.
Source: Schultz, Math 246A §I.2 Theorem 4, pp.23–25; Math 205B §IV.2 Lemma 6,
p.51. Apply the coordinate flag intersection theorem. The inverse `WithLp`
linear equivalence sends convex hulls to convex hulls and, being injective,
sends intersections to intersections. These two identities transport the
coordinate equality to Euclidean space. The empty flag is allowed, and its
convex hull and every intersection involving it are empty. -/
theorem coordinate_flag_cell_intersection_transport (n : ℕ)
    (C D : Finset (Finset (Fin (n + 1))))
    (hC : (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (hD : (∀ F ∈ D, F.Nonempty) ∧
      (D : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    convexHull ℝ
        ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
          ((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _))) ∩
      convexHull ℝ
        ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
          ((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (D : Set _))) =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        (convexHull ℝ
          (((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _)) ∩
            ((fun F : Finset (Fin (n + 1)) ↦
              (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (D : Set _)))) := by
  have he : Function.Injective
      ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap :
        (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) := by
    intro x y hxy
    exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.injective hxy
  rw [← LinearMap.image_convexHull, ← LinearMap.image_convexHull]
  rw [← Set.image_inter he]
  have h := standard_simplex_barycentric_flag_intersections n
  dsimp at h
  rw [h.2.2.1 C D hC hD]


end HolomorphicAnosov.BarycentricGeometry

