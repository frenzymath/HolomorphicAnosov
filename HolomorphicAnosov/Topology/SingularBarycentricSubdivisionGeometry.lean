import HolomorphicAnosov.Topology.BarycentricGeometry.CoordinateFlagIntersectionEuclidean
import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesDiameter
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesContainment
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesZeroDiameter
import HolomorphicAnosov.Topology.BarycentricGeometry.MaximalCellsConed
import HolomorphicAnosov.Topology.BarycentricGeometry.FlagFacesOneStep
import HolomorphicAnosov.Topology.BarycentricGeometry.IteratedFacesComplex
import HolomorphicAnosov.Topology.BarycentricHullBridge
import Mathlib.Data.Set.Finite.List
import HolomorphicAnosov.Topology.BarycentricCoverage
import HolomorphicAnosov.Topology.StandardSimplexBarycentricFlagIntersections
import HolomorphicAnosov.Topology.BarycentricIteratedMesh
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Order.NonemptyFiniteChains

/-!
# Euclidean barycentric subdivision geometry

Source: Hatcher, *Algebraic Topology*, Proposition 2.21 proof (1), pp.119–121,
and Appendix, pp.534–535. The flag-intersection prerequisite follows the written
Schultz subdivision argument named in the current DAG, rather than assuming the
geometric-complex assertion that Hatcher leaves without proof.

The original simplex uses the genuine Euclidean norm, not the coordinate maximum
norm. Prefix and iterated vertices are the existing `BarycentricMesh` definitions.
Finite chains are Mathlib's `PartialOrder.NonemptyFiniteChains`. The geometric
simplicial complexes below are conclusion witnesses with exactly the concrete
specified faces; no subdivision oracle or new input hypothesis is supplied.
-/

noncomputable section

open Set _root_.Topology
open scoped Classical BigOperators

namespace HolomorphicAnosov.BarycentricGeometry

/-- The Euclidean face centroid has the explicit equal-weight formula used by
the coordinate flag theorem. This is the manual affine-combination bridge. -/
theorem faceBarycenter_eq_equalWeightSum {n : ℕ} (F : OriginalFace n) :
    faceBarycenter n F =
      (F.val.card : ℝ)⁻¹ • ∑ i ∈ F.val, standardVertices n i := by
  unfold faceBarycenter
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
  · simp only [Finset.centroidWeights_apply]
    rw [← Finset.smul_sum]
  · simpa using F.val.sum_centroidWeights_eq_one_of_nonempty ℝ F.property

/- The Euclidean coordinate embedding commutes with the finite vertex sum. -/
theorem standardVertices_sum_eq_toLp {n : ℕ} (F : Finset (Fin (n + 1))) :
    ∑ i ∈ F, standardVertices n i =
      WithLp.toLp 2 (∑ i ∈ F, Pi.single i (1 : ℝ)) := by
  rw [WithLp.toLp_sum]
  simp [standardVertices, PiLp.toLp_single]

theorem faceBarycenter_eq_toLp_coordinateBarycenter {n : ℕ}
    (F : OriginalFace n) :
    faceBarycenter n F =
      WithLp.toLp 2 ((F.val.card : ℝ)⁻¹ •
        ∑ i ∈ F.val, Pi.single i (1 : ℝ)) := by
  rw [faceBarycenter_eq_equalWeightSum, standardVertices_sum_eq_toLp]
  rw [WithLp.toLp_smul]

def coordinateFaceBarycenter (n : ℕ) (F : OriginalFace n) : Fin (n + 1) → ℝ :=
  (F.val.card : ℝ)⁻¹ • ∑ i ∈ F.val, Pi.single i (1 : ℝ)

theorem coordinateFaceBarycenter_image {n : ℕ} (C : FaceFlag n) :
    (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap ''
        (flagVertices n C : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      coordinateFaceBarycenter n '' (C.finset : Set (OriginalFace n)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨F, hF, ?_⟩
    rw [faceBarycenter_eq_toLp_coordinateBarycenter]
    rfl
  · rintro ⟨F, hF, rfl⟩
    refine ⟨faceBarycenter n F, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨F, hF, rfl⟩
    · rw [faceBarycenter_eq_toLp_coordinateBarycenter]
      rfl

theorem coordinateFaceHull_image {n : ℕ} (C : FaceFlag n) :
    (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap ''
        (convexHull ℝ (flagVertices n C : Set (EuclideanSpace ℝ (Fin (n + 1))))) =
      convexHull ℝ (coordinateFaceBarycenter n '' (C.finset : Set (OriginalFace n))) := by
  rw [LinearMap.image_convexHull, coordinateFaceBarycenter_image]

theorem coordinate_flag_cell_intersection (n : ℕ)
    (C D : Finset (Finset (Fin (n + 1))))
    (hC : (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (hD : (∀ F ∈ D, F.Nonempty) ∧
      (D : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    convexHull ℝ
        ((fun F : Finset (Fin (n + 1)) ↦
          (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _)) ∩
      convexHull ℝ
        ((fun F : Finset (Fin (n + 1)) ↦
          (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (D : Set _)) =
      convexHull ℝ
        (((fun F : Finset (Fin (n + 1)) ↦
          (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _)) ∩
          ((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (D : Set _))) := by
  have h := standard_simplex_barycentric_flag_intersections n
  dsimp at h
  exact h.2.2.1 C D hC hD

/- For actual face flags, this specializes the linear transport to the named
   `flagVertices` and `faceBarycenter` objects used by the target. -/
theorem flag_cell_hull_intersection_image {n : ℕ} (C D : FaceFlag n) :
    (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap ''
        (convexHull ℝ (flagVertices n C : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩
          convexHull ℝ (flagVertices n D : Set (EuclideanSpace ℝ (Fin (n + 1))))) =
      convexHull ℝ (coordinateFaceBarycenter n '' (C.finset : Set (OriginalFace n))) ∩
        convexHull ℝ (coordinateFaceBarycenter n '' (D.finset : Set (OriginalFace n))) := by
  have he : Function.Injective
      ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap :
        EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ)) := by
    intro x y hxy
    exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).injective hxy
  rw [Set.image_inter he, coordinateFaceHull_image, coordinateFaceHull_image]

/- The imported flag theorem also has the original-face trace clause.  Exposing
   it in the same coordinate notation makes the restriction input explicit. -/
theorem coordinate_flag_restriction (n : ℕ)
    (A : Finset (Fin (n + 1))) (C : Finset (Finset (Fin (n + 1))))
    (hC : (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    convexHull ℝ
        ((fun F : Finset (Fin (n + 1)) ↦
          (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _)) ∩
      convexHull ℝ ((fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ)) '' (A : Set _)) =
      convexHull ℝ
        ((fun F : Finset (Fin (n + 1)) ↦
          (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) ''
            (C.filter (fun F ↦ F ⊆ A) : Set _)) := by
  have h := standard_simplex_barycentric_flag_intersections n
  dsimp at h
  exact h.2.2.2.2.1 A C hC

/- Transport the trace clause back to EuclideanSpace through the inverse
   `WithLp` equivalence. -/
theorem coordinate_flag_restriction_transport (n : ℕ)
    (A : Finset (Fin (n + 1))) (C : Finset (Finset (Fin (n + 1))))
    (hC : (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        (convexHull ℝ
            ((fun F : Finset (Fin (n + 1)) ↦
              (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _)) ∩
          convexHull ℝ
            ((fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ)) '' (A : Set _))) =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        (convexHull ℝ
          ((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) ''
              (↑(C.filter (fun F ↦ F ⊆ A)) : Set (Finset (Fin (n + 1)))))) := by
  have he : Function.Injective
      ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap :
        (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) := by
    intro x y hxy
    exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.injective hxy
  apply (Set.image_eq_image he).2
  exact coordinate_flag_restriction n A C hC

/- The embedding face in the target is the inverse-`WithLp` image of its
   coordinate standard vertices. -/
theorem standardVertices_range_embedding {n m : ℕ}
    (a : Fin (m + 1) ↪ Fin (n + 1)) :
    range (standardVertices n ∘ a) =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        ((fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ)) ''
          ((Finset.univ.image a : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨Pi.single (a j) (1 : ℝ), ?_, ?_⟩
    · exact ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, rfl⟩
    · simp [Function.comp, standardVertices, PiLp.toLp_single]
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    refine ⟨j, ?_⟩
    subst hji
    simp [Function.comp, standardVertices, PiLp.toLp_single]

theorem standardVertices_hull_embedding {n m : ℕ}
    (a : Fin (m + 1) ↪ Fin (n + 1)) :
    convexHull ℝ (range (standardVertices n ∘ a)) =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        (convexHull ℝ
          ((fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ)) ''
            ((Finset.univ.image a : Finset (Fin (n + 1))) : Set (Fin (n + 1))))) := by
  rw [standardVertices_range_embedding]
  rw [← LinearMap.image_convexHull]

theorem coordinate_flag_restriction_embedding {n m : ℕ}
    (a : Fin (m + 1) ↪ Fin (n + 1))
    (C : Finset (Finset (Fin (n + 1))))
    (hC : (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise
        (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    convexHull ℝ
          ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
            ((fun F : Finset (Fin (n + 1)) ↦
              (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) '' (C : Set _))) ∩
      convexHull ℝ (range (standardVertices n ∘ a)) =
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ''
        (convexHull ℝ
          ((fun F : Finset (Fin (n + 1)) ↦
            (F.card : ℝ)⁻¹ • ∑ i ∈ F, Pi.single i (1 : ℝ)) ''
              (↑(C.filter (fun F ↦ F ⊆ Finset.univ.image a)) :
                Set (Finset (Fin (n + 1)))))) := by
  have he : Function.Injective
      ((WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap :
        (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) := by
    intro x y hxy
    exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.injective hxy
  rw [← LinearMap.image_convexHull, standardVertices_hull_embedding]
  rw [← Set.image_inter he]
  rw [coordinate_flag_restriction n (Finset.univ.image a) C hC]

/-- The exact Euclidean barycentric subdivision of Δⁿ, including recursive coning, geometric
simplicial decomposition, all-face restriction, and fixed-dimension iterated mesh estimates.

Source: Hatcher, Algebraic Topology, Proposition 2.21(1), printed pp.119-121;
literature/hatcher-at.txt:6058-6148.

The geometric carrier is the range of Mathlib standard-simplex weights in EuclideanSpace. For every
depth r the witness's faces are exactly the nonempty finite subfaces of the actual
permutation-prefix descendants. Its geometric realization is the original simplex. At r=1 these are
exactly the original-face flags; the maximal cells are exactly the recursively coned cells. The face
clause restricts to any injective original face tuple before iterating, and identifies its cells
with the subcomplex lying in that original face. The empty original face has no cells. The diameter
clauses include lower-dimensional subfaces. At n=0 there is no division by n; every iterated simplex
has diameter zero, including depth zero. No arbitrary singular image is asserted to form a geometric
simplicial complex, and no chain-orientation convention is assumed.

Complete current natural-language proof:

1. Represent Δⁿ as the hull of standard coordinate vertices e_i, or equivalently nonnegative
coordinates summing to one. For each nonempty original face F its barycenter is |F|⁻¹Σ_{i∈F}e_i.
Every maximal chain of nonempty faces has exactly the prefix faces of a permutation: remove the full
face to obtain a maximal flag in the opposite face missing the permutation's last index; conversely
append that missing index and the full face. Thus the prefix construction is exactly Hatcher's
recursive coning construction, with n=0 the unchanged vertex. The centroid-map identity preserves
each barycenter under injective face relabeling.

2. The flag-cell theorem gives affine independence, intersection along the common barycentric vertex
face, closure under taking subflags, and exact restriction to every original face, including empty
and singleton faces. Coverage supplies the union of all maximal prefix cells equal to Δⁿ. Together
these are a finite simplicial decomposition, rather than just a collection whose union covers. Every
centroid and every cell is in the original hull. The ordering of barycenters by face cardinality
agrees with Hatcher Appendix pp.534–535; this geometric statement requires no sign choices or
alternating chain boundary.

3. Apply the existing shape-independent prefix/iterated-mesh theorem to the standard vertex tuple
with D=diam(Δⁿ). The original hull is compact, hence bounded, so every original vertex pair has
distance≤D. The cited theorem gives one-step containment and vertex-pair bound qD for q=n/(n+1). Use
convexHull_exists_dist_ge2 to reduce arbitrary points in a child hull to two of its actual vertices
and Metric.diam_le_of_forall_dist_le with qD≥0 to obtain diam(child)≤qD. Lower-dimensional faces of
each maximal child satisfy the same bound by containment and bounded-superset diameter monotonicity.

4. The shape-independent metric theorem remains an open source prerequisite, not a verified Mathlib
leaf. Hatcher's pp.120–121 argument behind it is this induction: two child vertices other than the
full barycenter lie in one subdivided proper face, whose contraction (n−1)/n is≤n/(n+1); for a pair
involving the full barycenter b, reduce the other face centroid to an original vertex v_i using
convexity. Write b=(1/(n+1))v_i+(n/(n+1))b_i, where b_i is the opposite-face centroid; then
dist(b,v_i)=(n/(n+1))dist(b_i,v_i)≤qD. This uses norm_smul, centroid normalization and convex-hull
distance reduction. The n=0 base avoids division by n. This explains the cited theorem's actual
source mechanism without claiming its unsplit proof obligations have been discharged here.

5. Every depth-r maximal cell is represented by a path of r permutation-prefix choices applied
successively to its actual vertex tuples. The source coverage theorem identifies these choices with
each recursively coned subdivision and preserves restriction to original faces. The mesh theorem
gives diameter≤q^rD for every such tuple, and lower faces inherit it. The estimate uses q for fixed
dimension n and does not assume a child has the standard shape. For n>0, q∈(0,1). The empty path r=0
returns the original hull and q^0=1. For n=0 all subdivisions consist of the singleton, whose
diameter is zero; no 0^0 expression or division by zero is used to establish that case.

6. The metric and coverage inputs allow repeated tuple values and zero original diameter because
they use only convex combinations and distance bounds. This parent's simplicial-decomposition
assertion, however, concerns the standard nondegenerate simplex; the flag theorem is used on that
carrier. An arbitrary singular map may identify different barycenters, so its image cells need not
be affinely independent or a simplicial complex. Orientation signs and repeated singular simplices
enter only the distinct linear/singular chain operator, Hatcher pp.121–123; they do not change these
domain-cell estimates or face restrictions.

-/
theorem singular_barycentric_subdivision_geometry (n : ℕ) :
    euclideanSimplex n = convexHull ℝ (range (standardVertices n)) ∧
    maximalCells n = conedMaximalCells n ∧
    flagFaces n = iteratedFaces (standardVertices n) 1 ∧
    (∀ r : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      K.faces = iteratedFaces (standardVertices n) r ∧ K.faces.Finite ∧
      K.space = euclideanSimplex n ∧
      (∀ s ∈ K.faces, convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        euclideanSimplex n) ∧
      (r = 1 → ∀ s ∈ K.faces,
        Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≤
          ((n : ℝ) / ((n : ℝ) + 1)) * Metric.diam (euclideanSimplex n)) ∧
      (0 < n → ∀ s ∈ K.faces,
        Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≤
          ((n : ℝ) / ((n : ℝ) + 1)) ^ r * Metric.diam (euclideanSimplex n)) ∧
      (n = 0 → ∀ s ∈ K.faces,
        Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1))))) = 0) ∧
      (∀ (m : ℕ) (a : Fin (m + 1) ↪ Fin (n + 1)),
        {s ∈ K.faces | convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
          convexHull ℝ (range (standardVertices n ∘ a))} =
            iteratedFaces (standardVertices n ∘ a) r) ∧
      ({s ∈ K.faces | convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
          (∅ : Set (EuclideanSpace ℝ (Fin (n + 1))))} = ∅)) := by
  have euclideanSimplex_eq_convexHull (n : ℕ) :
      euclideanSimplex n = convexHull ℝ (range (standardVertices n)) := by
    let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
    have hconvex : Convex ℝ
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      intro f hf g hg a b ha hb hab
      refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hf.1 i))
        (mul_nonneg hb (hg.1 i)), ?_⟩
      simp_rw [Pi.add_apply, Pi.smul_apply]
      rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2,
        smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    have hhull : convexHull ℝ (range (fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ))) =
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      refine Subset.antisymm (convexHull_min ?_ hconvex) ?_
      · rintro _ ⟨i, rfl⟩
        constructor
        · intro j
          simp only [Pi.single_apply]
          split <;> norm_num
        · simp
      · rintro w ⟨hw₀, hw₁⟩
        rw [pi_eq_sum_univ w]
        rw [← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
        exact Finset.univ.centerMass_mem_convexHull (fun i _ ↦ hw₀ i)
          (hw₁.symm ▸ zero_lt_one) (fun i _ ↦ by
            exact ⟨i, by ext j; simp [Pi.single_apply, eq_comm]⟩)
    have hsimplex : euclideanSimplex n =
        e '' {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      have hweights :
          range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦
            fun i ↦ t.weights i) =
              {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
        rw [Convexity.StdSimplex.range_toFun_comp_weights]
        ext x
        simp
      rw [← hweights, ← range_comp]
      rfl
    rw [hsimplex, ← hhull]
    change e.toLinearMap '' convexHull ℝ (range (fun i ↦ Pi.single i 1)) = _
    rw [e.toLinearMap.image_convexHull, ← range_comp]
    congr 1
  have iteratedFaces_finite
      (v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) (r : ℕ) : (iteratedFaces v r).Finite := by
    let : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
    let P := {p : List (Equiv.Perm (Fin (n + 1))) | p.length = r}
    have hP : P.Finite := List.finite_length_eq _ _
    refine (hP.prod (Set.finite_univ : (Set.univ : Set (Finset (Fin (n+1)))).Finite)).image
      (fun q ↦ q.2.image (BarycentricMesh.iteratedVertices v q.1)) |>.subset ?_
    rintro s ⟨p, hp, A, hA, rfl⟩
    exact ⟨(p, A), ⟨hp, Set.mem_univ _⟩, rfl⟩
  refine ⟨euclideanSimplex_eq_convexHull n, maximalCells_eq_conedMaximalCells n,
    flagFaces_eq_iteratedFaces_one n, ?_⟩
  intro r
  obtain ⟨K, hK, hspace, hface⟩ := iteratedFaces_simplicialComplex n r
  refine ⟨K, hK, hK.symm ▸ iteratedFaces_finite (standardVertices n) r, hspace,
    ?_, ?_, ?_, ?_, hface, ?_⟩
  · intro s hs
    exact iteratedFaces_hull_subset n r s (hK ▸ hs)
  · rintro rfl s hs
    simpa using iteratedFaces_diam_le n 1 s (hK ▸ hs)
  · intro hn s hs
    exact iteratedFaces_diam_le n r s (hK ▸ hs)
  · rintro rfl s hs
    exact iteratedFaces_diam_zero r s (hK ▸ hs)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hs, hzero⟩
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
    exact hzero (subset_convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) hx)

end HolomorphicAnosov.BarycentricGeometry
