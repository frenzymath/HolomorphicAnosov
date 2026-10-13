import HolomorphicAnosov.Topology.Barycentric.StandardFlagConvexHullInter
import HolomorphicAnosov.Topology.Barycentric.StandardFlagFaceTrace
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Common faces of barycentric flag simplices

Source: Reinhard Schultz, Mathematics 246A §I.2, Proposition 3 and Theorem 4, pp.23–25.
-/

open scoped BigOperators

namespace HolomorphicAnosov

/--
The barycentric flags in the original standard simplex form its finite geometric flag complex.

Source: Reinhard Schultz, Mathematics 246A §I.2, Proposition 3 printed p.23 and
Theorem 4 pp.24–25, with the arbitrary-subface reduction in Mathematics 205B §IV.2,
Default Hypothesis discussion p.52 and Proposition 1/Corollary 2 pp.46–47.

The ambient vectors are literally Fin(n+1)→ℝ, the standard vertices are Pi.single i 1,
and stdSimplex is Mathlib's set of nonnegative vectors whose coordinate sum is one.
The local flag predicate is a finite family of nonempty index subsets strictly
comparable by inclusion; the empty family satisfies it. Each local barycenter is
exactly the displayed equal-weight sum. Convex hulls are Mathlib's actual convexHull.
No coordinates are identified under a singular map. Mathlib's SimplicialComplex
stores only NONEMPTY faces. Therefore its faces are exactly the nonempty flag vertex
sets, while the empty flag, its empty hull, and all intersections involving it remain
explicit in the other conclusions. Original-face restriction is both the displayed
trace formula and the exact characterization of the restricted complex's faces.

Complete natural-language proof:

Compute each coordinate of b_F: it is 1/|F| on F and zero elsewhere. For a strict
chain, remove its largest face F. If smaller faces exist, choose an index of F
outside the largest smaller face; otherwise choose any index of F. All previous
barycenters vanish at this coordinate, whereas b_F is positive. Induction gives
linear independence, hence affine independence. This is a direct standard-coordinate
refinement of Proposition 3's triangular argument; it avoids maximal-flag extension.

For two nonnegative chain expansions of a vector, a positive coefficient on F makes
every coordinate inside F strictly larger than every coordinate outside F: nested
faces contribute nonnegative differences, and F contributes a positive difference.
If the second chain omits F, choose i in F outside its largest member not containing
F. If no member contains F, its i-coordinate is zero, contradicting the positive
first expansion. Otherwise choose j outside F in its smallest member containing F;
every member containing i also contains j. The second expansion therefore has
coordinate i at most coordinate j, another contradiction. This finite-chain
separator is an explicitly agent-written ordering detail expanding the source's
equal-level argument. Thus every positive coefficient occurs on a common face.
Discard zero coefficients to obtain the hull of common vertices; the reverse
inclusion is hull monotonicity. This proves arbitrary-flag intersections directly,
without the source's extension to maximal flags and subsequent subface reduction.

For an original face A, every coordinate outside A vanishes. Nonnegative weights
force the coefficient of every F not contained in A to vanish. Restricting the
combination proves the exact trace formula. Conversely a barycenter lies in A
whenever its index set is contained in A, by its uniform convex combination.
Each barycenter also lies in the standard simplex, so convexity gives containment.

Define the complex's faces to be the nonempty flag vertex sets. A nonempty subset
of one such set is the image of the subflag selected by vertex membership, proving
downward closure. Independence and the intersection result supply the other fields.
There are finitely many flags on the finite index type, hence finitely many faces.
A cell is contained in A exactly when all its barycenters are, equivalent to every
index set being contained in A. Empty hulls are empty, and the complex has no empty
face, proving the final empty restriction. All arguments allow n=0 and empty flags.
-/
theorem standard_simplex_barycentric_flag_intersections (n : ℕ) :
    let e : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun i ↦ Pi.single i 1
    let b : Finset (Fin (n + 1)) → (Fin (n + 1) → ℝ) :=
      fun F ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, e i
    let flag : Finset (Finset (Fin (n + 1))) → Prop := fun C ↦
      (∀ F ∈ C, F.Nonempty) ∧
        (C : Set (Finset (Fin (n + 1)))).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F)
    let vertices := fun C : Finset (Finset (Fin (n + 1))) ↦
      b '' (C : Set (Finset (Fin (n + 1))))
    let cell := fun C : Finset (Finset (Fin (n + 1))) ↦ convexHull ℝ (vertices C)
    let face := fun A : Finset (Fin (n + 1)) ↦
      convexHull ℝ (e '' (A : Set (Fin (n + 1))))
    (∀ C, flag C → AffineIndependent ℝ (fun p : vertices C ↦
      (p : Fin (n + 1) → ℝ))) ∧
    (∀ C, flag C → cell C ⊆
      {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}) ∧
    (∀ C D, flag C → flag D →
      cell C ∩ cell D = convexHull ℝ (vertices C ∩ vertices D)) ∧
    (∀ C D, flag C → D ⊆ C → flag D) ∧
    (∀ (A : Finset (Fin (n + 1))) C, flag C →
      cell C ∩ face A = cell (C.filter (fun F ↦ F ⊆ A))) ∧
    cell ∅ = ∅ ∧ face ∅ = ∅ ∧
    ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      K.faces.Finite ∧
      (∀ s, s ∈ K.faces ↔
        ∃ C, flag C ∧ C.Nonempty ∧ (s : Set (Fin (n + 1) → ℝ)) = vertices C) ∧
      (∀ A : Finset (Fin (n + 1)),
        {s ∈ K.faces | convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) ⊆ face A} =
          {s : Finset (Fin (n + 1) → ℝ) |
            ∃ C, flag C ∧ C.Nonempty ∧ (∀ F ∈ C, F ⊆ A) ∧
            (s : Set (Fin (n + 1) → ℝ)) = vertices C}) ∧
      {s ∈ K.faces | convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) ⊆ face ∅} = ∅ := by
  classical
  let e : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun i ↦ Pi.single i 1
  let b : Finset (Fin (n + 1)) → (Fin (n + 1) → ℝ) :=
    fun F ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, e i
  let flag : Finset (Finset (Fin (n + 1))) → Prop := fun C ↦
    (∀ F ∈ C, F.Nonempty) ∧
      (C : Set (Finset (Fin (n + 1)))).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F)
  let vertices := fun C : Finset (Finset (Fin (n + 1))) ↦ b '' (C : Set _)
  let cell := fun C : Finset (Finset (Fin (n + 1))) ↦ convexHull ℝ (vertices C)
  let face := fun A : Finset (Fin (n + 1)) ↦ convexHull ℝ (e '' (A : Set _))
  have hind : ∀ C, flag C → AffineIndependent ℝ (fun p : vertices C ↦
      (p : Fin (n + 1) → ℝ)) := by
    intro C hC
    exact (BarycentricGeometry.standard_flag_linearIndependent C hC.1 hC.2).id_image.affineIndepOn
  have hcontain : ∀ C, flag C → cell C ⊆
      {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
    have hconvex : Convex ℝ
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      intro f hf g hg a b ha hb hab
      refine ⟨fun i ↦ add_nonneg (mul_nonneg ha (hf.1 i))
        (mul_nonneg hb (hg.1 i)), ?_⟩
      simp_rw [Pi.add_apply, Pi.smul_apply]
      rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2,
        smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    have hhull : convexHull ℝ (Set.range (fun i : Fin (n + 1) ↦ Pi.single i (1 : ℝ))) =
        {f : Fin (n + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
      refine Set.Subset.antisymm (convexHull_min ?_ hconvex) ?_
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
    intro C hC
    apply convexHull_min _ hconvex
    rintro x ⟨F, hF, rfl⟩
    have h := (BarycentricGeometry.standard_barycenter_mem_face_iff F Finset.univ
      (hC.1 F hF)).mpr (Finset.subset_univ F)
    simpa only [Finset.coe_univ, Set.image_univ, hhull] using h
  have hinter : ∀ C D, flag C → flag D →
      cell C ∩ cell D = convexHull ℝ (vertices C ∩ vertices D) := by
    intro C D hC hD
    exact BarycentricGeometry.standard_flag_convexHull_inter C D hC.1 hD.1 hC.2 hD.2
  have hsub : ∀ C D, flag C → D ⊆ C → flag D := by
    intro C D hC hDC
    exact ⟨fun F hF ↦ hC.1 F (hDC hF), hC.2.mono hDC⟩
  have htrace : ∀ A C, flag C → cell C ∩ face A = cell (C.filter (fun F ↦ F ⊆ A)) := by
    intro A C hC
    exact BarycentricGeometry.standard_flag_face_trace C hC.1 hC.2 A
  have hcempty : cell ∅ = ∅ := by simp [cell, vertices]
  have hfempty : face ∅ = ∅ := by simp [face]
  refine ⟨hind, hcontain, hinter, hsub, htrace, hcempty, hfempty, ?_⟩
  let K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) := {
    faces := {s | ∃ C, flag C ∧ C.Nonempty ∧ (s : Set _) = vertices C}
    isRelLowerSet_faces := by
      rintro s ⟨C, hC, hCn, hs⟩
      constructor
      · obtain ⟨F, hF⟩ := hCn
        have hb : b F ∈ (s : Set _) := hs.symm ▸ Set.mem_image_of_mem b hF
        exact ⟨b F, hb⟩
      · intro t hts htn
        let D := C.filter (fun F ↦ b F ∈ t)
        have hDsub : D ⊆ C := Finset.filter_subset _ _
        have ht : (t : Set _) = vertices D := by
          ext x
          constructor
          · intro hx
            have hxs : x ∈ vertices C := hs ▸ hts hx
            obtain ⟨F, hF, rfl⟩ := hxs
            exact ⟨F, Finset.mem_filter.mpr ⟨hF, hx⟩, rfl⟩
          · rintro ⟨F, hF, rfl⟩
            exact (Finset.mem_filter.mp hF).2
        refine ⟨D, hsub C D hC hDsub, ?_, ht⟩
        obtain ⟨x, hx⟩ := htn
        have hxD : x ∈ vertices D := ht ▸ hx
        obtain ⟨F, hF, _⟩ := hxD
        exact ⟨F, hF⟩
    indep := by
      rintro s ⟨C, hC, _, hs⟩
      have hi := hind C hC
      rw [← hs] at hi
      exact hi
    inter_subset_convexHull := by
      rintro s t ⟨C, hC, _, hs⟩ ⟨D, hD, _, ht⟩
      rw [hs, ht, ← hinter C D hC hD]
  }
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · apply (Set.finite_range (fun C : Finset (Finset (Fin (n + 1))) ↦ C.image b)).subset
    rintro s ⟨C, _, _, hs⟩
    refine ⟨C, ?_⟩
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using hs.symm
  · intro s
    rfl
  · intro A
    ext s
    constructor
    · rintro ⟨⟨C, hC, hCn, hs⟩, hface⟩
      refine ⟨C, hC, hCn, ?_, hs⟩
      intro F hF
      apply (BarycentricGeometry.standard_barycenter_mem_face_iff F A (hC.1 F hF)).mp
      apply hface
      apply subset_convexHull ℝ
      exact hs.symm ▸ Set.mem_image_of_mem b hF
    · rintro ⟨C, hC, hCn, hCA, hs⟩
      refine ⟨⟨C, hC, hCn, hs⟩, ?_⟩
      rw [hs]
      apply convexHull_min _ (convex_convexHull ℝ _)
      rintro x ⟨F, hF, rfl⟩
      exact (BarycentricGeometry.standard_barycenter_mem_face_iff F A (hC.1 F hF)).mpr (hCA F hF)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hs, hzero⟩
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
    have hxcell : x ∈ convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) :=
      subset_convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) hx
    have hm := hzero hxcell
    change x ∈ face ∅ at hm
    rw [hfempty] at hm
    exact hm

end HolomorphicAnosov
