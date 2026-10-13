import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic

noncomputable section
open Set
open scoped BigOperators
namespace HolomorphicAnosov

/-- The centroid of a face of a geometric simplicial complex belongs to another
face hull exactly when the first vertex set is contained in the second.

This is an agent-written expansion of the face-detection step omitted in Schultz,
Mathematics 246A §I.2 Proposition 1 and Corollary 2, p.21. It fills that step in
`topo.iterated_faces_restriction_g19`. Its algebraic input is the written Mathlib
proof `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`
(LinearAlgebra/AffineSpace/Independent.lean, line 511).

The centroid has uniform positive weights on every vertex of its nonempty face.
If it also lies in a second face hull, the simplicial intersection axiom places
it in the convex hull, hence affine span, of the common vertices. Affine
independence forces the weight of any vertex outside that common set to be zero.
This contradicts positivity, so all first-face vertices lie in the second face.
Conversely containment of vertex sets gives containment of convex hulls, and the
centroid lies in its own face hull. Singleton faces and arbitrary ambient real
vector spaces are included; no global finiteness assumption is used. -/
theorem simplicial_face_centroid_mem_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    s.centroid ℝ id ∈ convexHull ℝ (t : Set E) ↔ s ⊆ t := by
  classical
  have hsne := K.nonempty_of_mem_faces hs
  let : Nonempty s := hsne.to_subtype
  have hxs : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) := s.centroid_mem_convexHull hsne
  constructor
  · intro hxt
    have hxst := K.inter_subset_convexHull hs ht ⟨hxs, hxt⟩
    have himage : ((↑) : s → E) '' {i : s | (i : E) ∈ t} = (s : Set E) ∩ t := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.property, hi⟩
      · rintro ⟨hys, hyt⟩
        exact ⟨⟨y, hys⟩, hyt, rfl⟩
    have hcentroid : s.centroid ℝ id = (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) :=
      Finset.centroid_eq_centroid_image_of_inj_on ℝ s
        (fun _ _ _ _ h ↦ h) (by simp)
    have hspan : (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) ∈
        affineSpan ℝ (((↑) : s → E) '' {i : s | (i : E) ∈ t}) := by
      rw [← hcentroid, himage]
      exact convexHull_subset_affineSpan _ hxst
    have hsum := (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty
      ℝ Finset.univ_nonempty
    intro y hys
    by_contra hyt
    have hz := (K.indep hs).eq_zero_of_affineCombination_mem_affineSpan
      hsum hspan (Finset.mem_univ (⟨y, hys⟩ : s)) hyt
    have hcard : (Fintype.card s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (inv_ne_zero hcard)
      (by simpa only [Finset.centroidWeights_apply, Finset.card_univ] using hz)
  · intro hst
    exact convexHull_mono hst hxs

end HolomorphicAnosov

