import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometryDefs

noncomputable section
open Set _root_.Topology
open scoped Classical BigOperators
namespace HolomorphicAnosov.BarycentricGeometry

/-- Every encoded finite-depth descendant face is nonempty, and every nonempty finite
subface is again encoded at the same depth. This is the finite-set closure clause in
Hatcher, *Algebraic Topology*, Proposition 2.21(1), pp.119--121: a descendant cell
is an image of a nonempty index set, and a nonempty subset of that image is the image
of the corresponding preimage index set. The statement is written for the literal
`iteratedFaces` encoding used by the geometric complex. -/
theorem iteratedFaces_nonempty_down_closed {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin (m + 1) → E) (r : ℕ) :
    (∀ s ∈ iteratedFaces v r, s.Nonempty) ∧
      (∀ s ∈ iteratedFaces v r, ∀ t : Finset E, t ⊆ s → t.Nonempty →
        t ∈ iteratedFaces v r) := by
  classical
  constructor
  · rintro s ⟨p, hp, A, hA, rfl⟩
    exact hA.image _
  · rintro s ⟨p, hp, A, hA, rfl⟩ t hts ht
    obtain ⟨B, hBA, hB⟩ := Finset.subset_image_iff.mp hts
    refine ⟨p, hp, B, ?_, hB.symm⟩
    obtain ⟨x, hx⟩ := ht
    rw [← hB] at hx
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi⟩

end HolomorphicAnosov.BarycentricGeometry
