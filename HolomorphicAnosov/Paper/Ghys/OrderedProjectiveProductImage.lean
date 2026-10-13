import HolomorphicAnosov.Geometry.ComplexProjectiveLine

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov.Ghys

/-! Ranges of complete stable and unstable leaf coordinates in an ordered projective product. (Ghys,
§5 pp.597–598) -/

/-- A stable leaf coordinate with whole source and constant transverse coordinate has range the
corresponding horizontal punctured projective line. -/
theorem stable_product_image_of_lift_data
    {U L : Type*} [TopologicalSpace U] [TopologicalSpace L]
    (D : U → ComplexProjectiveLine × ComplexProjectiveLine)
    (u : U) (lift : L → U)
    (hconst : ∀ z, (D (lift z)).2 = (D u).2)
    (pole : ComplexProjectiveLine)
    (e : OpenPartialHomeomorph L ComplexProjectiveLine)
    (hsource : e.source = Set.univ) (htarget : e.target = {pole}ᶜ)
    (heq : ∀ z, e z = (D (lift z)).1) :
    Set.range (fun z ↦ D (lift z)) =
      {q | q.1 ≠ pole ∧ q.2 = (D u).2} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, hconst z⟩
    have hz : e z ∈ e.target := e.map_source (hsource.symm ▸ Set.mem_univ z)
    rw [htarget, heq z] at hz
    exact hz
  · intro hq
    have hqtarget : q.1 ∈ e.target := by
      rw [htarget]
      exact hq.1
    refine ⟨e.symm q.1, ?_⟩
    apply Prod.ext
    · exact (heq _).symm.trans (e.right_inv hqtarget)
    · exact (hconst _).trans hq.2.symm

/-- An unstable leaf coordinate with whole source and constant transverse coordinate has range the
corresponding vertical punctured projective line. -/
theorem unstable_product_image_of_lift_data
    {U L : Type*} [TopologicalSpace U] [TopologicalSpace L]
    (D : U → ComplexProjectiveLine × ComplexProjectiveLine)
    (u : U) (lift : L → U)
    (hconst : ∀ z, (D (lift z)).1 = (D u).1)
    (pole : ComplexProjectiveLine)
    (e : OpenPartialHomeomorph L ComplexProjectiveLine)
    (hsource : e.source = Set.univ) (htarget : e.target = {pole}ᶜ)
    (heq : ∀ z, e z = (D (lift z)).2) :
    Set.range (fun z ↦ D (lift z)) =
      {q | q.1 = (D u).1 ∧ q.2 ≠ pole} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨hconst z, ?_⟩
    have hz : e z ∈ e.target := e.map_source (hsource.symm ▸ Set.mem_univ z)
    rw [htarget, heq z] at hz
    exact hz
  · intro hq
    have hqtarget : q.2 ∈ e.target := by
      rw [htarget]
      exact hq.2
    refine ⟨e.symm q.2, ?_⟩
    apply Prod.ext
    · exact (hconst _).trans hq.1.symm
    · exact (heq _).symm.trans (e.right_inv hqtarget)

end HolomorphicAnosov.Ghys
