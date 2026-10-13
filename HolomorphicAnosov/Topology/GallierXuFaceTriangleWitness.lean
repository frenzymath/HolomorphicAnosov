import HolomorphicAnosov.Topology.GallierXuFaceMapGenerators

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Every face index in the concrete triangle presentation comes from a unique
listed triangle occurrence, and its word is the corresponding triangleWord.
The witness is intentionally existential: the presentation is a list map, so
later face-map constructions may choose the occurrence without changing the
presentation or quotient relation. -/
lemma trianglePresentation_face_witness {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length) :
    ∃ s : Triangle K,
      triangleWord s (o s) = (trianglePresentation K o).get f := by
  have hf := List.get_mem (trianglePresentation K o) f
  simp only [trianglePresentation, List.mem_map] at hf
  obtain ⟨s, hs, heq⟩ := hf
  let t : Triangle K := ⟨s.val, by simpa [simplices] using s.property⟩
  exact ⟨t, heq⟩

/-- The selected triangle occurrence has exactly the three prescribed original
vertices, and each presentation side carries two distinct endpoints. -/
lemma trianglePresentation_face_word_mem {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length)
    (s : Triangle K) (hs : triangleWord s (o s) = (trianglePresentation K o).get f)
    (i : Fin ((trianglePresentation K o).get f).length) :
    ∃ j : Fin 3,
      edgeDart (o s j).val (o s (finRotate 3 j)).val =
        ((trianglePresentation K o).get f).get i := by
  have hi : ((trianglePresentation K o).get f).get i ∈ triangleWord s (o s) := by
    rw [hs]
    exact List.get_mem _ i
  simp only [triangleWord, List.mem_map] at hi
  rcases hi with ⟨j, hj, h⟩
  exact ⟨j, h⟩

end HolomorphicAnosov.Topology.GallierXu
