import HolomorphicAnosov.Topology.GallierXuFaceWordSides
import HolomorphicAnosov.Topology.GallierXuOriginalEdgeParameter

/-! # Faithfulness of the original triangle presentation

Source: Gallier–Xu, Proposition 3.2 p.31, and Lee, Proposition 6.14 p.173.
The statements concern the literal vertex, edge-label and word encodings. -/

noncomputable section
open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- Equality of the min/max pair labels retains each endpoint. Decode Nat.pair,
then compare the two possible endpoint orders. -/
lemma edgeLabel_endpoint {N : ℕ} {a b u v : Fin N}
    (h : edgeLabel a b = edgeLabel u v) : a = u ∨ a = v := by
  have hh := Nat.pair_eq_pair.mp h
  have hmin := hh.1
  have hmax := hh.2
  have ha : a.val = u.val ∨ a.val = v.val := by omega
  exact ha.imp Fin.ext Fin.ext

/-- The cyclic word determines its original triangle. Source: Gallier–Xu,
Proposition 3.2 p.31, original-edge labeling. Every vertex is an endpoint
of a recorded side. Equal words therefore put all vertices of the first
triangle in the second; both have three vertices, so their sets agree. -/
lemma triangle_word_injective {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s t : Triangle K) (o : Fin 3 ≃ ↥s.val) (p : Fin 3 ≃ ↥t.val)
    (h : triangleWord s o = triangleWord t p) : s = t := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨i, hi⟩ := o.surjective ⟨a, ha⟩
    have hm : edgeDart (o i).val (o (finRotate 3 i)).val ∈ triangleWord t p := by
      rw [← h]
      simp only [triangleWord, List.mem_map]
      exact ⟨i, List.mem_finRange _, rfl⟩
    simp only [triangleWord, List.mem_map] at hm
    obtain ⟨j, _, hj⟩ := hm
    have hh : edgeLabel a (o (finRotate 3 i)).val =
        edgeLabel (p j).val (p (finRotate 3 j)).val := by
      simpa [edgeDart, hi] using (congrArg Prod.fst hj).symm
    rcases edgeLabel_endpoint hh with he | he
    · exact he ▸ (p j).property
    · exact he ▸ (p (finRotate 3 j)).property
  · simp only [s.property.2, t.property.2, le_refl]

/-- Every original triangle word occurs once in the presentation. The list of
attached triangle indices has no duplicates, and triangle-word injectivity
preserves this property under its defining list map. -/
lemma triangle_presentation_nodup {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) : (trianglePresentation K o).Nodup := by
  apply List.Nodup.map
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun s : Triangle K ↦ s.val) (triangle_word_injective _ _ _ _ hab)
  · exact Finset.nodup_toList _

/-- Each original triangle has a face index in the presentation, by membership
in the finite triangle set and the defining list map. -/
lemma triangle_word_occurs {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) (s : Triangle K) :
    ∃ f : Fin (trianglePresentation K o).length,
      triangleWord s (o s) = (trianglePresentation K o).get f := by
  suffices h : triangleWord s (o s) ∈ trianglePresentation K o by
    obtain ⟨f, hf⟩ := List.mem_iff_get.mp h
    exact ⟨f, hf.symm⟩
  simp only [trianglePresentation, List.mem_map]
  have hs : s.val ∈ simplices K 2 := by simpa [simplices] using s.property
  exact ⟨⟨s.val, hs⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩

/-- Every distinct pair of triangle vertices labels a side of its original
cyclic word. Among three cyclic indices, any two are consecutive in one
of the two orders; swapping endpoints preserves the unoriented label. -/
lemma triangle_pair_side {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) {u v : Fin N}
    (hu : u ∈ s.val) (hv : v ∈ s.val) (hne : u ≠ v) :
    ∃ i : Fin (triangleWord s o).length,
      ((triangleWord s o).get i).1 = edgeLabel u v := by
  obtain ⟨j, hj⟩ := triangle_side_for_pair2 s o hu hv hne
  have hm : edgeDart (o j).val (o (finRotate 3 j)).val ∈ triangleWord s o := by
    simp only [triangleWord, List.mem_map]
    exact ⟨j, List.mem_finRange _, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  refine ⟨i, ?_⟩
  rw [hi]
  rcases hj with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · change edgeLabel (o j).val (o (finRotate 3 j)).val = _
    rw [hu, hv]
  · change edgeLabel (o j).val (o (finRotate 3 j)).val = _
    rw [hu, hv, edgeLabel_comm]

end HolomorphicAnosov.Topology.GallierXu
