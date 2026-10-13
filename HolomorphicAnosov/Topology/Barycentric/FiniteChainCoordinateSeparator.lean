import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

namespace HolomorphicAnosov.BarycentricGeometry

/-- A set omitted by a finite inclusion chain can be separated from that chain by
one coordinate, or by the difference of two coordinates. Agent-written finite ordering detail for the equal-level argument in Schultz, Math 246A §I.2, Theorem 4, p.25.
Choose an index outside the largest chain member not containing F. If a chain
member contains F, choose an outside index in the smallest such member. -/
theorem finite_chain_coordinate_separator {ι : Type*} [DecidableEq ι]
    (D : Finset (Finset ι))
    (hchain : (D : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (F : Finset ι) (hne : F.Nonempty) (hnot : F ∉ D) :
    ∃ i ∈ F, (∀ G ∈ D, i ∉ G) ∨
      ∃ j, j ∉ F ∧ ∀ G ∈ D, i ∈ G → j ∈ G := by
  classical
  let L := D.filter (fun G ↦ ¬ F ⊆ G)
  have hi : ∃ i ∈ F, ∀ G ∈ D, i ∈ G → F ⊆ G := by
    by_cases hL : L.Nonempty
    · obtain ⟨H, hH, hmax⟩ := L.exists_max_image Finset.card hL
      obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp (Finset.mem_filter.mp hH).2
      refine ⟨i, hi, fun G hG hiG ↦ ?_⟩
      by_contra hn
      have hGL : G ∈ L := Finset.mem_filter.mpr ⟨hG, hn⟩
      by_cases he : G = H
      · exact hni (he ▸ hiG)
      · rcases hchain hG (Finset.mem_filter.mp hH).1 he with h | h
        · exact hni (h.subset hiG)
        · exact (not_lt_of_ge (hmax G hGL)) (Finset.card_lt_card h)
    · obtain ⟨i, hi⟩ := hne
      refine ⟨i, hi, fun G hG _ ↦ ?_⟩
      by_contra hn
      exact hL ⟨G, Finset.mem_filter.mpr ⟨hG, hn⟩⟩
  obtain ⟨i, hiF, hi⟩ := hi
  refine ⟨i, hiF, ?_⟩
  let U := D.filter (fun G ↦ F ⊆ G)
  by_cases hU : U.Nonempty
  · right
    obtain ⟨H, hH, hmin⟩ := U.exists_max_image (fun G ↦ (OrderDual.toDual G.card)) hU
    have hHD := (Finset.mem_filter.mp hH).1
    have hFH : F ⊂ H := (Finset.mem_filter.mp hH).2.ssubset_of_ne (by
      intro he
      exact hnot (he ▸ hHD))
    obtain ⟨j, hjH, hjF⟩ := Finset.exists_of_ssubset hFH
    refine ⟨j, hjF, fun G hG hiG ↦ ?_⟩
    have hGU : G ∈ U := Finset.mem_filter.mpr ⟨hG, hi G hG hiG⟩
    by_cases he : H = G
    · exact he ▸ hjH
    · rcases hchain hHD hG he with h | h
      · exact h.subset hjH
      · exact False.elim ((not_lt_of_ge (hmin G hGU)) (Finset.card_lt_card h))
  · left
    intro G hG hiG
    exact hU ⟨G, Finset.mem_filter.mpr ⟨hG, hi G hG hiG⟩⟩

end HolomorphicAnosov.BarycentricGeometry
