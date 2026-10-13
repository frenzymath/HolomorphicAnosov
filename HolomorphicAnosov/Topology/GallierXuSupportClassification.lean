import HolomorphicAnosov.Topology.GallierXuFaceWordSides
import HolomorphicAnosov.Topology.GallierXuVertexSupport

noncomputable section
open Set Topology _root_.Topology
open scoped BigOperators
namespace HolomorphicAnosov.Topology.GallierXu

/-- If a simplex point lies in two distinct three-vertex supports, its nonzero
coordinate support has one or two elements. This is the finite carrier
intersection step in Lee Proposition 6.14, p.173. -/
lemma support_single_or_pair_of_distinct_triangles {N : ℕ}
    {x : Fin N → ℝ} (hx : x ∈ {f : Fin N → ℝ | (∀ v, 0 ≤ f v) ∧ ∑ v, f v = 1})
    {K : AbstractSimplicialComplex (Fin N)} {s t : Triangle K} (hst : s ≠ t)
    (hs : ∀ w ∉ s.val, x w = 0) (ht : ∀ w ∉ t.val, x w = 0) :
    (∃ u, u ∈ s.val ∧ u ∈ t.val ∧ x = Pi.single u 1) ∨
      (∃ u v, u ≠ v ∧ u ∈ s.val ∧ v ∈ s.val ∧ u ∈ t.val ∧ v ∈ t.val ∧ (∀ w, w ∉ ({u, v} : Finset (Fin N)) → x w = 0)) := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter (fun w ↦ x w ≠ 0)
  have hSsub_s : S ⊆ s.val := by
    intro w hw
    by_contra hws
    have := hs w hws
    have hnonzero : x w ≠ 0 := by simpa [S] using hw
    rw [this] at hnonzero
    exact (hnonzero rfl).elim
  have hSsub_t : S ⊆ t.val := by
    intro w hw
    by_contra hwt
    have := ht w hwt
    have hnonzero : x w ≠ 0 := by simpa [S] using hw
    rw [this] at hnonzero
    exact (hnonzero rfl).elim
  have hSpos : 0 < S.card := by
    by_contra h
    have hS0 : S.card = 0 := Nat.eq_zero_of_not_pos h
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
    have hzero : ∀ w, x w = 0 := by
      intro w
      by_contra hw
      have hmem : w ∈ S := by simp [S, hw]
      rw [hSempty] at hmem
      simp at hmem
    have hsum0 : (∑ w, x w) = 0 := by simp [hzero]
    linarith [hx.2]
  have hScard : S.card ≤ 2 := by
    by_contra hlarge
    have hS3 : 3 ≤ S.card := by omega
    have hS_card_s : S.card ≤ s.val.card := Finset.card_le_card hSsub_s
    have hS_eq_s : S = s.val := by
      apply Finset.eq_of_subset_of_card_le hSsub_s
      rw [s.property.2]
      exact hS3
    have hS_eq_t : S = t.val := by
      apply Finset.eq_of_subset_of_card_le hSsub_t
      rw [t.property.2]
      exact hS3
    apply hst
    apply Subtype.ext
    exact hS_eq_s.symm.trans hS_eq_t
  have hScases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hScases with h1 | h2
  · left
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    have hz : ∀ w, w ≠ u → x w = 0 := by
      intro w hw
      by_contra hn
      have : w ∈ S := by simp [S, hn]
      rw [hu] at this
      simp [hw] at this
    have huS : u ∈ S := by rw [hu]; simp
    exact ⟨u, hSsub_s huS, hSsub_t huS, simplex_single_vertex_support hx hz⟩
  · right
    obtain ⟨u, v, huv, hUv⟩ := Finset.card_eq_two.mp h2
    have huS : u ∈ S := by rw [hUv]; simp
    have hvS : v ∈ S := by rw [hUv]; simp
    refine ⟨u, v, huv, hSsub_s huS, hSsub_s hvS, hSsub_t huS, hSsub_t hvS, ?_⟩
    intro w hw
    by_contra hn
    have hmem : w ∈ S := by simp [S, hn]
    rw [hUv] at hmem
    simp [hw] at hmem

end HolomorphicAnosov.Topology.GallierXu
