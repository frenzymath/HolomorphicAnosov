import HolomorphicAnosov.Topology.BoundaryCycleEdgeCountG9

open scoped BigOperators
namespace HolomorphicAnosov.Topology.GallierXu

/-- The boundary cycles enumerate each one-incidence edge exactly once, so
its edge count is the sum of the lengths of the disjoint boundary cycles.
Source: Gallier--Xu Definition 6.1, pp.79–81, simple disjoint boundary contours. -/
theorem boundary_edge_count_eq_cycle_lengths_g9 {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B) :
    ((simplices K 1).filter fun e ↦ incidence K e = 1).card =
      ∑ j : Fin b, (B j).length := by
  classical
  let edges (j : Fin b) : Finset (Finset (Fin N)) :=
    Finset.univ.image fun i : Fin (B j).length ↦
      {(B j).get i, (B j).get (finRotate (B j).length i)}
  have hne (j : Fin b) (i : Fin (B j).length) :
      (B j).get i ≠ (B j).get (finRotate (B j).length i) := by
    intro h
    have hi := (hB.1 j).1.injective_get h
    apply finRotate_twice_ne_g9 (hB.1 j).2 i
    exact hi.trans (congrArg (finRotate (B j).length) hi)
  have hunion : (simplices K 1).filter (fun e ↦ incidence K e = 1) =
      Finset.univ.biUnion edges := by
    ext e
    constructor
    · intro he
      have he' : (e ∈ K.faces ∧ e.card = 2) ∧ incidence K e = 1 := by
        simpa [simplices] using he
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he'.1.2
      obtain ⟨j, i, h | h⟩ := (hB.2.2 u v).mp ⟨huv, he'.1.1, he'.2⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [h.1, h.2]⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [h.1, h.2, Finset.pair_comm]⟩
    · intro he
      obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      have hc : cycleEdge (B j) ((B j).get i) ((B j).get (finRotate (B j).length i)) :=
        ⟨i, Or.inl ⟨rfl, rfl⟩⟩
      have hb := (hB.2.2 _ _).mpr ⟨j, hc⟩
      simp only [Finset.mem_filter, simplices, Finset.mem_univ, true_and]
      exact ⟨⟨hb.2.1, Finset.card_pair (hne j i)⟩, hb.2.2⟩
  have hdisj : (↑(Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint edges := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp he
    obtain ⟨r, hr, her⟩ := Finset.mem_image.mp hf
    have hmem : (B j).get i ∈
        ({(B k).get r, (B k).get (finRotate (B k).length r)} : Finset (Fin N)) := by
      rw [her, ← hei]
      simp
    have hmemk : (B j).get i ∈ (B k).toFinset := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h <;> rw [h] <;> simp
    exact Finset.disjoint_left.mp (hB.2.1 j k hjk) (by simp) hmemk
  rw [hunion, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro j hj
  exact cycle_edge_pair_card_g9 (B j) (hB.1 j).1 (hB.1 j).2

end HolomorphicAnosov.Topology.GallierXu
