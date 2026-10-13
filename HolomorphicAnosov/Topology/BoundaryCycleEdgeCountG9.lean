import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

namespace HolomorphicAnosov.Topology.GallierXu

lemma finRotate_twice_ne_g9 {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : i ≠ finRotate n (finRotate n i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro h
  have hv := congrArg Fin.val h
  simp only [finRotate_apply, Fin.val_add_one] at hv
  split_ifs at hv <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> try omega
  have hi : i = 0 := Fin.ext hv
  subst i
  norm_num at *
  have hm : 1 < m + 1 := by omega
  simp only [Nat.mod_eq_of_lt hm] at *
  omega

/-- A simple cycle with at least three vertices has distinct unordered edges.
Gallier--Xu Definition 6.1 uses these original edges for the boundary contour. -/
theorem cycle_edge_pair_injective_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length) :
    Function.Injective (fun i : Fin l.length ↦
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N))) := by
  intro i j hij
  dsimp only at hij
  have hi : l.get i = l.get j ∨ l.get i = l.get (finRotate l.length j) := by
    have hm : l.get i ∈ ({l.get j, l.get (finRotate l.length j)} : Finset (Fin N)) := by
      rw [← hij]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hi' : l.get (finRotate l.length i) = l.get j ∨
      l.get (finRotate l.length i) = l.get (finRotate l.length j) := by
    have hm : l.get (finRotate l.length i) ∈
        ({l.get j, l.get (finRotate l.length j)} : Finset (Fin N)) := by
      rw [← hij]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hi with h | h
  · exact hnd.injective_get h
  · rcases hi' with h' | h'
    · have ha := hnd.injective_get h
      have hb := hnd.injective_get h'
      exact False.elim (finRotate_twice_ne_g9 hlen i (ha.trans (congrArg _ hb.symm)))
    · exact (finRotate l.length).injective (hnd.injective_get h')

/-- A simple cycle of at least three vertices has exactly its length many
unoriented edges; this is the edge count used when adjoining a cone cap. -/
theorem cycle_edge_pair_card_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length) :
    (Finset.univ.image (fun i : Fin l.length ↦
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)))).card = l.length := by
  rw [Finset.card_image_of_injective _ (cycle_edge_pair_injective_g9 l hnd hlen)]
  simp

end HolomorphicAnosov.Topology.GallierXu
