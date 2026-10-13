import HolomorphicAnosov.Topology.TriangleIncidenceCountG9

open scoped BigOperators
namespace HolomorphicAnosov.Topology.GallierXu

/-- A surface whose edges have one or two incident triangles satisfies the
finite incidence identity `3F + E_boundary = 2E`. -/
theorem surface_edge_incidence_count_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2) :
    3 * (simplices K 2).card +
      ((simplices K 1).filter fun e ↦ incidence K e = 1).card =
        2 * (simplices K 1).card := by
  classical
  rw [← sum_edge_incidence_g9]
  have hb : ((simplices K 1).filter fun e ↦ incidence K e = 1).card =
      ∑ e ∈ simplices K 1, if incidence K e = 1 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hb, ← Finset.sum_add_distrib]
  calc
    (∑ e ∈ simplices K 1, (incidence K e + if incidence K e = 1 then 1 else 0)) =
        ∑ e ∈ simplices K 1, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rcases hincidence e he with h | h <;> simp [h]
    _ = 2 * (simplices K 1).card := by simp [Nat.mul_comm]

end HolomorphicAnosov.Topology.GallierXu

