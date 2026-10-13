import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import Mathlib.Combinatorics.Enumerative.DoubleCounting

open scoped BigOperators
namespace HolomorphicAnosov.Topology.GallierXu

/-- Counting pairs consisting of an original triangle and one of its edges gives
three incidences per triangle. This is the finite incidence count in the
Gallier--Xu polygon presentation, Definition 6.1, pp.79–81. -/
theorem sum_edge_incidence_g9 {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) :
    ∑ e ∈ simplices K 1, incidence K e = 3 * (simplices K 2).card := by
  classical
  have hedge (t : Finset (Fin N)) (ht : t ∈ simplices K 2) :
      ((simplices K 1).filter fun e ↦ e ⊆ t) = t.powersetCard 2 := by
    have ht' : t ∈ K.faces ∧ t.card = 3 := by simpa [simplices] using ht
    ext e
    simp only [Finset.mem_filter, simplices, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨he, hcard⟩, hsub⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      have hne : e.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨⟨(K.isRelLowerSet_faces ht'.1).2 hsub hne, hcard⟩, hsub⟩
  calc
    ∑ e ∈ simplices K 1, incidence K e =
        ∑ t ∈ simplices K 2, ((simplices K 1).filter fun e ↦ e ⊆ t).card := by
      simpa only [incidence, Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := simplices K 1) (t := simplices K 2) (fun e t ↦ e ⊆ t))
    _ = ∑ t ∈ simplices K 2, 3 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hedge t ht, Finset.card_powersetCard]
      have ht' : t.card = 3 := (by simpa [simplices] using ht : t ∈ K.faces ∧ t.card = 3).2
      rw [ht']
      decide
    _ = 3 * (simplices K 2).card := by simp [Nat.mul_comm]

end HolomorphicAnosov.Topology.GallierXu

