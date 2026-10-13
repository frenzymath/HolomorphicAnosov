import HolomorphicAnosov.Topology.Cubical.CellCarrierSubsetSkeleton
import Mathlib.Tactic

namespace HolomorphicAnosov.Cubical

/-- A boundary point of a coordinate (q+1)-cell lies in the q-skeleton.
Source: Hatcher, Algebraic Topology, Appendix A.2 p.521 and Lemma 2.34 p.137.
Choose an active coordinate at which the point is an endpoint, and collapse
that interval to the chosen endpoint. This is a face belonging to the same
subdivision, contains the point, and has strictly fewer active coordinates.
Its dimension is therefore at most q, so its carrier lies in the q-skeleton. -/
theorem cell_boundary_subset_skeleton {N : ℕ}
    (K : FiniteRectilinearSubdivision N) (q : ℕ)
    (c : ClosedCoordinateCell N) (hc : c ∈ K.cells) (hd : c.dimension = q + 1) :
    {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
      c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)} ⊆ K.skeleton q := by
  classical
  rintro x ⟨hx, i, hi, hxi⟩
  let a : ClosedCoordinateCell N :=
    ⟨Function.update c.lower i (x i), Function.update c.upper i (x i), by
      intro j
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]
        exact c.lower_le_upper j⟩
  have haface : ClosedCoordinateCell.IsFace a c := by
    intro j
    by_cases hji : j = i
    · subst j
      rcases hxi with hxi | hxi
      · exact Or.inr (Or.inl (by simpa [a] using And.intro hxi hxi))
      · exact Or.inr (Or.inr (by simpa [a] using And.intro hxi hxi))
    · exact Or.inl (by simp [a, Function.update_of_ne hji])
  have hxa : x ∈ a.carrier := by
    constructor <;> intro j <;> by_cases hji : j = i
    · subst j; simp [a]
    · simpa [a, Function.update_of_ne hji] using hx.1 j
    · subst j; simp [a]
    · simpa [a, Function.update_of_ne hji] using hx.2 j
  have hdim : a.dimension < c.dimension := by
    apply Set.ncard_lt_ncard
    · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j; simp [a] at hj
        · simpa [a, Function.update_of_ne hji] using hj
      · intro heq
        have : a.lower i < a.upper i := by
          change i ∈ {j | a.lower j < a.upper j}
          rw [heq]
          exact hi
        simp [a] at this
    · exact Set.toFinite _
  exact cell_carrier_subset_skeleton K q a (K.faces c hc a haface)
    (by omega) hxa

end HolomorphicAnosov.Cubical
