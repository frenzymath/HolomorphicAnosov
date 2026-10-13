import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov.RelativeTriangleRealization
universe u

/-- Every ordered triangle point is an interior point, an interior face point,
or a vertex. Source: Hatcher pp.103–104, the simplex and its faces. This scratch
spells out the coordinate argument: if a weight vanishes, the simplex lies in
the corresponding face by Mathlib's range-of-map criterion. If both face
weights are positive it is an interior face point; otherwise one is zero and
the other is one, giving a vertex. -/
theorem triangle_strata (t : Simplex 2) :
    t ∈ interior 2 ∨ (∃ j s, s ∈ interior 1 ∧ t = face j s) ∨
      ∃ j, t = Convexity.StdSimplex.single j := by
  by_cases hi : t ∈ interior 2
  · exact Or.inl hi
  right
  obtain ⟨j,hj⟩ : ∃ j, t.weights j = 0 := by
    change ¬ ∀ j, 0 < t.weights j at hi
    push Not at hi
    obtain ⟨j,hj⟩ := hi
    exact ⟨j, le_antisymm hj (t.nonneg j)⟩
  obtain ⟨s,hs⟩ := (Convexity.StdSimplex.mem_range_map_iff j.succAbove t).mpr (by
    intro k hk
    have hkj : k = j := by simpa only [Fin.range_succAbove, mem_compl_iff,
      mem_singleton_iff, not_not] using hk
    simpa only [hkj] using hj)
  change face j s = t at hs
  by_cases his : s ∈ interior 1
  · exact Or.inl ⟨j,s,his,hs.symm⟩
  right
  obtain ⟨k,hk⟩ : ∃ k : Fin 2, s = Convexity.StdSimplex.single k := by
    change ¬ ∀ k, 0 < s.weights k at his
    push Not at his
    obtain ⟨k,hk⟩ := his
    have hz : s.weights k = 0 := le_antisymm hk (s.nonneg k)
    have htotal := s.total_fin_two
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one] at hz
    · have h1 : s.weights 1 = 1 := by simpa only [hz, zero_add] using htotal
      refine ⟨1, ?_⟩
      ext l
      fin_cases l <;> simp [hz,h1]
    · have h0 : s.weights 0 = 1 := by simpa only [hz, add_zero] using htotal
      refine ⟨0, ?_⟩
      ext l
      fin_cases l <;> simp [hz,h0]
  refine ⟨j.succAbove k, ?_⟩
  rw [← hs, hk]
  exact Convexity.StdSimplex.map_single k j.succAbove

end HolomorphicAnosov.RelativeTriangleRealization
