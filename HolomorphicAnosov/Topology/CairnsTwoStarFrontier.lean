import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

namespace HolomorphicAnosov.Topology.Plane
open Set

/-- The initial Cairns seam disappears from the frontier when two star regions
are joined along their common open base. Source: Cairns (1951), §4(B), p.864.
Each star frontier is its closed base together with its outer front. The closed
base is already in each star closure, so adjoining the open base does not add
closure points beyond the two star closures. The resulting closure is therefore
the joined region together with the two fronts: every base point not on the
open seam is one of the endpoints, which are on the fronts. If the joined
region is open and avoids the fronts, subtracting it from its closure gives
exactly those fronts. The hypotheses explicitly retain the geometric work:
seam openness and front avoidance must come from the two opposite star collars,
and are not consequences of arbitrary frontier formulas alone. -/
theorem cairns_two_star_frontier
    (U V L M : Set ℂ) (p q : ℂ)
    (hU : frontier U = segment ℝ p q ∪ L)
    (hV : frontier V = segment ℝ p q ∪ M)
    (hp : p ∈ L ∪ M) (hq : q ∈ L ∪ M)
    (hopen : IsOpen (U ∪ V ∪ openSegment ℝ p q))
    (havoid : Disjoint (L ∪ M) (U ∪ V ∪ openSegment ℝ p q)) :
    closure (U ∪ V ∪ openSegment ℝ p q) = closure U ∪ closure V ∧
      frontier (U ∪ V ∪ openSegment ℝ p q) = L ∪ M := by
  have hbase : segment ℝ p q ⊆ closure U := by
    intro z hz
    exact frontier_subset_closure (hU.symm ▸ Or.inl hz)
  have hcl : closure (U ∪ V ∪ openSegment ℝ p q) = closure U ∪ closure V := by
    apply Subset.antisymm
    · apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      rintro z ((hz | hz) | hz)
      · exact Or.inl (subset_closure hz)
      · exact Or.inr (subset_closure hz)
      · exact Or.inl (hbase (openSegment_subset_segment ℝ p q hz))
    · exact union_subset (closure_mono (fun z hz ↦ Or.inl (Or.inl hz)))
        (closure_mono (fun z hz ↦ Or.inl (Or.inr hz)))
  refine ⟨hcl, ?_⟩
  rw [hopen.frontier_eq, hcl, closure_eq_self_union_frontier U,
    closure_eq_self_union_frontier V, hU, hV]
  ext z
  constructor
  · rintro ⟨hz, hznot⟩
    have hbase_or : z ∈ segment ℝ p q ∨ z ∈ L ∪ M := by
      rcases hz with (hz | hz) | (hz | hz)
      · exact False.elim (hznot (Or.inl (Or.inl hz)))
      · rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
      · exact False.elim (hznot (Or.inl (Or.inr hz)))
      · rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz)
    rcases hbase_or with hz | hz
    · by_cases hzp : z = p
      · exact hzp ▸ hp
      by_cases hzq : z = q
      · exact hzq ▸ hq
      exact False.elim (hznot (Or.inr
        (mem_openSegment_of_ne_left_right (Ne.symm hzp) (Ne.symm hzq) hz)))
    · exact hz
  · intro hz
    refine ⟨?_, fun hr ↦ Set.disjoint_left.mp havoid hz hr⟩
    rcases hz with hz | hz
    · exact Or.inl (Or.inr (Or.inr hz))
    · exact Or.inr (Or.inr (Or.inr hz))

end HolomorphicAnosov.Topology.Plane
