import HolomorphicAnosov.Topology.CompactLocalUpperBound

noncomputable section
namespace HolomorphicAnosov
open Filter Set
open scoped Topology _root_.Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Finitely many original forward or inverse residual norms have one positive bound.
The index set may be empty and may be the disjoint union of the two finite residue sets. -/
theorem compact_finite_local_residue_bound {J : Type*} [Finite J] (b : J → X → ℝ)
    (hb : ∀ j x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x, b j y ≤ q) :
    ∃ R : ℝ, 0 < R ∧ ∀ j x, b j x ≤ R := by
  classical
  choose C hCpos hC using fun j ↦ HolomorphicAnosov.compact_local_upper_bound (b j) (hb j)
  obtain ⟨R, hR⟩ := Finite.bddAbove_range C
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun j x ↦ ?_⟩
  exact (hC j x).trans ((hR (mem_range_self j)).trans (le_max_right _ _))


end HolomorphicAnosov
