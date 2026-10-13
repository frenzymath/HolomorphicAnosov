import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic

/-!
# Compact local upper bounds

This is the elementary finite-subcover argument used to turn local eventual
upper bounds into one global positive upper bound on a compact space.
-/

noncomputable section

open Filter Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A locally eventual upper bound on a compact space has one positive global
upper bound. The positive padding also covers an empty space. -/
theorem compact_local_upper_bound (b : X → ℝ)
    (hb : ∀ x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x, b y ≤ q) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, b x ≤ R := by
  classical
  choose q hq using hb
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun x ↦ {y | b y ≤ q x}) hq
  obtain ⟨R, hR⟩ := (t.finite_toSet.image q).bddAbove
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x ↦ ?_⟩
  have hx : x ∈ ⋃ z ∈ t, {y | b y ≤ q z} := by rw [ht]; trivial
  obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp hx
  exact hzx.trans ((hR ⟨z, hz, rfl⟩).trans (le_max_right _ _))

end HolomorphicAnosov
