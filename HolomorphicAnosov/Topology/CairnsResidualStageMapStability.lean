import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- All later Cairns maps agree on an earlier closed stage and on the original
curve. Source: Cairns (1951), §4(B,C), pp.864–865, recurrent Hypothesis (5).
Induct on the later index. Source-region monotonicity keeps the point in each
later closed region, and the successor-map identity preserves its image. -/
theorem cairns_residual_stage_map_stable
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) {j n : ℕ} (hjn : j ≤ n) {z : ℂ}
    (hz : z ∈ closure (d.stages j).region ∪ range σ) :
    (d.stages n).map z = (d.stages j).map z := by
  obtain ⟨hA, _, _, hmap⟩ := cairns_residual_star_recurrence_properties d
  induction n, hjn using Nat.le_induction with
  | base => rfl
  | succ n hjn ih =>
      have hzn : z ∈ closure (d.stages n).region ∪ range σ :=
        (union_subset_union (closure_mono (hA hjn)) (Subset.refl _)) hz
      exact (hmap n z hzn).trans ih

/-- Every literal recurrence map retains the prescribed boundary map, without
assuming that its stage is already a cell or that the map is a homeomorphism.
Source: Cairns (1951), §4(B,C), pp.864–865. The initial map equals the given map
on the curve by its first defining branch; compatibility with stage zero then
propagates this identity to every later stage. -/
theorem cairns_residual_stage_map_boundary
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) (n : ℕ) {z : ℂ} (hz : z ∈ range σ) :
    (d.stages n).map z = (h ⟨z, hz⟩ : ℂ) := by
  rw [cairns_residual_stage_map_stable d (Nat.zero_le n) (Or.inr hz), d.start_eq]
  simp only [InitialData.stage, dite_eq_left hz]

end HolomorphicAnosov.Topology.Plane

