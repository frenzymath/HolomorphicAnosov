import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.UniformSpace.HeineCantor

open Filter _root_.Topology
open scoped ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- Wells's finite-head/tail uniform estimate for a continuous map along a null sequence.
Source: Wells (1976), p.288, the choices of `δ`, `N`, and `δ'` following equation (1).
The null sequence together with its limit zero is compact. Continuity at its points
therefore gives one radius controlling the variation from every sequence entry,
including perturbations outside the sequence range. This is precisely the compact-set
form of the source's finite-head/tail argument. -/
theorem null_sequence_uniform_continuity
    {E F : Type*} [NormedAddCommGroup E] [PseudoMetricSpace F]
    (a : ℕ → E) (ha : Tendsto a atTop (𝓝 0)) (f : E → F)
    (hf0 : ContinuousAt f 0) (hfa : ∀ n, ContinuousAt f (a n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n y, dist y (a n) < δ → dist (f y) (f (a n)) < ε := by
  have hf : ∀ x ∈ insert 0 (Set.range a), ContinuousAt f x := by
    intro x hx
    rcases hx with rfl | ⟨n, rfl⟩
    · exact hf0
    · exact hfa n
  have hu := ha.isCompact_insert_range.uniformContinuousAt_of_continuousAt f hf
    (Metric.uniformity_basis_dist.mem_of_mem hε)
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformity_basis_dist.mem_iff.mp hu
  refine ⟨δ, hδ, fun n y hy ↦ ?_⟩
  have hh := hbound (show (a n, y) ∈ {p : E × E | dist p.1 p.2 < δ} by
    simpa only [Set.mem_ofPred_eq, dist_comm] using hy)
    (Set.mem_insert_of_mem 0 (Set.mem_range_self n))
  simpa only [Set.mem_ofPred_eq, dist_comm] using hh

end HolomorphicAnosov.Analysis

