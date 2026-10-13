import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

open Set Filter Metric
open scoped Topology
namespace HolomorphicAnosov

/-- Local bounds propagate across an open connected domain when a point bound
propagates to each compact subset of every contained disk. Agent-written
expansion of the local-to-global step of Conway II XVI Theorem 4.2 p.124 by an
open-and-closed argument. The locus of locally uniformly bounded points is open.
At a limit point, a contained disk meets that locus; its bounded point propagates
to a smaller closed disk around the limit point. Thus the locus is relatively
closed. Connectedness and the initial bounded point make it the whole domain;
a finite subcover gives the bound on each compact subset. -/
theorem conway_connected_compact_bound_g7 {G : Set ℂ}
    (hG : IsOpen G) (hc : IsPreconnected G) (f : ℕ → ℂ → ℂ)
    (hlocal : ∀ (x : ℂ) (r : ℝ), 0 < r → ball x r ⊆ G →
      ∀ a ∈ ball x r, (∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖f n a‖ ≤ M) →
      ∀ K : Set ℂ, IsCompact K → K ⊆ ball x r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖f n z‖ ≤ M)
    {a : ℂ} (ha : a ∈ G) (haB : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖f n a‖ ≤ M) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖f n z‖ ≤ M := by
  classical
  let U : Set ℂ := {x | ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ V → ‖f n z‖ ≤ M}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨V, hVo, hxV, M, hM, hbound⟩
    exact mem_of_superset (hVo.mem_nhds hxV) (fun y hy ↦ ⟨V, hVo, hy, M, hM, hbound⟩)
  have hnear (x : ℂ) (hx : x ∈ G) : ∃ r : ℝ, 0 < r ∧ ball x r ⊆ G :=
    Metric.mem_nhds_iff.mp (hG.mem_nhds hx)
  have hpush (x : ℂ) (r : ℝ) (hr : 0 < r) (hrG : ball x r ⊆ G)
      (y : ℂ) (hy : y ∈ ball x r)
      (hyB : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖f n y‖ ≤ M) : x ∈ U := by
    obtain ⟨M, hM, hbound⟩ := hlocal x r hr hrG y hy hyB (closedBall x (r/2))
      (isCompact_closedBall _ _) (closedBall_subset_ball (by linarith))
    exact ⟨ball x (r/2), isOpen_ball, mem_ball_self (by positivity), M, hM,
      fun n z hz ↦ hbound n z (ball_subset_closedBall hz)⟩
  have haU : a ∈ U := by
    obtain ⟨r, hr, hrG⟩ := hnear a ha
    exact hpush a r hr hrG a (mem_ball_self hr) haB
  have hclosed : closure U ∩ G ⊆ U := by
    rintro x ⟨hxU, hxG⟩
    obtain ⟨r, hr, hrG⟩ := hnear x hxG
    obtain ⟨y, hyball, hyU⟩ := (mem_closure_iff_nhds.mp hxU) (ball x r)
      (isOpen_ball.mem_nhds (mem_ball_self hr))
    obtain ⟨V, _, hyV, M, hM, hbound⟩ := hyU
    exact hpush x r hr hrG y hyball ⟨M, hM, fun n ↦ hbound n y hyV⟩
  have hGU : G ⊆ U := hc.subset_of_closure_inter_subset hU ⟨a, ha, haU⟩ hclosed
  intro K hK hKG
  have hchoices : ∀ x : K, ∃ V : Set ℂ, IsOpen V ∧ (x : ℂ) ∈ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ V → ‖f n z‖ ≤ M :=
    fun x ↦ hGU (hKG x.property)
  choose V hVo hxV M hM hb using hchoices
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hVo (by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩)
  refine ⟨∑ x ∈ s, M x, Finset.sum_nonneg (fun x hx ↦ hM x), ?_⟩
  intro n z hz
  obtain ⟨x, hx, hzV⟩ := mem_iUnion₂.mp (hs hz)
  exact (hb x n z hzV).trans (Finset.single_le_sum (fun y hy ↦ hM y) hx)

end HolomorphicAnosov
