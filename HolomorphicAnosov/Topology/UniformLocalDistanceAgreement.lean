import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

open Set
namespace HolomorphicAnosov

/-- Local agreement with a distance on a compact metric space holds uniformly
for sufficiently close pairs. The second function need not itself be a metric.

Agent-written compactness step of the Hirsch–Pugh metric transfer. Choose the
given open agreement neighborhoods as an open cover. A Lebesgue number puts
every sufficiently small metric ball into one member of that cover. Its center
and every point at distance at most half the Lebesgue number are both in that
member, where the two functions agree. Empty spaces are included. -/
theorem uniform_local_distance_agreement
    {X : Type*} [inst : MetricSpace X] [CompactSpace X]
    (ρ : X → X → ℝ)
    (hlocal : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, dist y z = ρ y z) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y : X, dist x y ≤ r → dist x y = ρ x y := by
  classical
  choose V hopen hmem hagree using hlocal
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    isCompact_univ hopen (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro x y hxy
  obtain ⟨i, hi⟩ := hball x (mem_univ x)
  apply hagree i x (hi (Metric.mem_ball_self hδ)) y
  apply hi
  change dist y x < δ
  rw [dist_comm y x]
  linarith

end HolomorphicAnosov
