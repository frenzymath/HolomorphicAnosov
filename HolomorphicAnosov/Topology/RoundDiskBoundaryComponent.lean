import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Basic

/-!
# The component at an unobstructed circle point

This expands the collar-component selection in the round-disk reduction of
Cairns (1951), Lemma 5.1, p.866. It uses an arbitrary closed obstacle missing the
specified circle point; no separation theorem for an arc is assumed.
DAG node: `topo.round_disk_boundary_component_g6`.
-/

open Set Metric
namespace HolomorphicAnosov

/-- A circle point outside a closed obstacle lies on the frontier of exactly
one component of the open disk minus that obstacle. A sufficiently small inward
ball cap lies entirely in that component.

Proof: closedness gives a ball missing the obstacle. Its intersection with the
open disk is convex, and it is nonempty since the circle point lies in the
closure of the disk. Choose a point of this connected cap; component maximality
puts the whole cap in its component. The circle point is in the closure of the
cap, hence of the component, but outside the disk, hence on its frontier. If a
second component accumulates there, it meets the same ball; that intersection
point belongs to the cap and hence to both components. Intersecting components
are equal.

Source: elementary expansion of Cairns, Lemma 5.1, p.866, the round-disk collar
step. The printed source does not state this general closed-obstacle lemma;
its proof is the agent's direct Mathlib topology/convexity argument.
-/
theorem roundDisk_boundary_component {K : Set ℂ} (hK : IsClosed K)
    {a : ℂ} (ha : a ∈ sphere (0 : ℂ) 1) (haK : a ∉ K) :
    let Ω := ball (0 : ℂ) 1 \ K
    ∃ ε : ℝ, 0 < ε ∧ Disjoint (ball a ε) K ∧
      ∃ x : ℂ, x ∈ ball a ε ∩ ball (0 : ℂ) 1 ∧
        ball a ε ∩ ball (0 : ℂ) 1 ⊆ connectedComponentIn Ω x ∧
        a ∈ frontier (connectedComponentIn Ω x) ∧
        ∀ y ∈ Ω, a ∈ closure (connectedComponentIn Ω y) →
          connectedComponentIn Ω y = connectedComponentIn Ω x := by
  dsimp only
  obtain ⟨ε, hε, hmiss⟩ := Metric.isOpen_iff.mp hK.isOpen_compl a haK
  have hacl : a ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall ha
  have hacap : a ∈ closure (ball a ε ∩ ball (0 : ℂ) 1) :=
    isOpen_ball.inter_closure ⟨mem_ball_self hε, hacl⟩
  obtain ⟨x, hx⟩ := (_root_.mem_closure_iff.mp hacl)
    (ball a ε) isOpen_ball (mem_ball_self hε)
  have hsub : ball a ε ∩ ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) 1 \ K :=
    fun z hz ↦ ⟨hz.2, hmiss hz.1⟩
  have hcap := ((convex_ball a ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
    |>.subset_connectedComponentIn hx hsub
  refine ⟨ε, hε, disjoint_left.mpr (fun z hz hzK ↦ hmiss hz hzK), x, hx,
    hcap, ?_, ?_⟩
  · refine ⟨closure_mono hcap hacap, ?_⟩
    intro hai
    have hadisk := (connectedComponentIn_subset (ball (0 : ℂ) 1 \ K) x
      (interior_subset hai)).1
    exact Set.disjoint_left.mp sphere_disjoint_ball ha hadisk
  · intro y _ hay
    obtain ⟨z, hzball, hzcomp⟩ := (_root_.mem_closure_iff.mp hay)
      (ball a ε) isOpen_ball (mem_ball_self hε)
    have hzcap : z ∈ ball a ε ∩ ball (0 : ℂ) 1 :=
      ⟨hzball, (connectedComponentIn_subset _ _ hzcomp).1⟩
    exact (connectedComponentIn_eq hzcomp).trans (connectedComponentIn_eq (hcap hzcap)).symm

end HolomorphicAnosov

