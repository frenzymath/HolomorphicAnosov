import HolomorphicAnosov.Topology.RoundDiskBoundaryComponent
import Mathlib.Topology.Connected.Clopen

/-!
# Constancy of the component incident to an unobstructed circle arc

This proves the collar-component constancy used in Cairns (1951), Lemma 5.1,
printed p.866, for any preconnected subset of the unit circle avoiding a closed
obstacle. DAG node: `topo.round_disk_boundary_component_constancy_g18`.
-/

open Set Metric

namespace HolomorphicAnosov

/-- The component of the open disk minus a closed obstacle incident to an
unobstructed boundary point is constant along any preconnected part of the circle
avoiding that obstacle.

Source: the collar step in Cairns, *An Elementary Proof of the Jordan-Schoenflies
Theorem* (1951), Lemma 5.1, p.866. The source does not state this closed-obstacle
generalization separately; the following is an agent-written expansion.

Fix the component incident at `a`. Among points of `S`, belonging to its closure
is a closed condition. At each such point the boundary-component theorem gives
an inward cap contained in this same component. Every nearby circle point is in
the closure of the cap, so the condition is also open in `S`. It is nonempty,
since it holds at `a`; preconnectedness therefore makes it hold everywhere.
Uniqueness of the incident component at `b` gives the equality. The statement
requires no arc parametrization, accessibility of the obstacle, or separation
theorem, and applies to disconnected obstacles and singleton `S`.
-/
theorem roundDisk_boundary_component_constancy
    {K S : Set ℂ} (hK : IsClosed K) (hS : IsPreconnected S)
    (hSK : S ⊆ sphere (0 : ℂ) 1 \ K)
    {a b x y : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hx : x ∈ ball (0 : ℂ) 1 \ K) (hy : y ∈ ball (0 : ℂ) 1 \ K)
    (hax : a ∈ closure (connectedComponentIn (ball (0 : ℂ) 1 \ K) x))
    (hby : b ∈ closure (connectedComponentIn (ball (0 : ℂ) 1 \ K) y)) :
    connectedComponentIn (ball (0 : ℂ) 1 \ K) x =
      connectedComponentIn (ball (0 : ℂ) 1 \ K) y := by
  let Ω := ball (0 : ℂ) 1 \ K
  let T : Set S := Subtype.val ⁻¹' closure (connectedComponentIn Ω x)
  have hTc : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have hTo : IsOpen T := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε, hε, _, w, _, hcap, _, huniq⟩ :=
      roundDisk_boundary_component hK (hSK z.property).1 (hSK z.property).2
    have hcomp : connectedComponentIn Ω x = connectedComponentIn Ω w :=
      huniq x hx hz
    refine ⟨ε, hε, ?_⟩
    intro t ht
    change (t : ℂ) ∈ closure (connectedComponentIn Ω x)
    rw [hcomp]
    apply closure_mono hcap
    apply isOpen_ball.inter_closure
    refine ⟨ht, ?_⟩
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall (hSK t.property).1
  have : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hT : T = univ := (show IsClopen T from ⟨hTc, hTo⟩).eq_univ ⟨⟨a, ha⟩, hax⟩
  have hbx : b ∈ closure (connectedComponentIn Ω x) := by
    have ht : (⟨b, hb⟩ : S) ∈ T := by rw [hT]; trivial
    exact ht
  obtain ⟨_, _, _, w, _, _, _, huniq⟩ :=
    roundDisk_boundary_component hK (hSK hb).1 (hSK hb).2
  exact (huniq x hx hbx).trans (huniq y hy hby).symm

end HolomorphicAnosov

