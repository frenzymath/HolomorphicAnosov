import HolomorphicAnosov.Topology.ConvexHullApexComponentClosure
import Mathlib.Analysis.Normed.Module.Convex

open Set
namespace HolomorphicAnosov

/-- The interior of a cone hull, minus a closed convex set containing its base
and avoiding its apex, is connected when nonempty.

Source: Cairns (1951), §3 Case II, p.863, expanded here by component maximality.
Every component approaches the apex by the radial segment lemma. Choose a ball
about the apex disjoint from the removed closed set. The intersection of this
ball with the cone interior is convex. Every component meets that convex set,
so all components coincide. -/
theorem convexCone_complement_connected_g2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E) (S K : Set E) (hS : S.Nonempty) (hK : Convex ℝ K)
    (hKclosed : IsClosed K) (hM : M ∉ K) (hSK : S ⊆ K)
    (hne : (interior (convexHull ℝ (insert M S)) \ K).Nonempty) :
    IsConnected (interior (convexHull ℝ (insert M S)) \ K) := by
  let U := interior (convexHull ℝ (insert M S))
  let V := U \ K
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hKclosed.isOpen_compl.mem_nhds hM)
  let C := Metric.ball M ε ∩ U
  have hCpre : IsPreconnected C :=
    ((convex_ball M ε).inter (convex_convexHull ℝ _).interior).isPreconnected
  have hCV : C ⊆ V := fun _ hx ↦ ⟨hx.2,hball hx.1⟩
  have hmeet (x : E) (hx : x ∈ V) : (C ∩ connectedComponentIn V x).Nonempty := by
    have hcl := convexHull_apex_mem_closure_component M S K hS hK hSK hx
    obtain ⟨z,hz,hzε⟩ := Metric.mem_closure_iff.mp hcl ε hε
    exact ⟨z,⟨by simpa [Metric.mem_ball,dist_comm] using hzε,
      (connectedComponentIn_subset V x hz).1⟩,hz⟩
  obtain ⟨x,hx⟩ := hne
  obtain ⟨z,hzC,hzx⟩ := hmeet x hx
  have hCsub : C ⊆ connectedComponentIn V x := by
    rw [connectedComponentIn_eq hzx]
    exact hCpre.subset_connectedComponentIn hzC hCV
  have heq : connectedComponentIn V x = V := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro y hy
    obtain ⟨w,hwC,hwy⟩ := hmeet y hy
    rw [connectedComponentIn_eq (hCsub hwC), ← connectedComponentIn_eq hwy]
    exact mem_connectedComponentIn hy
  change IsConnected V
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr hx

end HolomorphicAnosov
