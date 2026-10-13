import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue

open Set Metric
namespace HolomorphicAnosov.Topology

/-- The intersection of a convex domain with a ball is the component on the
inside of the sphere through any of its points. This is the component-selection
step in Conway, Functions of One Complex Variable II, Chapter 14, Theorem 5.5,
p.50, expanded in the source disk in the short-cap argument.

The convex intersection is preconnected and lies in the complement of the sphere,
so component maximality gives one inclusion. If its component reached outside the
ball, continuity of distance and the intermediate value theorem would force a
point of that component onto the removed sphere, a contradiction. The argument
requires no regularity of the remaining components. -/
theorem convex_cap_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : Convex ℝ U) (c : E) (r : ℝ)
    (x : E) (hx : x ∈ U ∩ ball c r) :
    connectedComponentIn (U \ sphere c r) x = U ∩ ball c r := by
  have hsub : U ∩ ball c r ⊆ U \ sphere c r := by
    intro z hz
    exact ⟨hz.1, fun hzs ↦ (ne_of_lt hz.2) (mem_sphere.mp hzs)⟩
  apply Subset.antisymm
  · intro y hy
    have hyU := connectedComponentIn_subset (U \ sphere c r) x hy
    refine ⟨hyU.1, ?_⟩
    by_contra h
    have hdist : r ≤ dist y c := le_of_not_gt h
    have hc := (isConnected_connectedComponentIn_iff.mpr (hsub hx)).isPreconnected
    have him := hc.image (fun z ↦ dist z c)
      (continuous_id.dist continuous_const).continuousOn
    obtain ⟨z, hz, hzr⟩ := him.Icc_subset
      ⟨x, mem_connectedComponentIn (hsub hx), rfl⟩ ⟨y, hy, rfl⟩
      (show r ∈ Icc (dist x c) (dist y c) from ⟨hx.2.le, hdist⟩)
    exact (connectedComponentIn_subset (U \ sphere c r) x hz).2
      (mem_sphere.mpr hzr)
  · exact (hU.inter (convex_ball c r)).isPreconnected.subset_connectedComponentIn hx hsub

end HolomorphicAnosov.Topology
