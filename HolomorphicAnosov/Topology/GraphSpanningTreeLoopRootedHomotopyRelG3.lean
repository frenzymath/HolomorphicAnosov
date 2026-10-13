import HolomorphicAnosov.Topology.GraphSpanningTreeLoopRootedContractionG3

namespace HolomorphicAnosov

open _root_.Topology

/-- Package carrier contraction data as the root-relative homotopy required by
based quotient descent.

Source: Hatcher, *Algebraic Topology*, Propositions 0.16--0.17, pp.15--16.
The carrier contraction supplies the endpoint and root equations; subtype
restriction is continuous because the contraction remains in the carrier.
-/
def graph_spanning_tree_loop_rooted_homotopy_rel_g3
    {X : Type*} [TopologicalSpace X]
    (T : Set X) (r0 : T)
    (H : C(unitInterval × T, X))
    (h0 : ∀ x, H (0, x) = x.val)
    (h1 : ∀ x, H (1, x) = r0.val)
    (hr : ∀ t, H (t, r0) = r0.val)
    (hmem : ∀ q, H q ∈ T) :
    ContinuousMap.HomotopyRel (ContinuousMap.id T)
      (ContinuousMap.const T r0) (Set.singleton r0) := by
  let H' : C(unitInterval × T, T) :=
    ⟨fun q ↦ ⟨H q, hmem q⟩, H.continuous.subtype_mk hmem⟩
  exact {
    toContinuousMap := H'
    map_zero_left := by
      intro x
      apply Subtype.ext
      exact h0 x
    map_one_left := by
      intro x
      apply Subtype.ext
      exact h1 x
    prop' := by
      intro t x hx
      have hx' : x = r0 := Set.mem_singleton_iff.mp hx
      subst x
      apply Subtype.ext
      exact hr t }

end HolomorphicAnosov
