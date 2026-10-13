import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen

/-!
# Connected complements of complementary components

Conway, Functions of One Complex Variable II, Chapter 13, Proposition 1.1
and Corollary 1.2, pp.1–2, component closure and connected-union argument;
Chapter 14, Lemma 5.4, p.49, its application to path complements.
-/

open Set
namespace HolomorphicAnosov.Topology

/-- In a connected locally connected space, each complementary component of a
nonempty closed connected set has connected complement.

Source: Conway II, Chapter 13 Proposition 1.1 and Corollary 1.2, pp.1–2;
the component argument used in Chapter 14 Lemma 5.4, p.49.
Proof: components of the open complement are open. The closure of each is
contained in that component together with the closed set, since every other
component is an open neighborhood disjoint from it. Each closure meets the
closed set: otherwise the component is also closed, hence is the whole
connected ambient space, contradicting nonemptiness of the closed set.
Thus adjoining any complementary component to the closed connected set gives
a connected set. The complement of one fixed component is the union of these
connected sets for all other components, with the original closed set common
to them. If the marked point belongs to the closed set, its complement
component is empty and the conclusion is connectedness of the ambient space.
-/
theorem connected_complement_component
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {T : Set X} (hclosed : IsClosed T) (hT : IsConnected T) (x : X) :
    IsConnected (connectedComponentIn Tᶜ x)ᶜ := by
  classical
  have hclosure (z : X) : closure (connectedComponentIn Tᶜ z) ⊆
      connectedComponentIn Tᶜ z ∪ T := by
    intro y hy
    by_cases hyT : y ∈ T
    · exact Or.inr hyT
    · have hO := hclosed.isOpen_compl.connectedComponentIn (x := y)
      obtain ⟨w, hwO, hwz⟩ := mem_closure_iff.mp hy _ hO (mem_connectedComponentIn hyT)
      have heq : connectedComponentIn Tᶜ z = connectedComponentIn Tᶜ y :=
        (connectedComponentIn_eq hwz).trans (connectedComponentIn_eq hwO).symm
      exact Or.inl (heq ▸ mem_connectedComponentIn hyT)
  have htouch (z : X) (hz : z ∉ T) :
      (T ∩ closure (connectedComponentIn Tᶜ z)).Nonempty := by
    by_contra hn
    have hsub : closure (connectedComponentIn Tᶜ z) ⊆ connectedComponentIn Tᶜ z := by
      intro y hy
      rcases hclosure z hy with hyz | hyT
      · exact hyz
      · exact False.elim (hn ⟨y, hyT, hy⟩)
    have hc : IsClosed (connectedComponentIn Tᶜ z) :=
      closure_subset_iff_isClosed.mp hsub
    have heq : connectedComponentIn Tᶜ z = univ :=
      (show IsClopen (connectedComponentIn Tᶜ z) from
        ⟨hc, hclosed.isOpen_compl.connectedComponentIn⟩).eq_univ
          ⟨z, mem_connectedComponentIn hz⟩
    obtain ⟨a, ha⟩ := hT.nonempty
    exact (connectedComponentIn_subset Tᶜ z (heq.symm ▸ mem_univ a)) ha
  have hunion (z : X) (hz : z ∉ T) : IsConnected (T ∪ connectedComponentIn Tᶜ z) := by
    have hc := hT.union (htouch z hz) (isConnected_connectedComponentIn_iff.mpr hz).closure
    have heq : T ∪ closure (connectedComponentIn Tᶜ z) = T ∪ connectedComponentIn Tᶜ z := by
      apply subset_antisymm
      · intro y hy
        rcases hy with hy | hy
        · exact Or.inl hy
        · rcases hclosure z hy with hy | hy
          · exact Or.inr hy
          · exact Or.inl hy
      · exact union_subset_union_right T subset_closure
    rwa [heq] at hc
  obtain ⟨a, ha⟩ := hT.nonempty
  have hTsub : T ⊆ (connectedComponentIn Tᶜ x)ᶜ := by
    intro z hz hzx
    exact (connectedComponentIn_subset Tᶜ x hzx) hz
  refine ⟨⟨a, hTsub ha⟩, isPreconnected_of_forall a ?_⟩
  intro z hz
  by_cases hzT : z ∈ T
  · exact ⟨T, hTsub, ha, hzT, hT.isPreconnected⟩
  · refine ⟨T ∪ connectedComponentIn Tᶜ z, ?_, Or.inl ha,
      Or.inr (mem_connectedComponentIn hzT), (hunion z hzT).isPreconnected⟩
    intro y hy hyx
    rcases hy with hy | hy
    · exact hTsub hy hyx
    · have heq : connectedComponentIn Tᶜ z = connectedComponentIn Tᶜ x :=
        (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hyx).symm
      exact hz (heq ▸ mem_connectedComponentIn hzT)

end HolomorphicAnosov.Topology

