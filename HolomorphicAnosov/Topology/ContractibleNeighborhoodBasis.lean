import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.LocallyPathConnected

namespace HolomorphicAnosov

universe u

/-- An open contractible-neighborhood basis gives a locally path-connected space. -/
theorem locallyPathConnected_of_contractible_neighborhoods
    {X : Type u} [TopologicalSpace X]
    (h : ∀ (x : X) (O : Set X), IsOpen O → x ∈ O →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ContractibleSpace V) :
    LocallyPathConnectedSpace X := by
  refine ⟨fun x ↦ Filter.hasBasis_self.mpr ?_⟩
  intro O hO
  obtain ⟨U, hUO, hU, hxU⟩ := mem_nhds_iff.mp hO
  obtain ⟨V, hV, hxV, hVU, hcontract⟩ := h x U hU hxU
  have : ContractibleSpace V := hcontract
  exact ⟨V, hV.mem_nhds hxV, isPathConnected_iff_pathConnectedSpace.mpr inferInstance,
    hVU.trans hUO⟩

end HolomorphicAnosov
