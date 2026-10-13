import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace HolomorphicAnosov

universe u

/-- A loop in a contractible subset is null-homotopic after inclusion into the ambient space. -/
theorem loop_nullhomotopic_of_contractible_subset
    {X : Type u} [TopologicalSpace X] {V : Set X} [ContractibleSpace V]
    {x : X} (hx : x ∈ V) (γ : Path x x) (hγ : Set.range γ ⊆ V) :
    γ.Homotopic (Path.refl x) := by
  let γV : Path (⟨x, hx⟩ : V) ⟨x, hx⟩ :=
    { toFun := fun t ↦ ⟨γ t, hγ ⟨t, rfl⟩⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have h := (SimplyConnectedSpace.paths_homotopic γV (Path.refl (⟨x, hx⟩ : V))).map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))
  have hmap : γV.map continuous_subtype_val = γ := by ext t; rfl
  have hrefl : (Path.refl (⟨x, hx⟩ : V)).map continuous_subtype_val = Path.refl x := by
    ext t
    rfl
  simpa only [hmap, hrefl] using h

end HolomorphicAnosov
