import Mathlib.Topology.Homeomorph.Defs

open scoped Topology
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Transport an injectively parametrized leaf to its literal original-point carrier. -/
theorem native_carrier_homeomorph_g15 {L : Type*} [TopologicalSpace L]
    {M : Type*} (ι : L → M) (hinj : Function.Injective ι) (S : Set M)
    (hrange : Set.range ι = S) :
    ∃ t : TopologicalSpace S, letI := t
      ∃ e : L ≃ₜ S, ∀ z : L, (e z).val = ι z := by
  let p : L → S := fun z ↦ ⟨ι z, hrange ▸ ⟨z, rfl⟩⟩
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro y
      have hy : y.val ∈ Set.range ι := hrange.symm ▸ y.property
      obtain ⟨z, hz⟩ := hy
      exact ⟨z, Subtype.ext hz⟩
  let e := Equiv.ofBijective p hp
  let t := (inferInstance : TopologicalSpace L).coinduced e
  refine ⟨t, ?_⟩
  let := t
  let h : L ≃ₜ S := e.toHomeomorph (fun _ ↦ isOpen_coinduced.symm)
  exact ⟨h, fun _ ↦ rfl⟩


end HolomorphicAnosov
