import Mathlib.Topology.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Iterate

namespace HolomorphicAnosov

open Set

/-- A bijection and its inverse have the same nonwandering points (Shub, Prop. 1.1). -/
theorem smale_nonwandering_inverse {X : Type*} [TopologicalSpace X] (e : X ≃ X) :
    {x | ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((e.symm : X → X)^[k]) '' U ∩ U).Nonempty} =
    {x | ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((e : X → X)^[k]) '' U ∩ U).Nonempty} := by
  ext x
  constructor
  · intro hx U hU hxU
    obtain ⟨k, hk, z, ⟨y, hy, rfl⟩, hz⟩ := hx U hU hxU
    refine ⟨k, hk, y, ⟨(e.symm : X → X)^[k] y, hz, ?_⟩, hy⟩
    exact Function.LeftInverse.iterate e.apply_symm_apply k y
  · intro hx U hU hxU
    obtain ⟨k, hk, z, ⟨y, hy, rfl⟩, hz⟩ := hx U hU hxU
    refine ⟨k, hk, y, ⟨(e : X → X)^[k] y, hz, ?_⟩, hy⟩
    exact Function.LeftInverse.iterate e.symm_apply_apply k y

end HolomorphicAnosov
