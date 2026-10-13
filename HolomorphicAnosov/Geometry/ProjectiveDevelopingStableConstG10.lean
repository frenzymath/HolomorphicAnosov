import Mathlib.Topology.Connected.Basic

namespace HolomorphicAnosov.Ghys

open Set _root_.Topology

universe u v w

/-- A projective developing map is constant on each class of a relation whose classes are connected
components of its fibres. -/
theorem projective_developing_eq_of_stable_link
    {E : Type u} {Z : Type v} [TopologicalSpace E]
    (D : E → Z) (R : E → E → Prop)
    (hslifts : ∀ x : E, ∃ (L : Type w) (lift : L → E),
      Set.range lift = {y : E | Relation.EqvGen R x y} ∧
      Set.range lift = connectedComponentIn (D ⁻¹' {D x}) x) :
    ∀ x y : E, Relation.EqvGen R x y → D x = D y := by
  intro x y hxy
  obtain ⟨L, lift, hrange, hcomponent⟩ := hslifts x
  have hy : y ∈ connectedComponentIn (D ⁻¹' {D x}) x := by
    rw [← hcomponent, hrange]
    exact hxy
  have hdy : D y = D x :=
    connectedComponentIn_subset (D ⁻¹' {D x}) x hy
  exact hdy.symm

end HolomorphicAnosov.Ghys
