import Mathlib.Topology.Connected.Basic

namespace HolomorphicAnosov.Ghys

open Set

/-- The omitted point of the image of an equivalence-generated leaf is independent of the marked
point within that leaf. (Ghys, proof of Thm. B, p. 598) -/
theorem omitted_point_eq_of_leaf_class_g10
    {E Z : Type*} (D : E → Z) (R : E → E → Prop) (pole : E → Z)
    (himage : ∀ x, D '' {y | Relation.EqvGen R x y} = {pole x}ᶜ)
    {x y : E} (hxy : Relation.EqvGen R x y) : pole x = pole y := by
  have hclass : {z | Relation.EqvGen R x z} = {z | Relation.EqvGen R y z} := by
    ext z
    exact ⟨fun hxz ↦ Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) hxz,
      fun hyz ↦ Relation.EqvGen.trans _ _ _ hxy hyz⟩
  apply Set.singleton_injective
  apply compl_injective
  rw [← himage x, ← himage y, hclass]

end HolomorphicAnosov.Ghys
