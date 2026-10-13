import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen

/-! A symmetric local relation on a preconnected space connects any two points by a finite chain if
every point has an open neighborhood related to it. This applies to the open plaques of a
connected intrinsic leaf. (Hirsch–Pugh–Shub, §7, p.116) -/

open Set

/-- A symmetric relation on a preconnected space has a single finite-chain class if each point has
an open neighborhood all of whose points are related to it. -/
theorem eqvGen_of_preconnected_local_relation_g10 {L : Type*} [TopologicalSpace L]
    [PreconnectedSpace L] (R : L → L → Prop)
    (hlocal : ∀ x : L, ∃ V : Set L, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, R x y)
    (x y : L) : Relation.EqvGen R x y := by
  let C : Set L := {z | Relation.EqvGen R x z}
  have ho : IsOpen C := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hV, hzV, hR⟩ := hlocal z
    refine ⟨V, ?_, hV, hzV⟩
    intro w hw
    exact Relation.EqvGen.trans _ _ _ hz (Relation.EqvGen.rel _ _ (hR w hw))
  have hc : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hV, hzV, hR⟩ := hlocal z
    refine ⟨V, ?_, hV, hzV⟩
    intro w hw hcw
    apply hz
    exact Relation.EqvGen.trans _ _ _ hcw
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hR w hw)))
  have hC : C = Set.univ := IsClopen.eq_univ ⟨hc, ho⟩ ⟨x, Relation.EqvGen.refl x⟩
  change y ∈ C
  rw [hC]
  exact Set.mem_univ y

