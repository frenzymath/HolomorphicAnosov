import Mathlib.Topology.Constructions
import HolomorphicAnosov.Topology.AttachedCellPolyhedralData

namespace HolomorphicAnosov.HatcherAttachedCell

/-- Deleting a point of the open attached cell leaves the characteristic
quotient presentation by the old space and the punctured characteristic
disk. Source: Hatcher Theorem 4.8, p.349 and Appendix A.17, pp.532–533.
The complement of the deleted point is open in a T1 space. Restrict the
original quotient to this open preimage. The old summand needs no deletion,
and the disk summand is restricted to its open preimage; the canonical map
from their sum to the restricted original source is continuous, open and
surjective, hence quotient. Compose the two quotient maps. -/
theorem attachment_punctured_quotient
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] {k : ℕ}
    (cell : Attachment Z k) (p : Z) (hp : p ∉ cell.oldSpace) :
    Topology.IsQuotientMap
      (Sum.elim (fun x : cell.oldSpace ↦
          (⟨x.val, fun he ↦ hp (he ▸ x.property)⟩ : {z : Z // z ≠ p}))
        (fun x : {d : CellDisk k // cell.characteristic d ≠ p} ↦
          (⟨cell.characteristic x.val, x.property⟩ : {z : Z // z ≠ p}))) := by
  let q : cell.oldSpace ⊕ CellDisk k → Z :=
    Sum.elim Subtype.val cell.characteristic
  let U : Set Z := {z | z ≠ p}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  let S := {s : cell.oldSpace ⊕ CellDisk k // q s ≠ p}
  let D := {d : CellDisk k // cell.characteristic d ≠ p}
  let e : cell.oldSpace ⊕ D → S := Sum.elim
    (fun x ↦ ⟨Sum.inl x, fun he ↦ hp (he ▸ x.property)⟩)
    (fun x ↦ ⟨Sum.inr x.val, x.property⟩)
  have hecont : Continuous e :=
    (continuous_inl.subtype_mk _).sumElim
      ((continuous_inr.comp continuous_subtype_val).subtype_mk _)
  have hD : IsOpen {d : CellDisk k | cell.characteristic d ≠ p} :=
    hU.preimage cell.characteristic.continuous
  have heopen : IsOpenMap e :=
    (isOpenMap_inl.subtype_mk _).sumElim
      ((isOpenMap_inr.comp hD.isOpenEmbedding_subtypeVal.isOpenMap).subtype_mk _)
  have hesurj : Function.Surjective e := by
    intro s
    rcases s with ⟨s, hs⟩
    cases s with
    | inl x => exact ⟨Sum.inl x, rfl⟩
    | inr d => exact ⟨Sum.inr ⟨d, hs⟩, rfl⟩
  have hq := cell.quotient.restrictPreimage_isOpen hU
  have hh := hq.comp (heopen.isQuotientMap hecont hesurj)
  have heq : (U.restrictPreimage q) ∘ e =
      Sum.elim (fun x : cell.oldSpace ↦
        (⟨x.val, fun he ↦ hp (he ▸ x.property)⟩ : {z : Z // z ≠ p}))
        (fun x : D ↦ (⟨cell.characteristic x.val, x.property⟩ : {z : Z // z ≠ p})) := by
    funext s
    cases s <;> rfl
  rw [heq] at hh
  exact hh

end HolomorphicAnosov.HatcherAttachedCell
