import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentCharacteristicFibres

namespace HolomorphicAnosov.HatcherAttachedCell

/-- An interior characteristic point has a singleton characteristic fibre,
as used to match the punctures in Hatcher Theorem 4.8, p.349. The fibre
classification leaves only equality: its boundary alternative contradicts
the strict interior norm bound. -/
theorem attachment_characteristic_interior_fibre
    {Z : Type*} [TopologicalSpace Z] {k : ℕ}
    (cell : Attachment Z k) (p : CellDisk k) (hp : ‖p.val‖ < 1) (z : CellDisk k) :
    cell.characteristic z = cell.characteristic p ↔ z = p := by
  constructor
  · intro he
    rcases attachment_characteristic_fibres cell z p he with h | h
    · exact h
    · exact (hp.ne h.2).elim
  · rintro rfl
    rfl

end HolomorphicAnosov.HatcherAttachedCell
