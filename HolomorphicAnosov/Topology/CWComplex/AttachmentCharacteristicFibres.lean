import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentOldSpaceBoundary

namespace HolomorphicAnosov.HatcherAttachedCell

/-- Equal characteristic images have equal disk representatives unless
both representatives lie on the boundary. Hatcher's one-cell attachment
in Theorem 4.8, pp.349–350 allows arbitrary boundary identifications;
interior injectivity comes from the specified open-cell homeomorphism.
Boundary membership is equivalent to membership of the image in the old
space, so equality of the images transfers boundary membership. If neither
point is on the boundary, the interior homeomorphism is injective. -/
theorem attachment_characteristic_fibres
    {Z : Type*} [TopologicalSpace Z] {k : ℕ}
    (cell : Attachment Z k) (z w : CellDisk k)
    (he : cell.characteristic z = cell.characteristic w) :
    z = w ∨ (‖z.val‖ = 1 ∧ ‖w.val‖ = 1) := by
  by_cases hz : ‖z.val‖ = 1
  · right
    refine ⟨hz, (attachment_characteristic_mem_old_iff cell w).mp ?_⟩
    rw [← he]
    exact (attachment_characteristic_mem_old_iff cell z).mpr hz
  · left
    have hw : ‖w.val‖ ≠ 1 := by
      intro hw
      apply hz
      apply (attachment_characteristic_mem_old_iff cell z).mp
      rw [he]
      exact (attachment_characteristic_mem_old_iff cell w).mpr hw
    have hzlt : ‖z.val‖ < 1 := lt_of_le_of_ne
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property) hz
    have hwlt : ‖w.val‖ < 1 := lt_of_le_of_ne
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property) hw
    let zi : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 :=
      ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hzlt⟩
    let wi : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 :=
      ⟨w.val, by simpa only [Metric.mem_ball, dist_zero_right] using hwlt⟩
    have hi : cell.interior zi = cell.interior wi := by
      apply Subtype.ext
      exact (cell.characteristic_interior zi).symm.trans
        (he.trans (cell.characteristic_interior wi))
    exact Subtype.ext (congrArg (fun x : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 ↦ x.val) (cell.interior.injective hi))

end HolomorphicAnosov.HatcherAttachedCell
