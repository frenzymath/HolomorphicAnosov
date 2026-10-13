import HolomorphicAnosov.Topology.AttachedCellPolyhedralData

namespace HolomorphicAnosov.HatcherAttachedCell

/-- In a one-cell attachment, a characteristic-disk point maps into the
old space exactly when it lies on the characteristic sphere. This is the
boundary/interior separation used in Hatcher Theorem 4.8, pp.349–350.
For a boundary point use the attaching identification. For an interior
point use the given homeomorphism onto the complement of the old space;
the closed-disk bound leaves no third case. -/
theorem attachment_characteristic_mem_old_iff
    {Z : Type*} [TopologicalSpace Z] {k : ℕ}
    (cell : Attachment Z k) (z : CellDisk k) :
    cell.characteristic z ∈ cell.oldSpace ↔ ‖z.val‖ = 1 := by
  have hzle : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  constructor
  · intro hz
    by_contra hn
    have hzlt : ‖z.val‖ < 1 := lt_of_le_of_ne hzle hn
    let zi : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 :=
      ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hzlt⟩
    have he : cell.characteristic z = (cell.interior zi).val :=
      cell.characteristic_interior zi
    rw [he] at hz
    exact (cell.interior zi).property hz
  · intro hz
    let zs : CellSphere k :=
      ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
    have he : cell.characteristic z = (cell.attaching zs).val := cell.boundary_eq zs
    rw [he]
    exact (cell.attaching zs).property

end HolomorphicAnosov.HatcherAttachedCell
