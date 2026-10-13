import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentOldSpaceBoundary
import HolomorphicAnosov.Topology.CWComplex.PuncturedDiskRadialDeformation
import HolomorphicAnosov.Topology.CWComplex.AttachmentInteriorFibre
import HolomorphicAnosov.Topology.CWComplex.AttachmentPuncturedHomotopyDescent

namespace HolomorphicAnosov.HatcherAttachedCell

/-- Removing any point of the open attached cell permits a deformation into
the old space, fixing the old space. Source: Hatcher Theorem 4.8, p.349.
Choose the interior characteristic representative of the deleted point,
apply the arbitrary-pole disk deformation, and postcompose it with the
characteristic map. Interior fibre uniqueness identifies the two punctures.
The disk stays inside its original carrier, ends on its sphere, and fixes
that sphere, so punctured attachment descent applies without any boundary
injectivity assumption. -/
theorem attachment_radial_deformation
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] {k : ℕ}
    (cell : Attachment Z k) (p : Z) (hp : p ∉ cell.oldSpace) :
    ∃ H : C(unitInterval × {z : Z // z ≠ p}, Z),
      (∀ z, H (0, z) = z.val) ∧
      (∀ z, H (1, z) ∈ cell.oldSpace) ∧
      (∀ t z, H (t, z) ≠ p) ∧
      (∀ t z, z.val ∈ cell.oldSpace → H (t, z) = z.val) := by
  let pi := cell.interior.symm ⟨p, hp⟩
  let pd : CellDisk k := interiorInclusion pi
  have hpi : ‖pd.val‖ < 1 := by
    change ‖pi.val‖ < 1
    simpa only [Metric.mem_ball, dist_zero_right] using pi.property
  have hpimage : cell.characteristic pd = p := by
    exact (cell.characteristic_interior pi).trans
      (congrArg Subtype.val (cell.interior.apply_symm_apply ⟨p, hp⟩))
  obtain ⟨R, hRzero, hRone, hRrange, hRfixed⟩ :=
    HolomorphicAnosov.punctured_disk_radial_deformation pd.val hpi
  let D := {d : CellDisk k // cell.characteristic d ≠ p}
  let liftD (d : D) : {z : EuclideanSpace ℝ (Fin k) // ‖z‖ ≤ 1 ∧ z ≠ pd.val} :=
    ⟨d.val.val,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using d.val.property,
      fun he ↦ d.property ((congrArg cell.characteristic (Subtype.ext he)).trans hpimage)⟩
  have hlift : Continuous liftD :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let Q : C(unitInterval × D, CellDisk k) := ⟨fun s ↦
    ⟨R (s.1, liftD s.2), by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hRrange s.1 (liftD s.2)).1⟩,
    (R.continuous.comp (continuous_fst.prodMk (hlift.comp continuous_snd))).subtype_mk
      (fun s ↦ by
        change R (s.1, liftD s.2) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
        simpa only [Metric.mem_closedBall, dist_zero_right] using (hRrange s.1 (liftD s.2)).1)⟩
  let H := cell.characteristic.comp Q
  obtain ⟨K, hKzero, hKone, hKavoid, hKfixed, _⟩ :=
    attachment_punctured_homotopy_descent cell p hp H (by
      intro d
      change cell.characteristic (Q (0, d)) = cell.characteristic d.val
      apply congrArg cell.characteristic
      apply Subtype.ext
      exact hRzero (liftD d)) (by
      intro t d hd
      change cell.characteristic (Q (t, d)) = cell.characteristic d.val
      apply congrArg cell.characteristic
      apply Subtype.ext
      exact hRfixed t (liftD d) hd) (by
      intro d
      apply (attachment_characteristic_mem_old_iff cell (Q (1, d))).mpr
      exact hRone (liftD d)) (by
      intro t d he
      have heq : Q (t, d) = pd :=
        (attachment_characteristic_interior_fibre cell pd hpi (Q (t, d))).mp
          (he.trans hpimage.symm)
      exact (hRrange t (liftD d)).2 (congrArg Subtype.val heq))
  exact ⟨K, hKzero, hKone, hKavoid, hKfixed⟩

end HolomorphicAnosov.HatcherAttachedCell
