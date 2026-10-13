import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentRadialDeformation

namespace HolomorphicAnosov.HatcherAttachedCell

/-- A map missing an open-cell point deforms into the old space relative
to the preimage of the old space. Source: Hatcher Theorem 4.8, p.349.
Lift the map to the complement of the missed point and compose with the
attached-cell radial deformation. Its time-one slice is continuous and
lands in the old space; radial fixedness gives the relative condition. -/
theorem attachment_missing_point_elimination
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] [T1Space Z]
    {k : ℕ} (cell : Attachment Z k) (f : C(X, Z))
    (p : Z) (hp : p ∉ cell.oldSpace) (hmiss : ∀ x, f x ≠ p) :
    ∃ g : C(X, Z), Set.range g ⊆ cell.oldSpace ∧
      Nonempty (ContinuousMap.HomotopyRel f g (f ⁻¹' cell.oldSpace)) := by
  obtain ⟨R, hzero, hone, _, hfixed⟩ := attachment_radial_deformation cell p hp
  let liftF : C(X, {z : Z // z ≠ p}) := ⟨fun x ↦ ⟨f x, hmiss x⟩,
    f.continuous.subtype_mk _⟩
  let H : C(unitInterval × X, Z) := ⟨fun q ↦ R (q.1, liftF q.2),
    R.continuous.comp (continuous_fst.prodMk (liftF.continuous.comp continuous_snd))⟩
  let g : C(X, Z) := ⟨fun x ↦ H (1, x),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, ?_, ⟨{
    toContinuousMap := H
    map_zero_left := fun x ↦ hzero (liftF x)
    map_one_left := fun _ ↦ rfl
    prop' := fun t x hx ↦ hfixed t (liftF x) hx }⟩⟩
  rintro z ⟨x, rfl⟩
  exact hone (liftF x)

end HolomorphicAnosov.HatcherAttachedCell
