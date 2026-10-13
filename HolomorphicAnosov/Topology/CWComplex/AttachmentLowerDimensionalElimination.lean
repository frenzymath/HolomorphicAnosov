import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentMissingPointHomotopy
import HolomorphicAnosov.Topology.CWComplex.AttachmentMissingPointElimination

namespace HolomorphicAnosov.HatcherAttachedCell

/-- A map from a lower-dimensional cube into a one-cell attachment can
be deformed into the old space relative to its original old-space preimage.
Source: Hatcher Theorem 4.8 and Lemma 4.10, pp.349–351.

Apply the narrower relative missed-point homotopy theorem. Its endpoint
misses a point in the open cell. Radially eliminate that
point to move the endpoint map into the old space. The first deformation
fixes the original old-space preimage; thus this set is contained in the
endpoint map's old-space preimage and the second homotopy fixes it too.
Concatenating the two relative homotopies proves the claim. The local
missed-point theorem is supplied by Bredon relative smoothing and locally stationary chart extension. -/
theorem attachment_lower_dimensional_elimination
    {Z : Type*} [TopologicalSpace Z] [T2Space Z] {n k : ℕ}
    (cell : Attachment Z k) (f : C(Cube n, Z)) (hnk : n < k) :
    ∃ g : C(Cube n, Z), Set.range g ⊆ cell.oldSpace ∧
      Nonempty (ContinuousMap.HomotopyRel f g (f ⁻¹' cell.oldSpace)) := by
  obtain ⟨f₁, p, hp, havoid, ⟨H₁⟩⟩ := attachment_missing_point_homotopy cell f hnk
  obtain ⟨r, hr, ⟨H₂⟩⟩ := attachment_missing_point_elimination cell f₁ p hp havoid
  let H₂' : ContinuousMap.HomotopyRel f₁ r (f ⁻¹' cell.oldSpace) := {
    toHomotopy := H₂.toHomotopy
    prop' := by
      intro t x hx
      apply H₂.eq_fst t
      change f₁ x ∈ cell.oldSpace
      rw [← H₁.fst_eq_snd hx]
      exact hx }
  exact ⟨r, hr, ⟨H₁.trans H₂'⟩⟩

end HolomorphicAnosov.HatcherAttachedCell
