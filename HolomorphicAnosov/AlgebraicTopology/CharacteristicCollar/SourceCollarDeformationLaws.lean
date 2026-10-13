import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationZero
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationFixed

/-! Hatcher, Algebraic Topology, Proposition 2.22 p.124 and Proposition 3.17
p.217: endpoint and boundary identities for the source collar deformation. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- The source collar deformation starts at the identity, ends at the specified
boundary retraction, and fixes the boundary for every time. These identities
follow componentwise from the disk-collar identities; Sigma and subtype
extensionality preserve the component label and the radial point. At time one
the retraction formula agrees by definition. No condition on the number of
cells, the dimension, or the attaching maps is used. -/
theorem sourceCollarDeformation_laws (X : Type u) [TopologicalSpace X]
    [CWComplex (univ : Set X)] (m : ℕ)
    (z : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
      (1 / 2 : ℝ) < ‖z.2.down.1‖}) :
    sourceCollarDeformation X m (0, z) = z ∧
      (sourceCollarDeformation X m (1, z)).1 = (sourceBoundaryRetraction X m z).1 ∧
      ∀ t : unitInterval, z.1.2 ∈ cellBoundary m →
        sourceCollarDeformation X m (t, z) = z := by
  constructor
  · apply Subtype.ext
    exact congrArg (fun w : DiskCollar.{u} m ↦
      (⟨z.1.1, w.1⟩ : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m))
      (collarDeformation_zero m ⟨z.1.2, z.2⟩)
  constructor
  · rfl
  · intro t hz
    apply Subtype.ext
    exact congrArg (fun w : DiskCollar.{u} m ↦
      (⟨z.1.1, w.1⟩ : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m))
      (collarDeformation_fixed m t ⟨z.1.2, z.2⟩ hz)

end HolomorphicAnosov.CharacteristicCellComparison
