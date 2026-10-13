import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundaryRetraction
import Mathlib.Topology.Constructions

/-! Hatcher, Algebraic Topology, Proposition 3.17 p.217 and the disk-collar
argument for excision pp.123–124: radial retraction on the disjoint disk collars.
The topology is the actual subspace topology of the characteristic disk union. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- The time-one radial retraction on the disjoint union of characteristic disk
collars, with its actual subspace topology. Continuity follows because the Sigma
of the subtype inclusions is inducing; after composing with that map, the
reindexing from the outer collar to the Sigma of collars is just subtype inclusion.
The continuous component retractions then assemble by `Continuous.sigma_map`. -/
def sourceBoundaryRetraction (X : Type u) [TopologicalSpace X]
    [CWComplex (univ : Set X)] (m : ℕ) :
    C(↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        (1 / 2 : ℝ) < ‖z.2.down.1‖},
      ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        z.2 ∈ cellBoundary m}) where
  toFun z := ⟨⟨z.1.1, (cellBoundaryRetraction m ⟨z.1.2, z.2⟩).1⟩,
    (cellBoundaryRetraction m ⟨z.1.2, z.2⟩).2⟩
  continuous_toFun := by
    let split : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        (1 / 2 : ℝ) < ‖z.2.down.1‖} →
        (Σ _i : RelCWComplex.cell (univ : Set X) m, DiskCollar.{u} m) :=
      fun z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
    have hind :=
      (isInducing_sigmaMap
        (σ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ DiskCollar.{u} m)
        (τ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ CellDisk.{u} m)
        (f₁ := id)
        (f₂ := fun _ : RelCWComplex.cell (univ : Set X) m ↦
          (Subtype.val : DiskCollar.{u} m → CellDisk.{u} m))
        Function.injective_id).mpr fun _ ↦ IsInducing.subtypeVal
    have hsplit : Continuous split := hind.continuous_iff.mpr continuous_subtype_val
    have hrad := Continuous.sigma_map
      (σ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ DiskCollar.{u} m)
      (τ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ CellDisk.{u} m)
      (f₁ := id)
      (f₂ := fun _ ↦ fun z : DiskCollar.{u} m ↦ (cellBoundaryRetraction m z).1)
      (fun _ ↦ (cellBoundaryRetraction m).continuous.subtype_val)
    exact (hrad.comp hsplit).subtype_mk _

end HolomorphicAnosov.CharacteristicCellComparison
