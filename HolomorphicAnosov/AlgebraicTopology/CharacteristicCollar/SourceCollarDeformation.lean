import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceBoundaryRetraction
import Mathlib.Topology.Homeomorph.Lemmas

/-! Hatcher, Algebraic Topology, Proposition 3.17 p.217 and the collar argument
in Proposition 2.22 p.124: the componentwise radial deformation of the disjoint
source collars. The interval and subspace topologies are unchanged. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- The radial disk-collar deformation on the disjoint characteristic source.
Joint continuity follows by reindexing the collar subtype as a Sigma of collars,
distributing the ordinary product with the interval, and applying the continuous
radial deformation on each summand. The inducing property of the Sigma of
subtype inclusions justifies the reindexing with the given topology. -/
def sourceCollarDeformation (X : Type u) [TopologicalSpace X]
    [CWComplex (univ : Set X)] (m : ℕ) :
    C(unitInterval × ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        (1 / 2 : ℝ) < ‖z.2.down.1‖},
      ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        (1 / 2 : ℝ) < ‖z.2.down.1‖}) where
  toFun z := ⟨⟨z.2.1.1, (collarDeformation m (z.1, ⟨z.2.1.2, z.2.2⟩)).1⟩,
    (collarDeformation m (z.1, ⟨z.2.1.2, z.2.2⟩)).2⟩
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
    have hd := (Homeomorph.sigmaProdDistrib
      (X := fun _ : RelCWComplex.cell (univ : Set X) m ↦ DiskCollar.{u} m)
      (Y := unitInterval)).continuous.comp
        ((hsplit.comp continuous_snd).prodMk continuous_fst)
    have hrad := Continuous.sigma_map
      (σ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ DiskCollar.{u} m × unitInterval)
      (τ := fun _ : RelCWComplex.cell (univ : Set X) m ↦ CellDisk.{u} m)
      (f₁ := id)
      (f₂ := fun _ ↦ fun z : DiskCollar.{u} m × unitInterval ↦
        (collarDeformation m (z.2, z.1)).1)
      (fun _ ↦ ((collarDeformation m).continuous.comp continuous_swap).subtype_val)
    exact (hrad.comp hd).subtype_mk _

end HolomorphicAnosov.CharacteristicCellComparison
