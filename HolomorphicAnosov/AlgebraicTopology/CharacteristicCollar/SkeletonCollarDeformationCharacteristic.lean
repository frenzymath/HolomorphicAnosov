import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellPreimageLowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationFixed
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DescendedCollarCharacteristic
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The skeleton-collar deformation agrees with the radial characteristic formula on every characteristic disk collar, including boundary points.

Proof: If the attached point lies in the lower skeleton, its disk representative is on the boundary, where radial deformation is fixed. Otherwise the claim is the characteristic evaluation rule for the descended formula.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem skeletonCollarDeformation_characteristic (m : ℕ) (t : unitInterval)
    (i : RelCWComplex.cell (univ : Set X) m) (z : DiskCollar.{u} m) :
    skeletonCollarDeformation X m t
      ⟨characteristicCell X m i z.1, Or.inr ⟨⟨i, z⟩, rfl⟩⟩ =
        characteristicCell X m i (collarDeformation m (t, z)).1 := by
  classical
  unfold skeletonCollarDeformation
  split_ifs with h
  · have hb : z.1 ∈ cellBoundary m :=
      (Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m i) z.1).mp h
    rw [collarDeformation_fixed m t z hb]
  · exact descendedCollar_characteristic X m t i z

end HolomorphicAnosov.CharacteristicCellComparison
