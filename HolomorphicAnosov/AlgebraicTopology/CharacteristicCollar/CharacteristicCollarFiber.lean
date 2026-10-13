import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellPreimageLowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationFixed
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicInteriorFiber

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- In a Hausdorff CW space, two characteristic collar representatives of the same skeleton point have equal characteristic images after radial deformation at any time, even if attaching maps identify boundary points.

Proof: If one representative is on the boundary, its image lies in the lower skeleton; exact boundary preimages imply the other is also on the boundary. Both radial deformations fix the representatives. Otherwise both are interior and their representatives agree by interior-fibre uniqueness.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem characteristic_collar_fiber (m : ℕ) (t : unitInterval)
    (i j : RelCWComplex.cell (univ : Set X) m) (z w : DiskCollar.{u} m)
    (he : characteristicCell X m i z.1 = characteristicCell X m j w.1) :
    characteristicCell X m i (collarDeformation m (t, z)).1 =
      characteristicCell X m j (collarDeformation m (t, w)).1 := by
  by_cases hz : z.1 ∈ cellBoundary m
  · have hw : w.1 ∈ cellBoundary m := by
      apply (Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m j) w.1).mp
      change characteristicCell X m j w.1 ∈ lowerSkeleton X m
      rw [← he]
      exact characteristicCell_mapsTo X m i hz
    rw [collarDeformation_fixed m t z hz, collarDeformation_fixed m t w hw]
    exact he
  · have hw : w.1 ∉ cellBoundary m := by
      intro hw
      apply hz
      apply (Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m i) z.1).mp
      change characteristicCell X m i z.1 ∈ lowerSkeleton X m
      rw [he]
      exact characteristicCell_mapsTo X m j hw
    have hs := characteristic_interior_fiber X m i j z.1 w.1 hz hw he
    have hi : i = j := congrArg Sigma.fst hs
    subst j
    have hzw : z = w := Subtype.ext (by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs)
    subst w
    rfl

end HolomorphicAnosov.CharacteristicCellComparison
