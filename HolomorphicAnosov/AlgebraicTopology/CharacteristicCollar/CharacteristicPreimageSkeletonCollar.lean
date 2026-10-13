import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellPreimageLowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicInteriorFiber
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The inverse image of the skeleton collar under any characteristic m-cell map is exactly the part of its disk with norm greater than one half.

Proof: If the image lies in the lower skeleton, the disk point has norm one. If it is another collar image, either the disk point is on the sphere, or both representatives are interior and interior-fibre uniqueness transfers the other representative’s collar bound. Conversely a point of norm greater than one half gives its own collar-image witness.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem characteristic_preimage_skeletonCollar (m : ℕ)
    (i : RelCWComplex.cell (univ : Set X) m) :
    (characteristicCell X m i) ⁻¹' skeletonCollar X m =
      {z | (1 / 2 : ℝ) < ‖z.down.1‖} := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · have hb := (Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m i) z).mp hz
      have hn : ‖z.down.1‖ = 1 := by
        simpa only [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hb
      change (1 / 2 : ℝ) < ‖z.down.1‖
      rw [hn]
      norm_num
    · obtain ⟨⟨j, w⟩, he⟩ := hz
      by_cases hb : z ∈ cellBoundary m
      · have hn : ‖z.down.1‖ = 1 := by
          simpa only [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hb
        change (1 / 2 : ℝ) < ‖z.down.1‖
        rw [hn]
        norm_num
      · have hwb : w.1 ∉ cellBoundary m := by
          intro hw
          apply hb
          apply (Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m i) z).mp
          change characteristicCell X m i z ∈ lowerSkeleton X m
          rw [← he]
          exact characteristicCell_mapsTo X m j hw
        have hs := characteristic_interior_fiber X m j i w.1 z hwb hb he
        have hv : w.1 = z := congrArg (fun a ↦ a.2) hs
        exact hv ▸ w.2
  · intro hz
    exact Or.inr ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩

end HolomorphicAnosov.CharacteristicCellComparison
