import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For each m-cell of a Hausdorff CW space, the inverse image of the lower skeleton under its characteristic map is exactly the boundary of its closed disk.

Proof: The boundary maps into the preceding skeleton. Conversely, a closed-disk point outside its boundary has norm strictly below one, so its image lies in the open cell. This open cell is disjoint from the preceding skeleton, giving a contradiction.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem characteristicCell_preimage_lowerSkeleton (m : ℕ)
    (i : RelCWComplex.cell (univ : Set X) m) :
    (characteristicCell X m i) ⁻¹' lowerSkeleton X m = cellBoundary m := by
  ext z
  constructor
  · intro hz
    by_contra hb
    have hle : dist z.down.1 0 ≤ 1 := z.down.2
    have hne : dist z.down.1 0 ≠ 1 := hb
    have hball : z.down.1 ∈ Metric.ball (0 : Fin m → ℝ) 1 :=
      lt_of_le_of_ne hle hne
    have hopen : RelCWComplex.map m i z.down.1 ∈ RelCWComplex.openCell m i :=
      ⟨z.down.1, hball, rfl⟩
    exact (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := (univ : Set X))
        (n := (m : ℕ∞)) (j := i) le_rfl)) hz hopen
  · intro hz
    exact characteristicCell_mapsTo X m i hz

end HolomorphicAnosov.CharacteristicCellComparison
