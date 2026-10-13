import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For every m-cell of a Hausdorff CW space, its characteristic map is the native continuous map from the lifted closed unit disk into the degree-m skeleton.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def characteristicCell (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) :
    C(CellDisk.{u} m, Skeleton X m) where
  toFun z := ⟨RelCWComplex.map m i z.down.1,
    CWComplex.closedCell_subset_skeletonLT m i ⟨z.down.1, z.down.2, rfl⟩⟩
  continuous_toFun :=
    ((continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn m i)).comp
      continuous_uliftDown).subtype_mk _

end HolomorphicAnosov.CharacteristicCellComparison
