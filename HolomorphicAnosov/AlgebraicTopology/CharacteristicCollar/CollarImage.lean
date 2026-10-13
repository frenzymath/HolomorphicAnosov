import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The characteristic collar image is the range of the disjoint union of disk collars under their characteristic maps into the skeleton.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarImage (m : ℕ) : Set (Skeleton X m) :=
  Set.range (fun z : Σ _i : RelCWComplex.cell (univ : Set X) m, DiskCollar.{u} m ↦
    characteristicCell X m z.1 z.2.1)

end HolomorphicAnosov.CharacteristicCellComparison
