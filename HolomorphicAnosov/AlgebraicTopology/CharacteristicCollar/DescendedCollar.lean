import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarImage

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The descended collar formula chooses a characteristic collar representative, radially deforms it at the specified time, and takes its characteristic image.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def descendedCollar (m : ℕ) (t : unitInterval) (x : ↥(collarImage X m)) : Skeleton X m :=
  let z := Classical.choose x.2
  characteristicCell X m z.1 (collarDeformation m (t, z.2)).1

end HolomorphicAnosov.CharacteristicCellComparison
