import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentSource

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The continuous attachment map is inclusion on the lower-skeleton summand and the characteristic map on each disk summand.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def attachmentMap (m : ℕ) : C(AttachmentSource X m, Skeleton X m) where
  toFun := Sum.elim Subtype.val (fun z ↦ characteristicCell X m z.1 z.2)
  continuous_toFun := continuous_subtype_val.sumElim
    (continuous_sigma fun i ↦ (characteristicCell X m i).continuous)

end HolomorphicAnosov.CharacteristicCellComparison
