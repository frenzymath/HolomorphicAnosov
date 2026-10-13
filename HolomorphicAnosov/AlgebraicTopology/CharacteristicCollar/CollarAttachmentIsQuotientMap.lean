import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMapIsQuotientMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.IsOpenSkeletonCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For a finite Hausdorff CW space, restriction of the characteristic attachment to the inverse image of the skeleton collar is a quotient map onto that collar.

Proof: Restrict the quotient attachment to the inverse image of the open skeleton collar. Restriction of a quotient map to an open target subset remains quotient.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarAttachment_isQuotientMap [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    Topology.IsQuotientMap ((skeletonCollar X m).restrictPreimage (attachmentMap X m)) :=
  (attachmentMap_isQuotientMap X m).restrictPreimage_isOpen (isOpen_skeletonCollar X m)

end HolomorphicAnosov.CharacteristicCellComparison
