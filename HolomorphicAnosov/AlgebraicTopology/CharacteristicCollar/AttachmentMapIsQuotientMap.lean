import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMapSurjective

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For every finite Hausdorff CW space and degree m, its characteristic attachment map is a quotient map for the original skeleton topology.

Proof: The lower skeleton is closed, so its inclusion is a closed map. Finiteness makes the disjoint union of characteristic disks compact; its continuous map to the Hausdorff skeleton is closed. Their sum is a continuous closed surjection, hence is a quotient map.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem attachmentMap_isQuotientMap [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    Topology.IsQuotientMap (attachmentMap X m) := by
  have hclosed : IsClosed (lowerSkeleton X m) :=
    (CWComplex.skeletonLT (univ : Set X) m).closed.preimage continuous_subtype_val
  have hdisk : CompactSpace (CellDisk.{u} m) := by infer_instance
  have hfinite : Finite (RelCWComplex.cell (univ : Set X) m) :=
    RelCWComplex.FiniteType.finite_cell m
  have hsum : CompactSpace (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) :=
    inferInstance
  have hleft : IsClosedMap (Subtype.val : ↥(lowerSkeleton X m) → Skeleton X m) :=
    hclosed.isClosedEmbedding_subtypeVal.isClosedMap
  have hright : IsClosedMap (fun z : Σ _i : RelCWComplex.cell (univ : Set X) m,
      CellDisk.{u} m ↦ characteristicCell X m z.1 z.2) :=
    (continuous_sigma fun i ↦ (characteristicCell X m i).continuous).isClosedMap
  exact (hleft.sumElim hright).isQuotientMap (attachmentMap X m).continuous
    (attachmentMap_surjective X m)

end HolomorphicAnosov.CharacteristicCellComparison
