import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMapIsQuotientMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicPreimageSkeletonCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For every finite Hausdorff CW space, its skeleton collar is open in the original skeleton topology.

Proof: Test openness after the quotient attachment. On the lower-skeleton summand the preimage is the whole space. On every disk summand the preimage is the strict norm inequality greater than one half, which is open by continuity of norm. Sum and sigma topology then give openness.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem isOpen_skeletonCollar [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    IsOpen (skeletonCollar X m) := by
  apply (attachmentMap_isQuotientMap X m).isCoinducing.isOpen_preimage.mp
  rw [isOpen_sum_iff]
  constructor
  · have he : Sum.inl ⁻¹' ((attachmentMap X m) ⁻¹' skeletonCollar X m) = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact Or.inl z.2
    rw [he]
    exact isOpen_univ
  · rw [isOpen_sigma_iff]
    intro i
    change IsOpen ((characteristicCell X m i) ⁻¹' skeletonCollar X m)
    rw [characteristic_preimage_skeletonCollar]
    exact isOpen_lt continuous_const
      ((continuous_subtype_val.comp continuous_uliftDown).norm)

end HolomorphicAnosov.CharacteristicCellComparison
