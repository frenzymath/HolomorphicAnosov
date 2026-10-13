import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationZero
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At time zero the skeleton-collar deformation is the inclusion of the collar into the skeleton.

Proof: On the lower skeleton the formula is identity by definition. Otherwise choose its characteristic collar representative and use that disk-collar deformation is identity at time zero.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem skeletonCollarDeformation_zero (m : ℕ) (x : ↥(skeletonCollar X m)) :
    skeletonCollarDeformation X m 0 x = x.1 := by
  classical
  unfold skeletonCollarDeformation
  split_ifs with h
  · rfl
  · let z := Classical.choose (x.2.resolve_left h)
    have he : characteristicCell X m z.1 z.2.1 = x.1 :=
      Classical.choose_spec (x.2.resolve_left h)
    change characteristicCell X m z.1 (collarDeformation m (0, z.2)).1 = x.1
    rw [collarDeformation_zero]
    exact he

end HolomorphicAnosov.CharacteristicCellComparison
