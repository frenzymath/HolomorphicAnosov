import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartTimeMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.14(b) pp.530–531, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar chart assignment to its continuous time path is continuous into the compact-open continuous-map space.

Proof: On each summand form the jointly continuous evaluation map on chart times interval. Curry it into the compact-open continuous-map space. The lower-skeleton case uses a constant path and the disk case uses the characteristic map composed with the radial deformation. Combine by sum and sigma continuity.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, A.14(b) pp.530–531 for continuity of currying, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarChartTimeMap_continuous (m : ℕ) : Continuous (collarChartTimeMap X m) := by
  apply Continuous.sumElim
  · let f : C(↥(lowerSkeleton X m) × unitInterval, Skeleton X m) :=
      ⟨fun zt ↦ zt.1.1, continuous_subtype_val.comp continuous_fst⟩
    exact (ContinuousMap.curry f).continuous
  · apply continuous_sigma
    intro i
    let f : C(DiskCollar.{u} m × unitInterval, Skeleton X m) :=
      ⟨fun zt ↦ characteristicCell X m i (collarDeformation m (zt.2, zt.1)).1,
        (characteristicCell X m i).continuous.comp (continuous_subtype_val.comp
          ((collarDeformation m).continuous.comp continuous_swap))⟩
    exact (ContinuousMap.curry f).continuous

end HolomorphicAnosov.CharacteristicCellComparison
