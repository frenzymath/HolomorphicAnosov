import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.Skeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarCharts

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- On a lower-skeleton chart the time map is the constant path; on a disk-collar chart it is the characteristic image of the radial collar path.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarChartTimeMap (m : ℕ) : CollarCharts X m → C(unitInterval, Skeleton X m) :=
  Sum.elim (fun z ↦ ContinuousMap.const _ z.1)
    (fun z ↦ ⟨fun t ↦ characteristicCell X m z.1 (collarDeformation m (t, z.2)).1,
      (characteristicCell X m z.1).continuous.comp
        (continuous_subtype_val.comp ((collarDeformation m).continuous.comp
          (continuous_id.prodMk continuous_const)))⟩)

end HolomorphicAnosov.CharacteristicCellComparison
