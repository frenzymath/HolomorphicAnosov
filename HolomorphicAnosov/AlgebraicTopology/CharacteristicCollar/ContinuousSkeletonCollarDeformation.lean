import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarAttachmentIsQuotientMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicPreimageSkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartCover
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMapContinuous
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMapOpen
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartTimeMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartTimeMapContinuous
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartTimeMapEq

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For a finite Hausdorff CW space, the skeleton-collar deformation is jointly continuous in time and in the collar point with its original subtype topology.

Proof: The chart cover is continuous and open by restriction to its target subtype.
On the lower-skeleton summand it is surjective by identity; on each disk summand the
exact collar-preimage identity supplies its radius bound. It is therefore quotient.
Descend joint continuity first through the quotient attachment restricted to the open collar, then through the quotient collar-chart cover. On charts, uncurry the continuous time-map assignment and exchange coordinates. The chart equality identifies that continuous map with the desired composite.

Proof origin: agent-written expansion of the joint-continuity step omitted from the
characteristic-cell excision argument of Hatcher Proposition 3.17 p.217. The custom
chart-cover surjectivity and two-stage descent argument are supplied here. Source inputs:
Hatcher Appendix A.4–A.5 pp.522–523, A.14 pp.530–531, and A.17 pp.532–533. -/
theorem continuous_skeletonCollarDeformation [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    Continuous (fun tx : unitInterval × ↥(skeletonCollar X m) ↦
      skeletonCollarDeformation X m tx.1 tx.2) := by
  have hcover : Topology.IsQuotientMap (collarChartCover X m) := by
    have hc : Continuous (collarChartCover X m) :=
      (collarChartMap_continuous X m).subtype_mk _
    have ho : IsOpenMap (collarChartCover X m) :=
      (collarChartMap_open X m).subtype_mk _
    have hs : Function.Surjective (collarChartCover X m) := by
      intro z
      rcases z with ⟨a, ha⟩
      rcases a with a | ⟨i, a⟩
      · exact ⟨Sum.inl a, rfl⟩
      · have hr : (1 / 2 : ℝ) < ‖a.down.1‖ :=
          (Set.ext_iff.mp (characteristic_preimage_skeletonCollar X m i) a).mp ha
        exact ⟨Sum.inr ⟨i, ⟨a, hr⟩⟩, rfl⟩
    exact ho.isQuotientMap hc hs
  apply (collarAttachment_isQuotientMap X m).continuous_lift_prod_right
  apply hcover.continuous_lift_prod_right
  have hc := (ContinuousMap.continuous_uncurry_of_continuous
    ⟨collarChartTimeMap X m, collarChartTimeMap_continuous X m⟩).comp continuous_swap
  exact hc.congr (fun tz ↦ collarChartTimeMap_eq X m tz.1 tz.2)

end HolomorphicAnosov.CharacteristicCellComparison
