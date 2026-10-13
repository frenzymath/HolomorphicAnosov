import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import HolomorphicAnosov.Geometry.IntrinsicPullbackSheet

/-! Covering maps obtained from pullback projections. -/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {S : Type u} {Y : Type v} {L : Type w}
variable [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace L]

/-- The first projection from a covering pullback is a covering (Bredon II §14 pp.111–112; Hatcher pp.60–62).-/
theorem intrinsicPullbackProjection_isCoveringMap
    (j : L → S) (p : Y → S) (hj : Continuous j) (hp : IsCoveringMap p) :
    IsCoveringMap (fun z : IntrinsicCoveringPullback j p ↦ z.val.1) := by
  intro a
  obtain ⟨inst, U, haU, hU, hpU, H, hH⟩ := hp (j a)
  let V := j ⁻¹' U
  let e := intrinsicPullbackSheet j p hj U V (fun _ hx ↦ hx) H hH
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := p ⁻¹' {j a})
  exact ⟨inst, V, haU, hU.preimage hj,
    (hU.preimage hj).preimage (continuous_fst.comp continuous_subtype_val), e, fun _ ↦ rfl⟩

end HolomorphicAnosov
