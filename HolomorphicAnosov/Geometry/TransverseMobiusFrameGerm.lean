import HolomorphicAnosov.Geometry.FlatProjectiveFrameCoverG9
import HolomorphicAnosov.Geometry.MobiusGroupCarrierG9
import Mathlib.Topology.Homotopy.Lifting

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- A frame determines the same transverse projective germ in every chart containing
its basepoint. (Thurston, §3.5, pp. 34–35) -/
theorem transverse_mobius_frame_germ
    {M L ι : Type*} [TopologicalSpace M] [TopologicalSpace L]
    (A : FlatProjectiveAtlas M L ι) (Z : FiberBundleCore ι M MobiusGroup)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (z : Z.TotalSpace) (i : ι) (hi : z.proj ∈ (A.chart i).source) :
    (fun w ↦ (mobiusGroupToComplexMobius z.2).apply
      (complexProjectiveLineFinite ((A.chart (A.indexAt z.proj) w).2))) =ᶠ[𝓝 z.proj]
    (fun w ↦ (mobiusGroupToComplexMobius (Z.localTriv i z).2).apply
      (complexProjectiveLineFinite ((A.chart i w).2))) := by
  let k := A.indexAt z.proj
  have hk : z.proj ∈ (A.chart k).source := A.mem_source _
  have hAt : ContinuousAt (A.transition k i) z.proj :=
    (A.transition_continuous k i).continuousAt
      (((A.chart k).open_source.inter (A.chart i).open_source).mem_nhds ⟨hk, hi⟩)
  have ht : ∀ᶠ w in 𝓝 z.proj, A.transition k i w = A.transition k i z.proj :=
    hAt.eventually ((isOpen_discrete {A.transition k i z.proj}).mem_nhds rfl)
  filter_upwards [ht, (A.chart k).open_source.mem_nhds hk,
    (A.chart i).open_source.mem_nhds hi] with w htw hwk hwi
  apply (OnePoint.equivProjectivization ℂ).symm.injective
  change (OnePoint.equivProjectivization ℂ).symm
      ((mobiusGroupToComplexMobius (show MobiusGroup from z.2)).apply _) = _
  rw [mobiusGroupToComplexMobius_apply, Equiv.symm_apply_apply,
    complexProjectiveLineFinite_to_onePoint]
  rw [mobiusGroupToComplexMobius_apply, Equiv.symm_apply_apply,
    complexProjectiveLineFinite_to_onePoint]
  rw [Z.localTriv_apply, hchange, hindex]
  change z.2.apply ((A.chart k w).2 : OnePoint ℂ) =
    ((show MobiusGroup from z.2) * (A.transition k i z.proj)⁻¹).apply ((A.chart i w).2 : OnePoint ℂ)
  rw [A.transition_agrees k i w ⟨hwk, hwi⟩, htw]
  change z.2.val _ = z.2.val ((A.transition k i z.proj).val.symm
    ((A.transition k i z.proj).val _))
  rw [Equiv.symm_apply_apply]

end HolomorphicAnosov.Ghys
