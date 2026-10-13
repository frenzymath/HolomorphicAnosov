import HolomorphicAnosov.Paper.Ghys.FlatProjectiveAtlas
import Mathlib.Topology.Covering.Basic

/-! The local frame changes of a flat projective atlas define a covering with discrete Möbius-group
fibre. (Thurston, §3.5, pp.34–35; §4.8, p.63) -/

noncomputable section
open Set

namespace HolomorphicAnosov.Ghys

/-- The frame changes `g ↦ g * tᵢⱼ⁻¹` of a flat projective atlas define a covering with its chart
sources as base domains. (Thurston, §3.5, pp.34–35; §4.8, p.63) -/
theorem flatProjectiveFrameCover
    {X L ι : Type*} [TopologicalSpace X] [TopologicalSpace L]
    (A : FlatProjectiveAtlas X L ι) :
    ∃ Z : FiberBundleCore ι X MobiusGroup,
      Z.baseSet = (fun i ↦ (A.chart i).source) ∧
      Z.indexAt = A.indexAt ∧
      Z.coordChange = (fun i j x g ↦ g * (A.transition i j x)⁻¹) ∧
      IsCoveringMap Z.proj := by
  let Z : FiberBundleCore ι X MobiusGroup := {
    baseSet := fun i ↦ (A.chart i).source
    isOpen_baseSet := fun i ↦ (A.chart i).open_source
    indexAt := A.indexAt
    mem_baseSet_at := A.mem_source
    coordChange := fun i j x g ↦ g * (A.transition i j x)⁻¹
    coordChange_self := by
      intro i x hx g
      rw [A.transition_self i x hx, inv_one, mul_one]
    continuousOn_coordChange := by
      intro i j
      exact continuous_snd.continuousOn.mul
        ((A.transition_continuous i j).comp continuous_fst.continuousOn
          (fun x hx ↦ hx.1)).inv
    coordChange_comp := by
      intro i j k x hx g
      rw [A.transition_comp i j k x hx, mul_inv_rev, mul_assoc]
  }
  refine ⟨Z, rfl, rfl, rfl, IsFiberBundle.isCoveringMap (F := MobiusGroup) ?_⟩
  intro x
  exact ⟨Z.localTrivAt x, Z.mem_localTrivAt_baseSet x⟩

end HolomorphicAnosov.Ghys
