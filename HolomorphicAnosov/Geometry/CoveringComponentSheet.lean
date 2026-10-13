import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import HolomorphicAnosov.Geometry.CoveringSheetComponent

/-!
Restriction of covering sheet charts to path components. (Bredon, II §14, pp.111–112; Hatcher,
pp.60–62)
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {E : Type u} {B : Type v} {I : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]

/-- A sheet chart over a path-connected base restricts to a chart on a marked path component, with
labels for the sheets meeting that component. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62) -/
def coveringComponentSheet (f : E → B) (V : Set B)
    (H : f ⁻¹' V ≃ₜ V × I) (hH : ∀ z, (H z).1.val = f z)
    [PathConnectedSpace V] (e0 : E) (v0 : V) :
    {z : pathComponent e0 // f z.val ∈ V} ≃ₜ
      V × {i : I // (H.symm (v0, i)).val ∈ pathComponent e0} where
  toFun z := (⟨f z.val.val, z.property⟩, ⟨(H ⟨z.val.val, z.property⟩).2, by
    have hz := (coveringSheet_component_iff f V H e0 v0
      (H ⟨z.val.val, z.property⟩).1 (H ⟨z.val.val, z.property⟩).2).mp
    exact hz (by simp)⟩)
  invFun z := ⟨⟨(H.symm (z.1, z.2.val)).val,
      (coveringSheet_component_iff f V H e0 v0 z.1 z.2.val).mpr z.2.property⟩, by
    have hh := hH (H.symm (z.1, z.2.val))
    have hh' : f (H.symm (z.1, z.2.val)) = z.1.val := by
      simpa using hh.symm
    change f _ ∈ V
    rw [hh']
    exact z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    have hh : (⟨f z.val.val, z.property⟩, (H ⟨z.val.val, z.property⟩).2) =
        H ⟨z.val.val, z.property⟩ := by
      apply Prod.ext
      · exact Subtype.ext (hH ⟨z.val.val, z.property⟩).symm
      · rfl
    simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      have hh := hH (H.symm (z.1, z.2.val))
      simpa using hh.symm
    · apply Subtype.ext
      simp
  continuous_toFun := by
    have hf : Continuous (fun z : f ⁻¹' V ↦ f z) := by
      have hh := (continuous_subtype_val.comp (continuous_fst.comp H.continuous))
      exact hh.congr (fun z ↦ hH z)
    have hc : Continuous (fun z : {z : pathComponent e0 // f z.val ∈ V} ↦
        (⟨z.val.val, z.property⟩ : f ⁻¹' V)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact ((hf.comp hc).subtype_mk _).prodMk
      ((continuous_snd.comp (H.continuous.comp hc)).subtype_mk _)
  continuous_invFun := by
    exact ((continuous_subtype_val.comp (H.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _).subtype_mk _

end HolomorphicAnosov
