import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-! Local sheets for pullback coverings. -/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {S : Type u} {Y : Type v} {L : Type w}
variable [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace L]

/-- Pull back an evenly covered chart, retaining its sheet label (Bredon II §14 pp.111–112; Hatcher pp.60–62).-/
def intrinsicPullbackSheet {I : Type*} [TopologicalSpace I]
    (j : L → S) (p : Y → S) (hj : Continuous j)
    (U : Set S) (V : Set L) (hVU : V ⊆ j ⁻¹' U)
    (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ z, (H z).1.1 = p z) :
    {z : IntrinsicCoveringPullback j p // z.val.1 ∈ V} ≃ₜ V × I where
  toFun z := (⟨z.val.val.1, z.property⟩,
    (H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩).2)
  invFun z := ⟨⟨(z.1.val, (H.symm (⟨j z.1.val, hVU z.1.property⟩, z.2)).val), by
    have hh := hH (H.symm (⟨j z.1.val, hVU z.1.property⟩, z.2))
    simpa using hh⟩, z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hh : (⟨j z.val.val.1, hVU z.property⟩,
          (H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩).2) =
          H ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact hVU z.property⟩ := by
        apply Prod.ext
        · apply Subtype.ext
          exact z.val.property.trans (hH ⟨z.val.val.2, by
            change p z.val.val.2 ∈ U
            rw [← z.val.property]
            exact hVU z.property⟩).symm
        · rfl
      simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · rfl
    · simp
  continuous_toFun := by
    exact
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).prodMk (continuous_snd.comp (H.continuous.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)))
  continuous_invFun := by
    exact (((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (H.symm.continuous.comp
        (((hj.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
          continuous_snd)))).subtype_mk _).subtype_mk _

end HolomorphicAnosov
