import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
Restriction of covering sheet charts to smaller base sets. (Bredon, II §14, pp.111–112; Hatcher,
pp.60–62)
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov
universe u v w
variable {E : Type u} {B : Type v} {I : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace I]

/-- The sheet chart over a base set restricts to a sheet chart with the same labels over any smaller
base set. (Bredon, II §14, pp.111–112; Hatcher, pp.60–62) -/
def coveringSheetRestrict (f : E → B) (hf : Continuous f)
    (U V : Set B) (hVU : V ⊆ U)
    (H : f ⁻¹' U ≃ₜ U × I) (hH : ∀ z, (H z).1.val = f z) :
    f ⁻¹' V ≃ₜ V × I where
  toFun z := (⟨f z, z.property⟩, (H ⟨z, hVU z.property⟩).2)
  invFun z := ⟨H.symm (⟨z.1, hVU z.1.property⟩, z.2), by
    have hh := hH (H.symm (⟨z.1, hVU z.1.property⟩, z.2))
    have hh' : f (H.symm (⟨z.1, hVU z.1.property⟩, z.2)) = z.1.val := by
      simpa using hh.symm
    change f _ ∈ V
    rw [hh']
    exact z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    have hh : (⟨f z, hVU z.property⟩, (H ⟨z, hVU z.property⟩).2) =
        H ⟨z, hVU z.property⟩ := by
      apply Prod.ext
      · exact Subtype.ext (hH ⟨z, hVU z.property⟩).symm
      · rfl
    simp only [hh, H.symm_apply_apply]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      have hh := hH (H.symm (⟨z.1, hVU z.1.property⟩, z.2))
      simpa using hh.symm
    · simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end HolomorphicAnosov
