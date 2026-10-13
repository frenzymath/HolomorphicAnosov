import HolomorphicAnosov.Topology.UnitSphereLinearNeZero
import HolomorphicAnosov.Topology.UnitSphereNormalizeInverse
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Basic

namespace HolomorphicAnosov

open Set

/-- A continuous linear change of norm induces the explicit radial homeomorphism
between the original unit-sphere subtypes.

Source: the norm-conversion step of `topo.unit_sphere_simply_connected_g9`, expanding
the elementary coordinate geometry accompanying Hatcher Proposition 1.14 p.35.
Normalize the forward and inverse linear maps. Their images have norm one; the
previous cancellation proves both inverse identities. Norms and linear maps are
continuous, and the denominators never vanish on either unit sphere. -/
theorem unit_sphere_radial_homeomorph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    ∃ h : {v : E // ‖v‖ = 1} ≃ₜ {w : F // ‖w‖ = 1},
      (∀ v, (h v).val = ‖e v.val‖⁻¹ • e v.val) ∧
      (∀ w, (h.symm w).val = ‖e.symm w.val‖⁻¹ • e.symm w.val) := by
  let h : {v : E // ‖v‖ = 1} ≃ₜ {w : F // ‖w‖ = 1} :=
    { toFun := fun v ↦ ⟨‖e v.val‖⁻¹ • e v.val, norm_smul_inv_norm (unit_sphere_linear_ne_zero e v)⟩
      invFun := fun w ↦
        ⟨‖e.symm w.val‖⁻¹ • e.symm w.val, norm_smul_inv_norm (unit_sphere_linear_ne_zero e.symm w)⟩
      left_inv := fun v ↦ Subtype.ext (unit_sphere_normalize_inverse e v.val v.property)
      right_inv := fun w ↦
        Subtype.ext (unit_sphere_normalize_inverse e.symm w.val w.property)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((e.continuous.comp continuous_subtype_val).norm.inv₀
          (fun v ↦ norm_ne_zero_iff.mpr (unit_sphere_linear_ne_zero e v))).smul
            (e.continuous.comp continuous_subtype_val)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact ((e.symm.continuous.comp continuous_subtype_val).norm.inv₀
          (fun w ↦ norm_ne_zero_iff.mpr (unit_sphere_linear_ne_zero e.symm w))).smul
            (e.symm.continuous.comp continuous_subtype_val) }
  exact ⟨h, fun _ ↦ rfl, fun _ ↦ rfl⟩

end HolomorphicAnosov

