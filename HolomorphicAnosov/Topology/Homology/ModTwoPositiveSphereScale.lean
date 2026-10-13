import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs
namespace HolomorphicAnosov.Topology.Homology
noncomputable def positiveSphereScaleHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r) : {x : E // ‖x‖ = 1} ≃ₜ {x : E // ‖x‖ = r} where
  toFun x := ⟨r • x.1, by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, x.2]; ring⟩
  invFun y := ⟨r⁻¹ • y.1, by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), y.2]; field_simp⟩
  left_inv x := by apply Subtype.ext; simp [smul_smul, hr.ne']
  right_inv y := by apply Subtype.ext; simp [smul_smul, hr.ne']
  continuous_toFun := (continuous_const.smul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.smul continuous_subtype_val).subtype_mk _
end HolomorphicAnosov.Topology.Homology
