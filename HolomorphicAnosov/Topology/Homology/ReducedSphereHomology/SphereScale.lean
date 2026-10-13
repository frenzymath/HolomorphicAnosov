import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The actual positive-radius scaling homeomorphism, with native subtype
 topologies and no norm-model change. Hatcher Corollary 2.14's elementary
 positive-radius extension is this literal real scalar multiplication. -/
def sphereScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    {x : E // ‖x‖ = 1} ≃ₜ {x : E // ‖x‖ = r} where
  toFun x := ⟨r • x.val, by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, x.property]; simp⟩
  invFun y := ⟨r⁻¹ • y.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), y.property]
    exact inv_mul_cancel₀ hr.ne'⟩
  left_inv x := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  right_inv y := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  continuous_toFun := (continuous_const.smul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.smul continuous_subtype_val).subtype_mk _

end HolomorphicAnosov.Topology.Homology
