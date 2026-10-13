import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped ContDiff Topology _root_.Topology Manifold
open Filter IsManifold

namespace HolomorphicAnosov

/-- Every fixed projective special linear transformation is holomorphic in the homogeneous-
coordinate complex atlas. (Demailly, V §15.A, p. 277; Ghys, §5, p. 597) -/
theorem projective_special_linear_action_contMDiff
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
    ContMDiff (complexModel 1) (complexModel 1) ∞
      (fun p : ComplexProjectiveLine ↦ g • p) := by
  induction g using QuotientGroup.induction_on with
  | H A =>
    intro p
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, p ∈ complexProjectiveLineChartSource j := by
      rcases complexProjectiveLineChart_cover p with h | h
      · exact ⟨1, h⟩
      · exact ⟨0, h⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin 2,
        A • p ∈ complexProjectiveLineChartSource k := by
      rcases complexProjectiveLineChart_cover (A • p) with h | h
      · exact ⟨1, h⟩
      · exact ⟨0, h⟩
    let V : ComplexModel 1 → ComplexModel 2 := fun z ↦
      Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (complexProjectiveLineChartVector j z)
    have hv (z : ComplexModel 1) : V z ≠ 0 :=
      (A.toLin'_equiv.val.map_ne_zero_iff).mpr (complexProjectiveLineChartVector_ne_zero j z)
    have haction (z : ComplexModel 1) :
        A • complexProjectiveLineChartInv j z = complexProjectiveLineMk (V z) (hv z) := by
      rw [Projectivization.matrixSpecialLinearGroup_smul_def]
      change A.toLin'_equiv • Projectivization.mk ℂ _ _ = _
      rw [Projectivization.smul_mk]
      rfl
    have hden : V (complexProjectiveLineChartFun j p) k ≠ 0 := by
      apply (projective_source_mk k _ _).mp
      rw [← haction, projective_left_inv j p hj]
      exact hk
    have hV : ContDiff ℂ ∞ V := by
      apply contDiff_pi.mpr
      intro i
      dsimp [V, Matrix.mulVec, dotProduct]
      apply ContDiff.sum
      intro l hl
      apply contDiff_const.mul
      dsimp [complexProjectiveLineChartVector]
      split_ifs
      · exact contDiff_const
      · exact contDiff_apply ℂ ℂ 0
    let R : ComplexModel 1 → ComplexModel 1 := fun z _ ↦ V z (k + 1) / V z k
    have hR : ContDiffAt ℂ ∞ R (complexProjectiveLineChartFun j p) := by
      apply contDiffAt_pi.mpr
      intro i
      exact ((contDiff_apply ℂ ℂ (k + 1)).comp hV).contDiffAt.div
        ((contDiff_apply ℂ ℂ k).comp hV).contDiffAt hden
    have hjatlas : complexProjectiveLineChart j ∈
        maximalAtlas (complexModel 1) ∞ ComplexProjectiveLine :=
      subset_maximalAtlas ⟨j, rfl⟩
    have hkatlas : complexProjectiveLineChart k ∈
        maximalAtlas (complexModel 1) ∞ ComplexProjectiveLine :=
      subset_maximalAtlas ⟨k, rfl⟩
    have hc := contMDiffAt_of_mem_maximalAtlas hjatlas hj
    have hr := hR.contMDiffAt.comp p hc
    have hi := contMDiffAt_symm_of_mem_maximalAtlas hkatlas
      (show R (complexProjectiveLineChartFun j p) ∈ (complexProjectiveLineChart k).target
        from Set.mem_univ _)
    have hcomp := hi.comp p hr
    apply hcomp.congr_of_eventuallyEq
    have hd : ∀ᶠ q in 𝓝 p, V (complexProjectiveLineChartFun j q) k ≠ 0 :=
      ((contDiff_apply ℂ ℂ k).comp hV).continuous.continuousAt.comp hc.continuousAt
        |>.eventually_ne hden
    filter_upwards [(projective_source_open j).mem_nhds hj, hd] with q hq hdq
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change A • q = complexProjectiveLineChartInv k (R (complexProjectiveLineChartFun j q))
    rw [← projective_left_inv j q hq, haction]
    simpa only [projective_right_inv, projective_fun_mk, R] using
      (projective_left_inv k _ ((projective_source_mk k _ (hv _)).mpr hdq)).symm


end HolomorphicAnosov
