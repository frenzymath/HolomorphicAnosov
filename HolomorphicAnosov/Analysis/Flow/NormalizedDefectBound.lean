import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized error obeys a genuine inhomogeneous linear differential inequality.
The derivative of the error is obtained by subtracting the nonlinear and linear IVPs.
The remainder premise is a pointwise Taylor estimate, supplied uniformly by the previous lemma. -/
theorem normalized_defect_bound
    (F : E → E) (α β γ : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (T K ε C : ℝ) (hT : 0 ≤ T) (_hK : 0 ≤ K) (hε : 0 ≤ ε) (_hC : 0 ≤ C)
    (h : E) (hh : h ≠ 0)
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (F (α t)) t)
    (hβ : ∀ t ∈ Icc 0 T, HasDerivAt β (F (β t)) t)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivAt γ (A t (γ t)) t)
    (hinit : β 0 - α 0 = h) (hγinit : γ 0 = h)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hgap : ∀ t ∈ Icc 0 T, ‖β t - α t‖ ≤ C * ‖h‖)
    (hrem : ∀ t ∈ Icc 0 T,
      ‖F (β t) - F (α t) - A t (β t - α t)‖ ≤ ε * ‖β t - α t‖) :
    ‖‖h‖⁻¹ • (β T - α T - γ T)‖ ≤ gronwallBound 0 K (ε * C) T := by
  let e : ℝ → E := fun t ↦ ‖h‖⁻¹ • (β t - α t - γ t)
  let e' : ℝ → E := fun t ↦ ‖h‖⁻¹ • (F (β t) - F (α t) - A t (γ t))
  have he : ∀ t ∈ Icc 0 T, HasDerivAt e (e' t) t := fun t ht ↦
    (((hβ t ht).sub (hα t ht)).sub (hγ t ht)).const_smul _
  have hecont : ContinuousOn e (Icc 0 T) :=
    fun t ht ↦ (he t ht).continuousAt.continuousWithinAt
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hbound : ∀ t ∈ Ico 0 T, ‖e' t‖ ≤ K * ‖e t‖ + ε * C := by
    intro t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
    let R := F (β t) - F (α t) - A t (β t - α t)
    have heq : e' t = A t (e t) + ‖h‖⁻¹ • R := by
      dsimp [e', e, R]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [map_sub]
      abel
    rw [heq]
    calc
      ‖A t (e t) + ‖h‖⁻¹ • R‖ ≤ ‖A t (e t)‖ + ‖‖h‖⁻¹ • R‖ := norm_add_le _ _
      _ ≤ K * ‖e t‖ + ‖h‖⁻¹ * ‖R‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
        have hop := ((A t).le_opNorm (e t)).trans
          (mul_le_mul_of_nonneg_right (hA t ht') (norm_nonneg (e t)))
        linarith
      _ ≤ K * ‖e t‖ + ε * C := by
        have hr := (hrem t ht').trans (mul_le_mul_of_nonneg_left (hgap t ht') hε)
        have hi := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hnorm.le)
        have hs : ‖h‖⁻¹ * (ε * (C * ‖h‖)) = ε * C := by
          field_simp
        dsimp [R]
        linarith [hs ▸ hi]
  simpa only [e, sub_zero] using
    norm_le_gronwallBound_of_norm_deriv_right_le hecont
      (fun t ht ↦ (he t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      (by simp [e, hinit, hγinit]) hbound T ⟨hT, le_rfl⟩

end FirstVariationalDefect
