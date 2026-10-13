import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import HolomorphicAnosov.Analysis.Distribution.RegularPairingL2Bound

open Filter MeasureTheory TopologicalSpace Set
open scoped ContDiff Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.ConnectionFlatEstimates

/-- The regular pairing of smooth scalar connection curvature equals the distributional exterior
derivative pairing on an open coordinate domain. (Zhang, §2.1, p. 7; Demailly, I §2.B.1, eq.
(2.6), p. 15) -/
theorem smooth_curvature_pairing {d : ℕ} (Ω : Opens (Fin d → ℂ))
    (A : (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] ℂ) (hA : ContDiffOn ℝ ∞ A Ω)
    (v w : Fin d → ℂ) (φ : TestFunction Ω ℂ ⊤) :
    DistributionalSection.regularPairing Ω
      (fun z ↦ fderiv ℝ A z v w - fderiv ℝ A z w v) φ =
      -(∫ z, A z w * fderiv ℝ (φ : (Fin d → ℂ) → ℂ) z v) +
        (∫ z, A z v * fderiv ℝ (φ : (Fin d → ℂ) → ℂ) z w) := by
  have hv : ContDiffOn ℝ ∞ (fun z ↦ A z w) Ω := hA.clm_apply contDiffOn_const
  have hw : ContDiffOn ℝ ∞ (fun z ↦ A z v) Ω := hA.clm_apply contDiffOn_const
  have hdv : ContinuousOn (fun z ↦ fderiv ℝ (fun y ↦ A y w) z v) Ω :=
    (hv.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hdw : ContinuousOn (fun z ↦ fderiv ℝ (fun y ↦ A y v) z w) Ω :=
    (hw.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hintv : Integrable (fun z ↦ fderiv ℝ (fun y ↦ A y w) z v * φ z) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        (hdv.locallyIntegrableOn Ω.isOpen.measurableSet)
  have hintw : Integrable (fun z ↦ fderiv ℝ (fun y ↦ A y v) z w * φ z) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        (hdw.locallyIntegrableOn Ω.isOpen.measurableSet)
  rw [DistributionalSection.regularPairing,
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz ↦ by simp [φ.zero_on_compl hz])]
  have heq : (∫ z, (fderiv ℝ A z v w - fderiv ℝ A z w v) * φ z) =
      (∫ z, (fderiv ℝ (fun y ↦ A y w) z v -
        fderiv ℝ (fun y ↦ A y v) z w) * φ z) := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ Ω
    · have hd := (hA.differentiableOn (by simp) z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
      rw [fderiv_clm_apply hd (differentiableAt_const w),
        fderiv_clm_apply hd (differentiableAt_const v)]
      simp
    · simp [φ.zero_on_compl hz]
  rw [heq]
  simp_rw [sub_mul]
  rw [integral_sub hintv hintw,
    local_directional_integration_by_parts Ω _ hv φ v,
    local_directional_integration_by_parts Ω _ hw φ w]
  simp [sub_eq_add_neg]

end HolomorphicAnosov.ConnectionFlatEstimates
