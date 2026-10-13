import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientsEqOn

open Filter MeasureTheory TopologicalSpace Set
open scoped ContDiff Topology _root_.Topology
noncomputable section

namespace HolomorphicAnosov.ConnectionFlatEstimates

/-- A smooth one-form whose exterior derivative vanishes against every compactly supported smooth
test has zero classical exterior derivative. (Zhang, Lemma 2.3, p. 7; Demailly, I §2.B.1, eq.
(2.6), p. 15) -/
theorem smooth_oneForm_flat_of_weak_closed {n : ℕ}
    (Ω : Opens (Fin n → ℂ))
    (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω)
    (hclosed : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      -(∫ x, A x w * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x v) +
        (∫ x, A x v * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x w) = 0) :
    ∀ z ∈ Ω, ∀ v w : Fin n → ℂ,
      fderiv ℝ A z v w - fderiv ℝ A z w v = 0 := by
  intro z hz v w
  have hv : ContDiffOn ℝ ∞ (fun x ↦ A x w) Ω := hA.clm_apply contDiffOn_const
  have hw : ContDiffOn ℝ ∞ (fun x ↦ A x v) Ω := hA.clm_apply contDiffOn_const
  have hDv : ContinuousOn (fun x ↦ fderiv ℝ (fun y ↦ A y w) x v) Ω :=
    (hv.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hDw : ContinuousOn (fun x ↦ fderiv ℝ (fun y ↦ A y v) x w) Ω :=
    (hw.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  let R := fun x ↦ fderiv ℝ (fun y ↦ A y w) x v -
    fderiv ℝ (fun y ↦ A y v) x w
  have hR : ContinuousOn R Ω := hDv.sub hDw
  have hzero (φ : TestFunction Ω ℂ ⊤) :
      (∫ x in (Ω : Set (Fin n → ℂ)), R x * φ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by simp [φ.zero_on_compl hx])]
    dsimp only [R]
    simp_rw [sub_mul]
    rw [integral_sub
      (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
        (φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
          (hDv.locallyIntegrableOn Ω.isOpen.measurableSet)))
      (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
        (φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
          (hDw.locallyIntegrableOn Ω.isOpen.measurableSet)))]
    have h := hclosed v w φ
    rw [local_directional_integration_by_parts Ω _ hv φ v,
      local_directional_integration_by_parts Ω _ hw φ w] at h
    simpa only [neg_neg, sub_eq_add_neg] using h
  have heq : EqOn R (fun _ ↦ 0) Ω := by
    apply continuous_coefficients_eqOn_of_current Ω Ω le_rfl R (fun _ ↦ 0)
      hR continuousOn_const (0 : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    · intro φ
      simpa only [zero_apply] using (hzero φ).symm
    · intro φ _
      simp
  have hzA := (hA.differentiableOn (by simp) z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
  have h := heq hz
  dsimp only [R] at h
  rw [fderiv_clm_apply hzA (differentiableAt_const w),
    fderiv_clm_apply hzA (differentiableAt_const v)] at h
  simpa using h

end HolomorphicAnosov.ConnectionFlatEstimates

