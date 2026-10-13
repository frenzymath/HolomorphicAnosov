import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTestApply

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- Demailly I (2.5)–(2.6), p.15, in the exact scalar complex convention:
the two real integration-by-parts identities combine linearly into the
antiholomorphic identity. This operand needs only local smoothness, and every
integral is justified by the test's compact support. -/
theorem local_antiholomorphic_integration_by_parts {n : ℕ}
    (V : Opens (Fin n → ℂ)) (g : (Fin n → ℂ) → ℂ)
    (hg : ContDiffOn ℝ ∞ g (V : Set _)) (j : Fin n) (φ : TestFunction V ℂ ⊤) :
    (∫ x, Analysis.antiholomorphicPartial g j x * φ x) =
      -(∫ x, g x * scalarDbarTest V j φ x) := by
  let vx : Fin n → ℂ := Pi.single j 1
  let vy : Fin n → ℂ := Pi.single j Complex.I
  have hc (v : Fin n → ℂ) : ContinuousOn (fun x ↦ fderiv ℝ g x v) (V : Set _) :=
    (hg.continuousOn_fderiv_of_isOpen V.isOpen (by simp)).clm_apply continuousOn_const
  have hleft (v : Fin n → ℂ) :
      Integrable (fun x ↦ fderiv ℝ g x v * φ x) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      (φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        ((hc v).locallyIntegrableOn V.isOpen.measurableSet))
  have hright (v : Fin n → ℂ) :
      Integrable (fun x ↦ g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x v) volume := by
    simpa only [ContinuousLinearMap.mul_apply', TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply, le_top, ite_true, mul_comm] using
      ((TestFunction.lineDerivCLM ℂ v φ : TestFunction V ℂ ⊤).integrable_bilin (μ := volume)
        (ContinuousLinearMap.mul ℂ ℂ)
        (hg.continuousOn.locallyIntegrableOn V.isOpen.measurableSet))
  have hx := local_directional_integration_by_parts V g hg φ vx
  have hy := local_directional_integration_by_parts V g hg φ vy
  have heqleft :
      (∫ x, Analysis.antiholomorphicPartial g j x * φ x) =
      (2 : ℂ)⁻¹ * ((∫ x, fderiv ℝ g x vx * φ x) +
        Complex.I * (∫ x, fderiv ℝ g x vy * φ x)) := by
    calc
      _ = ∫ x, (2 : ℂ)⁻¹ * (fderiv ℝ g x vx * φ x +
          Complex.I * (fderiv ℝ g x vy * φ x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          dsimp [Analysis.antiholomorphicPartial, vx, vy]; ring
      _ = _ := by rw [integral_const_mul, integral_add (hleft vx)
          ((hleft vy).const_mul _), integral_const_mul]
  have heqright :
      (∫ x, g x * scalarDbarTest V j φ x) =
      (2 : ℂ)⁻¹ * ((∫ x, g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x vx) +
        Complex.I * (∫ x, g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x vy)) := by
    calc
      _ = ∫ x, (2 : ℂ)⁻¹ * (g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x vx +
          Complex.I * (g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x vy)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          dsimp only
          rw [scalarDbarTest_apply]
          dsimp [Analysis.antiholomorphicPartial, vx, vy]; ring
      _ = _ := by rw [integral_const_mul, integral_add (hright vx)
          ((hright vy).const_mul _), integral_const_mul]
  rw [heqleft, heqright, hx, hy]
  ring


end HolomorphicAnosov
