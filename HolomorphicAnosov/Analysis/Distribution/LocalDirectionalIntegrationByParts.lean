import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- Demailly I (2.6), p.15, for one real coordinate direction. All three
integrability guards are proved from the compact support of the test. The
coefficient need only be smooth on the open set; Mathlib's local-support
integration-by-parts theorem applies directly, without extending the coefficient. -/
theorem local_directional_integration_by_parts {n : ℕ}
    (V : Opens (Fin n → ℂ)) (g : (Fin n → ℂ) → ℂ)
    (hg : ContDiffOn ℝ ∞ g (V : Set _)) (φ : TestFunction V ℂ ⊤)
    (v : Fin n → ℂ) :
    (∫ x, g x * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x v) =
      -(∫ x, fderiv ℝ g x v * φ x) := by
  have hd : ContinuousOn (fun x ↦ fderiv ℝ g x v) (V : Set _) :=
    (hg.continuousOn_fderiv_of_isOpen V.isOpen (by simp)).clm_apply continuousOn_const
  have hi := (TestFunction.lineDerivCLM ℂ v φ : TestFunction V ℂ ⊤).integrable_bilin (μ := volume)
    (ContinuousLinearMap.mul ℂ ℂ)
    (hg.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)
  simp only [ContinuousLinearMap.mul_apply', TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, le_top, ite_true, mul_comm] at hi
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      (φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        (hd.locallyIntegrableOn V.isOpen.measurableSet))) hi
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      (φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        (hg.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)))
    (fun x hx ↦ (hg.differentiableOn (by simp) x (φ.tsupport_subset hx)).differentiableAt
      (V.isOpen.mem_nhds (φ.tsupport_subset hx)))
    (fun x _ ↦ (φ.contDiff.differentiable (by simp)).differentiableAt)


end HolomorphicAnosov
