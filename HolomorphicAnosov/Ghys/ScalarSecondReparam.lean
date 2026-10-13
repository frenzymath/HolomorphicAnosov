import HolomorphicAnosov.Ghys.CurveJetReparametrizationData
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The second scalar coefficient under rational source reparametrization (Ghys, §3) -/

namespace HolomorphicAnosov.Ghys

/-- The second Taylor coefficient of scalar precomposition is the ordinary second-derivative chain rule divided by two. (Ghys, §3) -/
theorem scalar_second_reparam (p : CurveJetReparametrization)
    (φ : ℂ → ℂ) (hφ : ContDiffAt ℂ 2 φ 0) :
    germSecond ((φ : ScalarGerm).compTendsto p.apply p.tendsto_zero) =
      (iteratedDeriv 2 φ 0 * deriv p.apply 0 ^ 2 +
        deriv φ 0 * iteratedDeriv 2 p.apply 0) / 2 := by
  change iteratedDeriv 2 (φ ∘ p.apply) 0 / 2 = _
  have hp0 : p.apply (0 : ℂ) = 0 := by simp [CurveJetReparametrization.apply]
  have hφ' : ContDiffAt ℂ 2 φ (p.apply 0) := by simpa [hp0] using hφ
  rw [iteratedDeriv_comp_two hφ'
    ((contDiffAt_const.mul contDiffAt_id).div
      (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) (by simp))]
  rw [hp0]


end HolomorphicAnosov.Ghys
