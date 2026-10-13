import HolomorphicAnosov.Ghys.CurveJetReparametrizationData
import Mathlib.Analysis.Calculus.Deriv.Inv

open scoped ContDiff
namespace HolomorphicAnosov.Ghys
/-! Ghys, Holomorphic Anosov systems (1995), §3, printed p.591: first coefficient of the rational source action on scalar germs. -/

/-- (Ghys, §3) -/
theorem scalar_first_reparam (p : CurveJetReparametrization)
    (φ : ℂ → ℂ) (hφ : ContDiffAt ℂ 2 φ 0) :
    germFirst ((φ : ScalarGerm).compTendsto p.apply p.tendsto_zero) =
      deriv φ 0 * deriv p.apply 0 := by
  change deriv (φ ∘ p.apply) 0 = _
  have hp0 : p.apply (0 : ℂ) = 0 := by simp [CurveJetReparametrization.apply]
  have hp : DifferentiableAt ℂ p.apply (0 : ℂ) := by
    unfold CurveJetReparametrization.apply
    fun_prop (disch := norm_num)
  rw [deriv_comp (𝕜 := ℂ) 0 (by simpa [hp0] using hφ.differentiableAt (by norm_num))
    hp]
  rw [hp0]

end HolomorphicAnosov.Ghys
