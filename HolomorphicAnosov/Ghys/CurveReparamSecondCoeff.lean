import HolomorphicAnosov.Ghys.CurveJetReparametrizationData
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The normalized second derivative of the rational source map. (Ghys, §3 p.591) -/

namespace HolomorphicAnosov.Ghys

/-- The normalized second derivative at zero of `omega*z/(1+mu*z)` is `-omega*mu`. (Ghys, §3 p.591)
-/
theorem reparam_second_coeff (p : CurveJetReparametrization) :
    iteratedDeriv 2 p.apply 0 / 2 = -(p.omega : ℂ) * p.mu := by
  let n : ℂ → ℂ := fun z ↦ (p.omega : ℂ) * z
  let d : ℂ → ℂ := fun z ↦ 1 + p.mu * z
  let q : ℂ → ℂ := fun z ↦ (d z)⁻¹
  have hn : ContDiffAt ℂ 2 n 0 := by fun_prop
  have hd : ContDiffAt ℂ 2 d 0 := by fun_prop
  have hq : ContDiffAt ℂ 2 q 0 := hd.fun_inv (by simp [d])
  have hq1 : deriv q 0 = -p.mu := by
    change deriv (fun z ↦ (d z)⁻¹) 0 = _
    rw [deriv_fun_inv'' (hd.differentiableAt (by norm_num)) (by simp [d])]
    simp [d]
  change iteratedDeriv 2 (n * q) 0 / 2 = _
  rw [iteratedDeriv_mul hn hq]
  simp [Finset.sum_range_succ, n, iteratedDeriv_succ, hq1]
  ring

end HolomorphicAnosov.Ghys

