import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Affine rigidity from vanishing second derivative

Source: Ghys, *Holomorphic Anosov systems* (1995), Lemma 3.2, p.591,
the affine transition between local solutions.
DAG: `analysis.holomorphic_affine_of_second_deriv_zero_g18`.
-/

namespace HolomorphicAnosov

/-- A holomorphic function on a connected open complex domain whose second
complex derivative vanishes and whose first derivative never vanishes is affine
with nonzero slope.

This agent-written proof expands the affine-transition rigidity in Ghys Lemma 3.2,
p.591. The derivative is holomorphic. Its derivative vanishes, so it is constant
on the connected open domain. Subtract the linear function with that constant
slope; equality of derivatives makes the difference constant. Evaluate the slope
at one point of the nonempty domain to prove it nonzero. The conclusion holds
only on the given domain and imposes no condition elsewhere. -/
theorem holomorphic_affine_of_second_deriv_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsConnected U) (hf : DifferentiableOn ℂ f U)
    (hsecond : ∀ z ∈ U, deriv (deriv f) z = 0)
    (hfirst : ∀ z ∈ U, deriv f z ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z ∈ U, f z = a * z + b := by
  obtain ⟨a, ha⟩ := hU.exists_is_const_of_deriv_eq_zero hc.isPreconnected
    (hf.deriv hU) hsecond
  obtain ⟨b, hb⟩ := hU.exists_eq_add_of_deriv_eq hc.isPreconnected hf
    ((differentiable_const a).mul differentiable_id).differentiableOn
    (show U.EqOn (deriv f) (deriv (fun z : ℂ ↦ a * z)) from by
      intro z hz
      simpa only [deriv_const_mul_id] using ha z hz)
  obtain ⟨z, hz⟩ := hc.nonempty
  exact ⟨a, b, by rw [← ha z hz]; exact hfirst z hz, fun z hz ↦ hb hz⟩

end HolomorphicAnosov

