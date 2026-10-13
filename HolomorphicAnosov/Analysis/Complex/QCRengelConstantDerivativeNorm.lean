import Mathlib.Analysis.Complex.AbsMax

namespace HolomorphicAnosov
open Set

/-!
# Holomorphic maps with constant derivative norm

Source: Lehto–Virtanen (1973), Chapter I §4.3, p.23.
DAG node: `analysis.qc_rengel_constant_derivative_norm_g11`.
-/

/-- The analytic last step of Rengel's equality argument: a holomorphic map whose
complex derivative has constant norm on a connected open domain is affine.
Source: Lehto–Virtanen (1973), I.§4.3, p.23, necessity in Rengel's equality.

Proof: the holomorphic derivative attains its constant norm at any point of the
nonempty domain. The maximum modulus principle makes the derivative constant.
Subtract its linear primitive and apply constancy of a function with zero derivative.
The zero norm case is included, with slope zero; positive norm gives a similarity. -/
theorem qc_rengel_constant_derivative_norm {U : Set ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hc : IsConnected U) (hf : DifferentiableOn ℂ f U)
    (hn : ∀ z ∈ U, ‖deriv f z‖ = r) :
    ∃ c d : ℂ, ‖c‖ = r ∧ ∀ z ∈ U, f z = c * z + d := by
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  have hconst : EqOn (deriv f) (fun _ ↦ deriv f z₀) U :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc.isPreconnected hU
      (hf.deriv hU) hz₀ (fun z hz ↦ by change ‖deriv f z‖ ≤ ‖deriv f z₀‖; rw [hn z hz, hn z₀ hz₀])
  obtain ⟨d, hd⟩ := hU.exists_eq_add_of_deriv_eq hc.isPreconnected hf
    ((differentiable_const (deriv f z₀)).mul differentiable_id).differentiableOn
    (show EqOn (deriv f) (deriv (fun z : ℂ ↦ deriv f z₀ * z)) U from by
      intro z hz
      simpa only [deriv_const_mul_id] using hconst hz)
  exact ⟨deriv f z₀, d, hn z₀ hz₀, fun z hz ↦ hd hz⟩

end HolomorphicAnosov
