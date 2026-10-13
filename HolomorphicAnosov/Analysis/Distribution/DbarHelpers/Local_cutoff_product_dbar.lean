import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport

/-!
# If a coefficient is smooth and antiholomorphically closed on an open neighborhood of the support
of a test cutoff, the antiholomorphic derivative of the cutoff product equals the derivative of
the cutoff times the coefficient everywhere.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
differentiated cutoff identity. DAG node: `analysis.dbar_helper_local_cutoff_product_dbar_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
If a coefficient is smooth and antiholomorphically closed on an open neighborhood of the support
of a test cutoff, the antiholomorphic derivative of the cutoff product equals the derivative of
the cutoff times the coefficient everywhere.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
differentiated cutoff identity.

Proof/construction: On the closed cutoff support, both factors are differentiable. Expand the two
real directional derivatives by the product rule, regroup their Wirtinger combination, and use the
vanishing antiholomorphic derivative of the coefficient. Off the cutoff support, both the cutoff
and its product vanish locally; their derivatives are zero, proving the same equation there.
-/
theorem local_cutoff_product_dbar {n : ℕ}
    (U Q : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤)
    (hψQ : tsupport (ψ : (Fin n → ℂ) → ℂ) ⊆ Q)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiffOn ℝ ∞ f (Q : Set _))
    (hbar : ∀ x ∈ Q, ∀ j, antiholomorphicPartial f j x = 0)
    (j : Fin n) (x : Fin n → ℂ) :
    antiholomorphicPartial (fun y ↦ ψ y * f y) j x =
      antiholomorphicPartial ψ j x * f x := by
  by_cases hx : x ∈ tsupport (ψ : (Fin n → ℂ) → ℂ)
  · have hfx := (hf.contDiffAt (Q.isOpen.mem_nhds (hψQ hx))).differentiableAt (by simp)
    have hψx := ψ.contDiff.differentiable (by simp) x
    have hp : antiholomorphicPartial (fun y ↦ ψ y * f y) j x =
        antiholomorphicPartial ψ j x * f x + ψ x * antiholomorphicPartial f j x := by
      simp only [antiholomorphicPartial, fderiv_fun_mul hψx hfx,
        add_apply, smul_apply, smul_eq_mul]
      ring
    rw [hp, hbar x (hψQ hx) j, mul_zero, add_zero]
  · have hprod : (fun y ↦ ψ y * f y) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    simp only [antiholomorphicPartial, hprod.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
      fderiv_of_notMem_tsupport ℝ hx, zero_apply,
      mul_zero, add_zero, zero_div, zero_mul]


end HolomorphicAnosov.Analysis.Distribution
