import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport

/-!
# If a complex-valued cutoff equals one on an open set, every point of that set is outside the closed support of every antiholomorphic partial derivative of the cutoff.

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), pp.28–29: psi
equals one on omega and dbar psi vanishes there.
DAG node: `analysis.dbar_helper_cutoff_dbar_support_separated_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology BigOperators

namespace HolomorphicAnosov.Analysis

/--
If a complex-valued cutoff equals one on an open set, every point of that set is outside the
closed support of every antiholomorphic partial derivative of the cutoff.

Source: Demailly (2012), I §3.E (3.29), pp.28–29: psi equals one on omega and dbar psi vanishes
there.

Proof: Every point in the open set has a neighborhood in that set. On this neighborhood the cutoff
is constantly one, so its real derivative is zero. The two real directional derivatives defining
the antiholomorphic partial derivative are therefore zero throughout this neighborhood. The
derivative vanishes locally, which is exactly exclusion from its closed support.
-/
theorem cutoff_dbar_support_separated {n : ℕ} (ψ : (Fin n → ℂ) → ℂ)
    (O : Set (Fin n → ℂ)) (hO : IsOpen O) (hψ : ∀ z ∈ O, ψ z = 1)
    (j : Fin n) (z : Fin n → ℂ) (hz : z ∈ O) :
    z ∉ tsupport (antiholomorphicPartial ψ j) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hO.mem_nhds hz] with x hx
  have heq : ψ =ᶠ[𝓝 x] (fun _ ↦ (1 : ℂ)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hψ y hy
  simp only [antiholomorphicPartial, heq.fderiv_eq, fderiv_const_apply,
    zero_apply, mul_zero, add_zero, zero_div, Pi.zero_apply]


end HolomorphicAnosov.Analysis
