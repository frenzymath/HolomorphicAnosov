import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Mityagin, Claim 2, pp. 2–3: a nonzero analytic function on a connected domain has
some nonzero iterated derivative at every point of the domain.

Proof: if all derivative tensors vanish at `w`, choose a power-series ball there.
The diagonal Taylor series in terms of iterated derivatives has every term zero,
so uniqueness of sums makes the function zero throughout that ball. The analytic
identity theorem then makes it zero on the connected domain, contradicting the
nonzero witness. This includes the zeroth derivative. -/
theorem analytic_exists_iteratedFDeriv_ne_zero {N : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin N))) (A : EuclideanSpace ℝ (Fin N) → ℝ)
    (hUconn : IsConnected U) (hA : AnalyticOnNhd ℝ A U)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) {w : EuclideanSpace ℝ (Fin N)} (hw : w ∈ U) :
    ∃ n : ℕ, iteratedFDeriv ℝ n A w ≠ 0 := by
  by_contra! hzero
  obtain ⟨p, r, hp⟩ := hA w hw
  have hevent : A =ᶠ[𝓝 w] 0 := by
    filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)] with z hz
    have hsum := hp.hasSum_iteratedFDeriv (y := z - w) (by
      simpa only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hz)
    simp only [hzero, zero_apply, smul_zero,
      add_sub_cancel] at hsum
    exact hsum.unique hasSum_zero
  obtain ⟨x, hx, hAx⟩ := hA_nonzero
  exact hAx (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn.isPreconnected hw
    hevent hx)

end HolomorphicAnosov
