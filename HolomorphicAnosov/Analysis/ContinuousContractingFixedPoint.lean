import Mathlib.Topology.MetricSpace.Contracting

/-!
# Continuous dependence of contraction fixed points

DAG node: `analysis.continuous_contracting_fixed_point_g20`.
Source: Fisher–Hasselblatt, *Hyperbolic flows*, author text December 20 2018,
Proposition 12.1.3(1)–(2), printed pp.578–579, residual estimate (12.1.2).
The printed proof obtains (1) from residual estimate (12.1.2) and obtains
continuity (2) from (1). The extension from a metric parameter to any topology
uses exactly the same neighborhood argument, with continuity only at each
fixed state. The caller CommonBallInverse applies it on one common complete
closed-ball carrier; neither the state space nor its metric changes with the parameter.
-/

namespace HolomorphicAnosov.Analysis

open scoped _root_.Topology NNReal

/-- The fixed points of uniformly contracting maps depend continuously on their
parameter if each evaluation at a fixed state does. The parameter may have any
topology. Source: Fisher–Hasselblatt, *Hyperbolic flows* (2018), Proposition
12.1.3(1)–(2), pp.578–579. The residual-estimate proof uses the Mathlib
`ContractingWith.fixedPoint` and `dist_fixedPoint_le` APIs.

Complete natural-language proof: fix a parameter p₀ and put x₀ equal to the
distinguished fixed point of f(p₀,·). Its fixed-point equation gives
f(p₀,x₀)=x₀. Since K<1, the residual bound at any p gives distance from
x₀ to the fixed point of f(p,·) at most dist(x₀,f(p,x₀))/(1-K).
For ε>0, continuity of p↦f(p,x₀) gives a neighborhood of p₀ on which
dist(f(p,x₀),f(p₀,x₀))<ε(1-K). Substitute the fixed-point equation,
use symmetry of distance, and divide by the positive number 1-K. This
proves continuity at p₀, hence continuity everywhere. For an empty parameter
space there are no points at which continuity must be checked. The constant
K=0 and a singleton state space require no separate argument. -/
theorem continuous_contracting_fixedPoint
    {P E : Type*} [TopologicalSpace P] [MetricSpace E] [Nonempty E] [CompleteSpace E]
    {K : ℝ≥0} (f : P → E → E) (hf : ∀ p, ContractingWith K (f p))
    (hc : ∀ x, Continuous (fun p ↦ f p x)) :
    Continuous (fun p ↦ (hf p).fixedPoint (f p)) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let x₀ : E := (hf p₀).fixedPoint (f p₀)
  have hx₀ : f p₀ x₀ = x₀ := (hf p₀).fixedPoint_isFixedPt
  apply Metric.continuousAt_iff'.2
  intro ε hε
  have hK : 0 < (1 : ℝ) - K := (hf p₀).one_sub_K_pos
  have hεK : 0 < ε * ((1 : ℝ) - K) := mul_pos hε hK
  have hev : ∀ᶠ p in 𝓝 p₀, dist (f p x₀) (f p₀ x₀) < ε * ((1 : ℝ) - K) := by
    have hcont : ContinuousAt (fun p : P ↦ f p x₀) p₀ := (hc x₀).continuousAt
    have h := (Metric.continuousAt_iff'.1 hcont)
      (ε * ((1 : ℝ) - K)) hεK
    simpa [x₀] using h
  filter_upwards [hev] with p hp
  have hres : dist x₀ (f p x₀) < ε * ((1 : ℝ) - K) := by
    simpa [hx₀, dist_comm] using hp
  have hdiv : dist x₀ (f p x₀) / ((1 : ℝ) - K) < ε :=
    (div_lt_iff₀ hK).2 (by simpa [mul_comm] using hres)
  have hbound : dist x₀ ((hf p).fixedPoint (f p)) ≤
      dist x₀ (f p x₀) / ((1 : ℝ) - K) :=
    (hf p).dist_fixedPoint_le x₀
  have hmain : dist ((hf p).fixedPoint (f p))
      ((hf p₀).fixedPoint (f p₀)) < ε := by
    rw [dist_comm]
    exact hbound.trans_lt hdiv
  exact hmain


end HolomorphicAnosov.Analysis
