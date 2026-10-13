import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness from continuous separate holomorphy

Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012, Chapter I
§3.B, pp.22–23, definitions (3.6)–(3.7), Cauchy/power-series formulas (3.8)–(3.9)
and their complex-analyticity conclusion.

The source and receiving spaces are the actual `ComplexModel` finite products,
with their original maximum norms. The slice domain is the exact preimage of the
arbitrary open source set under a single-coordinate update. No regularity outside
that set, positive dimension, or global product domain is required.
-/

namespace HolomorphicAnosov

open scoped ContDiff

/-- A continuous map on an arbitrary open finite-dimensional complex domain, holomorphic
in each single-coordinate slice, is infinitely complex differentiable there.

Source: Demailly, Chapter I §3.B, pp.22–23, especially (3.6)–(3.9). Both empty
coordinate index sets are permitted. The original `ComplexModel` and `complexModel`
use the same finite-product space and its identity model with corners; this theorem
uses the underlying normed-space calculus, without a replacement coordinate model.

Natural-language proof from the DAG:

Step 1: For every output coordinate k:Fin e define g_k(x)=f(x)(k). The product continuity criterion
gives ContinuousOn g_k s. Apply the finite-product differentiability criterion to each supplied
slice f∘update z j on its exact preimage to obtain DifferentiableOn ℂ (g_k∘update z j) there. No
change of source or subset occurs. When e=0 this family is empty and the final product criterion
already gives the result.

Step 2: If d=0, E has one element, so each g_k agrees everywhere with the constant value g_k(0).
Constant analyticity therefore gives AnalyticAt ℂ g_k x at every x; it requires no coordinate-line
hypothesis.

Step 3: If d≥1, fix x∈s. Since s is open in the finite-product sup norm, choose ε>0 with ball(x,ε)⊆s
and use the common radius R_j=ε/2. Every point of its closed polydisc has sup distance at most
ε/2<ε, so the closed polydisc lies in s. Apply the sourced polydisc Cauchy/power-series theorem to
g_k, center x and these radii; its analytic conclusion gives AnalyticAt ℂ g_k x. This is exactly the
local step of Demailly (3.8)–(3.9), not an application of the one-variable
DifferentiableOn.contDiffOn theorem.

Step 4: For every x∈s and k:Fin e, convert the resulting AnalyticAt ℂ g_k x to ContDiffAt ℂ ∞ g_k x,
using completeness of Complex. Restrict the local smooth Taylor data to s (neighborhood membership
and derivative identities restrict under subsets) to obtain ContDiffWithinAt there; universally
quantify x∈s, which is the definition of ContDiffOn ℂ ∞ g_k s.

Step 5: Use the finite-product ContDiffOn equivalence to conclude ContDiffOn ℂ ∞ f s from all scalar
coordinate conclusions. The theorem permits an empty index, so e=0 is covered; if s is empty the
pointwise statements are vacuous.
-/
theorem contDiffOn_of_continuousOn_separately_holomorphic {d e : ℕ}
    {s : Set (ComplexModel d)} (hs : IsOpen s) {f : ComplexModel d → ComplexModel e}
    (hf : ContinuousOn f s)
    (hsep : ∀ z : ComplexModel d, ∀ j : Fin d,
      DifferentiableOn ℂ (f ∘ Function.update z j) ((Function.update z j) ⁻¹' s)) :
    ContDiffOn ℂ ∞ f s := by
  classical
  by_cases hd : d = 0
  · subst d
    have hconst : f = fun _ ↦ f 0 := by
      funext z
      congr 1
      exact Subsingleton.elim z 0
    rw [hconst]
    exact contDiffOn_const
  · apply contDiffOn_pi.mpr
    intro k x hx
    have hg : ContinuousOn (fun z ↦ f z k) s := continuousOn_pi.mp hf k
    have hgsep : ∀ (z : ComplexModel d) (j : Fin d),
        DifferentiableOn ℂ (fun t : ℂ ↦ f (Function.update z j t) k)
          ((fun t : ℂ ↦ Function.update z j t) ⁻¹' s) := by
      intro z j
      exact differentiableOn_pi.mp (hsep z j) k
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
    have hclosed : PolydiscBoundaryCauchySeries.closedPolydisc x (fun _ ↦ ε / 2) ⊆ s := by
      intro w hw
      apply hball
      apply Metric.mem_ball.mpr
      have hdist : dist w x ≤ ε / 2 := by
        apply (dist_pi_le_iff (by positivity : 0 ≤ ε / 2)).mpr
        intro j
        simpa only [dist_eq_norm] using hw j
      linarith
    have han : AnalyticAt ℂ (fun z ↦ f z k) x :=
      (PolydiscCauchy.polydisc_cauchy_power_series (by omega : 1 ≤ d) s hs
        (fun z ↦ f z k) hg hgsep x (fun _ ↦ ε / 2) (fun _ ↦ by positivity)
        hclosed).2.2.2.2
    exact han.contDiffAt.contDiffWithinAt


end HolomorphicAnosov
