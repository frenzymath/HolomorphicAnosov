import Mathlib.Analysis.Distribution.TestFunction

/-!
# Iterated derivative bound for linear coordinate pullback

Source: Nenning–Rainer, On groups of Hölder diffeomorphisms and their regularity,
author manuscript dated 3 April 2018, §2.1 p.4 (multilinear operator norms),
Remark 2.12, formula (2.7), pp.7–8 (higher chain rule on Banach spaces),
specialized to a continuous linear inner map. The test seminorm is Mathlib's
native supremum of the derivative norm, not the source's combined Hölder norm.
-/

open Function Set TopologicalSpace
open scoped ContDiff

namespace HolomorphicAnosov.Analysis.Distribution

/--
Pullback by a real continuous linear equivalence between Banach spaces bounds
each derivative by the corresponding test seminorm times the operator-norm power.

Source: Nenning–Rainer (2018 author version), formula (2.7), pp.7–8, and the
multilinear operator norm in §2.1 p.4. This is its linear-inner-map specialization.

Proof: For positive derivative order, every higher derivative of the linear inner
map vanishes. Thus the displayed Faà di Bruno sum has only the all-ones index,
whose coefficient is i!/(i!·1)=1. The derivative of the composition is the original
derivative at e(x), with e inserted in every slot; symmetrization fixes this
symmetric derivative. For order zero this identity is evaluation. Its operator
norm is at most the original derivative norm times norm(e)^i. The native fixed
support test seminorm bounds the original derivative at every point; multiplying
by the nonnegative operator-norm power proves the claim. Completeness is retained
to match the source's Banach hypotheses, although the native identity is stronger.
-/
theorem coordinatePullback_iterated_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (K : Compacts F)
    (φ : ContDiffMapSupportedIn F ℂ ⊤ K) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i ((φ : F → ℂ) ∘ e) x‖ ≤
      ‖e.toContinuousLinearMap‖ ^ i *
        (ContDiffMapSupportedIn.seminorm ℂ F ℂ ⊤ K i) φ := by
  classical
  rw [show iteratedFDeriv ℝ i ((φ : F → ℂ) ∘ e) x =
      (iteratedFDeriv ℝ i (φ : F → ℂ) (e x)).compContinuousLinearMap
        (fun _ ↦ e.toContinuousLinearMap) from
    e.toContinuousLinearMap.iteratedFDeriv_comp_right φ.contDiff x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i φ (e x)‖ * ‖e.toContinuousLinearMap‖ ^ i := by
      simpa using (iteratedFDeriv ℝ i φ (e x)).norm_compContinuousLinearMap_le
        (fun _ ↦ e.toContinuousLinearMap)
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
        (pow_nonneg (norm_nonneg _) _)


end HolomorphicAnosov.Analysis.Distribution
