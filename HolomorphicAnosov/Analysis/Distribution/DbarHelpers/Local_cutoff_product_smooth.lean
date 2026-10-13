import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.Basic

/-!
# A smooth compactly supported complex test function times a function smooth on an open
neighborhood of the test support is globally smooth and compactly supported, without any
regularity assumption on the second function outside that neighborhood.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
cutoff multiplication. DAG node: `analysis.dbar_helper_local_cutoff_product_smooth_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A smooth compactly supported complex test function times a function smooth on an open neighborhood
of the test support is globally smooth and compactly supported, without any regularity assumption
on the second function outside that neighborhood.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
cutoff multiplication.

Proof/construction: At a point in the closed test support, openness of the given neighborhood
makes the coefficient smooth at that point, so the product rule for smooth functions applies. At a
point outside the closed support, the test and hence the product vanish on a neighborhood, so the
product is smooth there. The support of the product lies in the compact support of the test.
-/
theorem local_cutoff_product_smooth {n : ℕ}
    (U Q : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤)
    (hψQ : tsupport (ψ : (Fin n → ℂ) → ℂ) ⊆ Q)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiffOn ℝ ∞ f (Q : Set _)) :
    ContDiff ℝ ∞ (fun x ↦ ψ x * f x) ∧
    HasCompactSupport (fun x ↦ ψ x * f x) := by
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, ψ.hasCompactSupport.mul_right⟩
  intro x
  by_cases hx : x ∈ tsupport (ψ : (Fin n → ℂ) → ℂ)
  · exact ψ.contDiff.contDiffAt.mul (hf.contDiffAt (Q.isOpen.mem_nhds (hψQ hx)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hx
    filter_upwards [hzero] with y hy
    simp [hy]


end HolomorphicAnosov.Analysis.Distribution
