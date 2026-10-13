import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus
import HolomorphicAnosov.Analysis.Distribution.ExistsNestedBalls

/-!
# For every point of an open subset U of complex n-space there is a smaller open neighborhood P
and a smooth complex test on U equal to one throughout P.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
choice of cutoff. DAG node: `analysis.dbar_helper_exists_local_test_cutoff_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
For every point of an open subset U of complex n-space there is a smaller open neighborhood P and
a smooth complex test on U equal to one throughout P.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.E (3.29), p.28,
choice of cutoff.

Proof/construction: Choose r>0 with the closed ball of radius 4r at the point contained in U. The
native real bump with inner radius 2r and outer radius 3r, coerced to complex values, is a smooth
compactly supported test on U. Take P to be the ball of radius r. This ball contains the point,
lies in U, and is contained in the inner closed ball where the bump is one.
-/
theorem exists_local_test_cutoff {n : ℕ} (U : Opens (Fin n → ℂ))
    (a : Fin n → ℂ) (ha : a ∈ U) :
    ∃ (P : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤),
      a ∈ P ∧ P ≤ U ∧ (∀ z ∈ P, ψ z = 1) := by
  obtain ⟨r, hr, _, _, _, hball⟩ := HolomorphicAnosov.exists_nested_balls U ha
  let b : ContDiffBump a := ⟨2*r, 3*r, by positivity, by linarith⟩
  have hsupp : tsupport (fun x ↦ (b x : ℂ)) ⊆ (U : Set _) := by
    have hb : tsupport (fun x ↦ (b x : ℂ)) ⊆ tsupport (b : (Fin n → ℂ) → ℝ) := by
      apply closure_mono
      intro x hx
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hx
    apply hb.trans
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_closedBall (by dsimp [b]; linarith)).trans hball
  have hsm : ContDiff ℝ ∞ (fun x : Fin n → ℂ ↦ (b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : HasCompactSupport (fun x : Fin n → ℂ ↦ (b x : ℂ)) := by
    exact b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let ψ : TestFunction U ℂ ⊤ := ⟨fun x ↦ (b x : ℂ), hsm, hc, hsupp⟩
  let P : Opens (Fin n → ℂ) := ⟨Metric.ball a r, Metric.isOpen_ball⟩
  refine ⟨P, ψ, Metric.mem_ball_self hr, ?_, ?_⟩
  · intro x hx
    exact hball ((Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))) hx)
  · intro x hx
    change (b x : ℂ) = 1
    rw [b.one_of_mem_closedBall]
    · simp
    · exact Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by dsimp [b]; linarith)) hx)


end HolomorphicAnosov.Analysis.Distribution
