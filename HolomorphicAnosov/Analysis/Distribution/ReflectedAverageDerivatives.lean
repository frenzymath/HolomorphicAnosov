import HolomorphicAnosov.Analysis.Distribution.ReflectedAverageFirstDerivative

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis.Distribution

/-- Every derivative of a reflected test-function average is the average of that derivative.

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), proof of Theorem 6.7,
p.73, derivative estimate following (6.25). No positivity, normalization, or symmetry
is needed for this identity, and zero-dimensional spaces and zero scales are included.

Proof: induction on the derivative order. At order zero, the canonical zero-variable
multilinear isometry commutes with integration. At the successor step, the preceding
iterated derivative is smooth with compact support, so dominated differentiation of
the translated average applies. The currying isometry commutes with the integral,
identifying the result with the next iterated derivative. -/
theorem iteratedFDeriv_reflected_average
    {m : ℕ} (U : Opens (EuclideanSpace ℝ (Fin m)))
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (φ : TestFunction U ℂ ⊤) (ε : ℝ) (j : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ z, ρ z • φ (y + ε • z)) y =
      ∫ z, ρ z • iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin m) → ℂ)
        (y + ε • z) := by
  induction j generalizing y with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    let L := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin m)) ℂ).symm.toLinearIsometry
    have hL := L.integral_comp_comm (𝕜 := ℝ) (μ := volume)
      (fun z ↦ ρ z • φ (y + ε • z))
    simpa only [L, map_smul, LinearIsometryEquiv.coe_toLinearIsometry] using hL.symm
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, funext ih]
    rw [(hasFDerivAt_reflected_average ρ _
      (φ.contDiff.iteratedFDeriv_right (by simp))
      (φ.hasCompactSupport.iteratedFDeriv j) ε y).fderiv]
    let L := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin m)) ℂ).symm.toLinearIsometry
    have hL := L.integral_comp_comm (𝕜 := ℝ) (μ := volume)
      (fun z ↦ ρ z • fderiv ℝ (iteratedFDeriv ℝ j
        (φ : EuclideanSpace ℝ (Fin m) → ℂ)) (y + ε • z))
    simpa only [L, map_smul, LinearIsometryEquiv.coe_toLinearIsometry,
      iteratedFDeriv_succ_eq_comp_left, Function.comp_apply] using hL.symm

end HolomorphicAnosov.Analysis.Distribution
