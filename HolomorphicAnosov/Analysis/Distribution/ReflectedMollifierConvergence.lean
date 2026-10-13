import HolomorphicAnosov.Analysis.Distribution.TestFunctionFixedSupportConvergence
import HolomorphicAnosov.Analysis.Distribution.ReflectedMollifierSupport
import HolomorphicAnosov.Analysis.Distribution.ReflectedAverageUniformConvergence
import HolomorphicAnosov.Analysis.Distribution.ReflectedMollifierChangeVariables
import HolomorphicAnosov.Analysis.Distribution.ReflectedAverageDerivatives

/-!
# Reflected mollifiers converge in the test-function topology

Source: Dyatlov, *Lecture notes for 18.155: distributions, elliptic regularity,
and applications to PDEs*, 2 October 2026, proof of Theorem 6.7, p.73,
equations (6.19), (6.25). DAG node:
`analysis.test_function_reflected_mollifier_tendsto_g11`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology



namespace HolomorphicAnosov.Analysis.Distribution

/-- Reflected mollification converges in the canonical LF topology of complex
smooth test functions on an open Euclidean domain. No evenness of the kernel
is assumed, and the convolution formula need hold only eventually as the scale
approaches zero through positive values.

Source: Dyatlov, proof of Theorem 6.7, p.73, equations (6.19), (6.25).

Proof: Let L be the compact support of φ. Choose δ > 0 so that the closed
δ-neighborhood K of L is compact and contained in U. When φ is zero use the
zero test directly. For 0 < ε < δ, the integral vanishes outside K: if φ(p)
is nonzero and y lies outside K, then ‖p-y‖ > ε, so the scaled kernel vanishes.
Thus all sufficiently small η ε have support in the same compact K.

Translation and positive dilation rewrite the integral as ∫ z, ρ(z) φ(y+εz).
Differentiating in y under this compact integral gives its jth real derivative
as ∫ z, ρ(z) Dʲφ(y+εz). This is justified in each finite order by a uniform
bound on the continuous derivatives over a compact neighborhood of y and the
unit ball in z; multiplying that bound by the compactly supported ρ gives an
integrable dominating function. Normalization and nonnegativity then bound
the norm of the derivative error by the supremum of
‖Dʲφ(y+εz)-Dʲφ(y)‖ for ‖z‖ ≤ 1. Each derivative of φ is continuous with
compact support, hence uniformly continuous on the full Euclidean space.
Therefore these bounds tend to zero uniformly in y in every finite order.

The seminorm characterization for ContDiffMapSupportedIn gives convergence in
the fixed-support smooth space on K. Its canonical continuous linear inclusion
into TestFunction U gives the asserted LF convergence. Altering a family away
from an eventual positive neighborhood does not affect its limit. The same
argument includes m = 0; for an empty domain all test functions are zero. -/
theorem testFunction_reflected_mollifier_tendsto
    {m : ℕ} (U : Opens (EuclideanSpace ℝ (Fin m)))
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (hρ_norm : ∫ x, ρ x ∂volume = 1)
    (φ : TestFunction U ℂ ⊤) (η : ℝ → TestFunction U ℂ ⊤)
    (hη : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      η ε y = ∫ p, φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ))) :
    Tendsto η (𝓝[>] (0 : ℝ)) (𝓝 φ) := by
  have hηavg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      η ε y = ∫ z, ρ z • φ (y + ε • z) := by
    filter_upwards [hη, self_mem_nhdsWithin] with ε hε hεpos
    intro y
    rw [hε y]
    exact reflected_mollifier_change_variables ρ φ hεpos y
  obtain ⟨K, hKU, hφK, hηK⟩ :=
    testFunction_reflected_mollifier_eventual_support U ρ hρ_support φ η hη
  apply testFunction_tendsto_of_eventual_fixed_support U K hKU φ η _ hφK hηK
  intro j t ht
  have huc : UniformContinuous (iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin m) → ℂ)) :=
    (φ.hasCompactSupport.iteratedFDeriv j).uniformContinuous_of_continuous
      (φ.contDiff.continuous_iteratedFDeriv (by simp))
  have havg := reflected_average_uniform_approximation ρ hρ_nonneg hρ_support hρ_norm
    (iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin m) → ℂ)) huc t ht
  have hformula : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      iteratedFDeriv ℝ j (η ε : EuclideanSpace ℝ (Fin m) → ℂ) y =
        ∫ z, ρ z • iteratedFDeriv ℝ j (φ : EuclideanSpace ℝ (Fin m) → ℂ)
          (y + ε • z) := by
    filter_upwards [hηavg] with ε hε
    intro y
    rw [show (η ε : EuclideanSpace ℝ (Fin m) → ℂ) =
      (fun y ↦ ∫ z, ρ z • φ (y + ε • z)) from funext hε]
    exact iteratedFDeriv_reflected_average U ρ φ ε j y
  filter_upwards [havg, hformula] with ε hε hf
  intro y
  rw [hf y]
  exact hε y

end HolomorphicAnosov.Analysis.Distribution

