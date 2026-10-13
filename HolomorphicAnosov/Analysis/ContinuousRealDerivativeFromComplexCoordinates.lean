import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Basic

namespace HolomorphicAnosov.Analysis

/-- A finite family of jointly continuous scalar complex derivatives yields a
jointly continuous full real derivative, on the same parameter domain.

This agent-written finite-coordinate and scalar-restriction application fills
the real differential step in Ghys Lemma 3.3, pp.592–593, after Demailly I §3.B,
pp.22–23 has supplied scalar derivative continuity. Assemble the scalar
derivatives continuously as a vector. The singleton-span linear isometry maps
that vector to the complex differential; restriction of scalars is continuous
and equals the real differential by complex differentiability. The parameter
space is arbitrary, no transverse derivative is needed, and the finite index
type may be empty. DAG: `analysis.real_derivative_from_complex_coordinates_g18`.
-/
theorem continuousOn_real_derivative_of_complex_coordinates
    {T J : Type*} [TopologicalSpace T] [Fintype J]
    (H : ℂ × T → (J → ℂ)) (Ω : Set (ℂ × T))
    (hdiff : ∀ p ∈ Ω, DifferentiableAt ℂ (fun z ↦ H (z,p.2)) p.1)
    (hscalar : ∀ k, ContinuousOn
      (fun p : ℂ × T ↦ deriv (fun z ↦ H (z,p.2) k) p.1) Ω) :
    ContinuousOn (fun p : ℂ × T ↦ fderiv ℝ (fun z ↦ H (z,p.2)) p.1) Ω := by
  have hv : ContinuousOn
      (fun p : ℂ × T ↦ fun k : J ↦ deriv (fun z ↦ H (z,p.2) k) p.1) Ω :=
    continuousOn_pi.mpr hscalar
  have hc : ContinuousOn
      (fun p : ℂ × T ↦ fderiv ℂ (fun z ↦ H (z,p.2)) p.1) Ω := by
    apply ((ContinuousLinearMap.toSpanSingletonLIE ℂ (J → ℂ)).continuous.comp_continuousOn hv).congr
    intro p hp
    symm
    change ContinuousLinearMap.toSpanSingleton ℂ
      (fun k ↦ deriv (fun z ↦ H (z,p.2) k) p.1) = _
    rw [← deriv_pi (differentiableAt_pi.mp (hdiff p hp)), toSpanSingleton_deriv]
  apply ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hc).congr
  intro p hp
  exact (hdiff p hp).fderiv_restrictScalars (𝕜 := ℝ)

end HolomorphicAnosov.Analysis

