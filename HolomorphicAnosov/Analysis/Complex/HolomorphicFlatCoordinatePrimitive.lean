import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Scalar primitive for a flat holomorphic coordinate

An expansion of the local differential-equation step in Ghys, *Holomorphic Anosov
systems* (1995), Lemma 3.2, p.591. DAG: analysis.holomorphic_flat_coordinate_primitive_g18.
-/

namespace HolomorphicAnosov

/-- A holomorphic coefficient on an open convex complex domain admits a holomorphic
function with nonvanishing derivative solving H″ = -2 A H′.

This agent-written proof expands Ghys, Lemma 3.2, p.591, where local solutions
are asserted. Take a holomorphic primitive P of -2 A, set E = exp P, and take a
primitive H of E. Openness turns both within derivatives into ordinary derivatives.
The exponential chain rule gives E′ = -2 A E; E never vanishes. Consequently
H′ = E and H″ = E′ on the open domain, proving the equation. Empty domains are
allowed. This does not assert injectivity on the whole domain: the inverse function
theorem is applied separately near a point. -/
theorem holomorphic_flat_coordinate_primitive {U : Set ℂ} {A : ℂ → ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hA : DifferentiableOn ℂ A U) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧
      ∀ z ∈ U, deriv H z ≠ 0 ∧ deriv (deriv H) z = (-2 : ℂ) * A z * deriv H z := by
  obtain ⟨P, hP⟩ := hconv.exists_forall_hasDerivWithinAt
    (hA.const_mul (-2 : ℂ))
  have hP' {z : ℂ} (hz : z ∈ U) : HasDerivAt P ((-2 : ℂ) * A z) z :=
    (hP z hz).hasDerivAt (hU.mem_nhds hz)
  have hE : DifferentiableOn ℂ (fun z ↦ Complex.exp (P z)) U := by
    intro z hz
    exact (hP' hz).cexp.differentiableAt.differentiableWithinAt
  obtain ⟨H, hH⟩ := hconv.exists_forall_hasDerivWithinAt hE
  have hH' {z : ℂ} (hz : z ∈ U) : HasDerivAt H (Complex.exp (P z)) z :=
    (hH z hz).hasDerivAt (hU.mem_nhds hz)
  refine ⟨H, (fun z hz ↦ (hH' hz).differentiableAt.differentiableWithinAt), ?_⟩
  intro z hz
  have hlocal : deriv H =ᶠ[nhds z] (fun w ↦ Complex.exp (P w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hH' hw).deriv
  refine ⟨by rw [(hH' hz).deriv]; exact Complex.exp_ne_zero _, ?_⟩
  rw [hlocal.deriv_eq, (hP' hz).cexp.deriv, (hH' hz).deriv]
  ring

end HolomorphicAnosov

