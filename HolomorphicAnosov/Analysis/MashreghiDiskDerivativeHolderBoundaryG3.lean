import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundary
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundaryTail
import HolomorphicAnosov.Analysis.MashreghiBoundary.AnglePoint
import HolomorphicAnosov.Analysis.MashreghiBoundary.RadialBoundaryAngular
import HolomorphicAnosov.Analysis.MashreghiBoundary.DiskExtension
import HolomorphicAnosov.Analysis.MashreghiBoundary.DiskExtensionContinuousOn

/-!
Public DAG node: `analysis.mashreghi_disk_derivative_holder_boundary_g3` (statement).
Source origin: Mashreghi Theorem 4.3 forward proof, printed pp.442-443, equations (4.6)-(4.7), as specialized in the unchanged canonical target.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
open MashreghiRadial
/-- A holomorphic function with integrable derivative growth extends continuously to the
closed unit disk, with explicit radial and local angular bounds.

Source: Mashreghi, *Generalized Lipschitz Functions*, Theorem 4.3, forward proof
pp.442–443, equations (4.6)–(4.7). Natural-language proof:

On the open disk, complex differentiability gives continuity. Fix a unit complex
number η and 0 ≤ u ≤ v < 1. The real radial path r ↦ rη has derivative η and remains
in the open disk on the entire closed interval [u,v]. The real/complex scalar-tower
chain rule gives derivative F′(rη)η. Its norm is at most C(1-r)^(α-1).
The majorant is continuous and integrable on this interval because 1-r > 0 there.
The norm-versus-integral estimate and the antiderivative −(C/α)(1-r)^α
give
  ‖F(vη)-F(uη)‖ ≤ (C/α)((1-u)^α-(1-v)^α) ≤ (C/α)(1-u)^α.
Every power here has a nonnegative base, and α > 0.

For r_n = 1-1/(n+2), these estimates and continuity of the positive power at zero
make F(r_nη) Cauchy, with a threshold independent of η. Completeness of ℂ supplies
a limit b(η) for each unit η. This value is indexed by η itself, so it is independent
of any angular representative. Passing v = r_n to the limit in the preceding
inequality gives ‖b(η)-F(ρη)‖ ≤ (C/α)(1-ρ)^α for every 0 ≤ ρ < 1. Define Fbar to
equal F in the open disk and b elsewhere; only closed-disk values are used.
This is a total function constructed without a pre-assumed boundary limit.

For θ < φ with h = φ-θ ∈ (0,1), take ρ = 1-h. The inner arc t ↦ ρ exp(it),
t ∈ [θ,φ], lies in the open disk. Its derivative has norm ρ, so the derivative of
F along it is bounded by Cρh^(α-1). Integration gives an inner increment at most
Cρh^α ≤ Ch^α. Adding the two radial tails yields
  ‖b(exp(iφ))-b(exp(iθ))‖ ≤ C(2/α+1)h^α.
For φ < θ exchange endpoints; for φ = θ both sides are zero since 0^α = 0.
No derivative on the boundary is used.

The agent-written completion of the source final continuity sentence is
`MashreghiRadial.diskExtension_continuousOn`: the radial estimate makes the
continuous functions η ↦ F(r_nη) converge uniformly to b on the unit circle, so b
is continuous there. For an arbitrary closed-disk approach z → η₀ with ‖η₀‖ = 1,
eventually r = ‖z‖ > 1/2 and η = z/r is unit, with r → 1 and η → η₀. The radial
estimate, also zero at r = 1, bounds
  ‖Fbar(z)-b(η₀)‖ ≤ (C/α)(1-r)^α + ‖b(η)-b(η₀)‖,
which tends to zero. At interior points Fbar agrees locally with the continuous F.
Thus Fbar is continuous on the whole closed disk. C = 0 and ρ = 0 are included;
the proof divides only by the strictly positive α and by r in the boundary-local
neighborhood. There is no assertion about arbitrary closed-disk pairs, boundary
analyticity, or injectivity.
-/
theorem mashreghi_disk_derivative_holder_boundary_g3
    (α C : ℝ) (hα : 0 < α) (hα_one : α < 1) (hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 →
      ‖deriv F z‖ ≤ C * Real.rpow (1 - ‖z‖) (α - 1)) :
    ∃ Fbar : ℂ → ℂ,
      Set.EqOn Fbar F {z : ℂ | ‖z‖ < 1} ∧
      ContinuousOn Fbar {z : ℂ | ‖z‖ ≤ 1} ∧
      (∀ η : ℂ, ‖η‖ = 1 → ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
        ‖Fbar η - F ((ρ : ℂ) * η)‖ ≤ (C / α) * Real.rpow (1 - ρ) α) ∧
      (∀ θ φ : ℝ, |φ - θ| < 1 →
        ‖Fbar (Complex.exp (Complex.I * (φ : ℂ))) -
          Fbar (Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
          C * (2 / α + 1) * Real.rpow |φ - θ| α) := by
  have anglePoint_norm (θ : ℝ) : ‖anglePoint θ‖ = 1 := by
    simp [anglePoint, Complex.norm_exp]
  have diskExtension_eq_boundary (F : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
      diskExtension F z = radialBoundary F z := by simp [diskExtension, hz]

  refine ⟨diskExtension F, ?_, diskExtension_continuousOn α C hα hα_one hC F hF hderiv,
    ?_, ?_⟩
  · intro z hz
    exact ite_eq_left hz
  · intro η hη ρ hρ hρ_one
    rw [diskExtension_eq_boundary F hη]
    exact radialBoundary_tail α C hα hα_one hC F hF hderiv η hη ρ hρ hρ_one
  · intro θ φ hsmall
    have hθ : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := anglePoint_norm θ
    have hφ : ‖Complex.exp (Complex.I * (φ : ℂ))‖ = 1 := anglePoint_norm φ
    rw [diskExtension_eq_boundary F hφ, diskExtension_eq_boundary F hθ]
    exact radialBoundary_angular α C hα hα_one hC F hF hderiv θ φ hsmall
end HolomorphicAnosov
