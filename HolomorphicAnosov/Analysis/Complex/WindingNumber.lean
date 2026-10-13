import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Circle

/-!
# The integer winding of a continuous complex loop

Source: Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*,
§3.3 p.107, equation (3.1) and the normalized integer winding preceding
Proposition3.8. We realize that topological invariant through the actual
Mathlib exponential covering and path lift, including self-intersecting loops.
No differentiability or integral is required of the loop.
-/

namespace HolomorphicAnosov
noncomputable section

/-- Continuous maps from the actual unit circle to ℂ (Lyubich §3.3 p.107). -/
abbrev ComplexLoop := C(Circle, ℂ)

/-- Positive once-around parametrization with the omitted value subtracted.
Source: Lyubich §3.3 p.107; `Circle.exp` is Mathlib’s exponential circle map. -/
def puncturedLoopPath (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z : Circle, γ z ≠ b) : C(↑unitInterval, {z : ℂ // z ≠ 0}) :=
  { toFun := fun t => ⟨γ (Circle.exp (2 * Real.pi * (t : ℝ))) - b,
      by exact fun h => hb _ (sub_eq_zero.mp h)⟩
    continuous_toFun := by fun_prop }

/-- The winding integer about an omitted value.

Source: Lyubich §3.3 p.107, normalized so the positive unit circle has winding1.

The auxiliary path `c(t)=γ(exp(2πit))−b` takes values in nonzero complex numbers
because `hb` holds on the entire circle. `Complex.exp_log` supplies its initial
lift `e=log(c(0))`. The exponential covering and `liftPath` provide a continuous
lift `L`. The endpoint equality `c(1)=c(0)` follows from `exp(2πi)=1`, so
`exp(L(1))=exp(L(0))`. The exact exponential-fibre theorem supplies an integer
`n` with `L(1)=L(0)+n(2πi)`, and the data below select it. Since `2πi≠0`, this
integer is unique. Every proof used to construct the data is an actual Mathlib
proof, and no theorem deferred to Stage3 is used by this definition.
-/
def loopWinding (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z : Circle, γ z ≠ b) : ℤ := by
  let c := puncturedLoopPath γ b hb
  let e : ℂ := Complex.log (c 0)
  have he : c 0 = (⟨Complex.exp e, Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) := by
    apply Subtype.ext
    dsimp [e]
    exact (Complex.exp_log (c 0).property).symm
  let L := Complex.isCoveringMap_exp.liftPath c e he
  have hl := Complex.isCoveringMap_exp.liftPath_lifts c e he
  have hperiod : c 1 = c 0 := by
    apply Subtype.ext
    dsimp [c, puncturedLoopPath]
    congr 2
    apply Subtype.ext
    simp [Circle.coe_exp, Complex.exp_two_pi_mul_I]
  have hexp : Complex.exp (L 1) = Complex.exp (L 0) := by
    have h1 := congrArg Subtype.val (congrFun hl (1 : unitInterval))
    have h0 := congrArg Subtype.val (congrFun hl (0 : unitInterval))
    exact h1.trans ((congrArg Subtype.val hperiod).trans h0.symm)
  exact Classical.choose (Complex.exp_eq_exp_iff_exists_int.mp hexp)

end
end HolomorphicAnosov
