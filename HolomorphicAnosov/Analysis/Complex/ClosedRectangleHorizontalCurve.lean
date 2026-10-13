import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Order.ProjIcc

/-!
# Horizontal curves of a continuous closed-rectangle extension

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5 Theorem 11.10, printed p.342, the horizontal curves used in (11.3).
This module supplies the parameterized curve with its actual interior derivative.
-/

open Set

namespace HolomorphicAnosov.Analysis.Complex

/-- The restriction of a continuous closed-rectangle extension to an interior
horizontal segment has a continuous ambient parameterization whose interior
velocity is the original map's complex derivative.

Source: the parameterized horizontal curves in Farb–Margalit Version 5.0,
§11.5 Theorem 11.10, printed p.342. This is an explicit construction of the
curve and the chain-rule detail omitted in the source.

Proof: Clamp the real parameter to [0,a], include it at fixed imaginary height
y in the closed rectangle, and compose with the continuous extension E. This
produces a globally continuous curve agreeing with E on the entire closed
segment. At an interior parameter x the clamp is the identity on a neighborhood
of x and E agrees there with f. Complex differentiability gives derivative
f′(x+iy) for the translated complex function. Restricting its parameter to the
real axis preserves this complex-valued derivative. The locally equal curve
therefore has that same derivative. No endpoint derivative is required.
-/
theorem exists_closed_rectangle_horizontal_curve
    {a b y : ℝ} (ha : 0 ≤ a) (hy : y ∈ Ioo 0 b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Complex.reProdIm (Ioo 0 a) (Ioo 0 b)))
    (E : Complex.reProdIm (Icc 0 a) (Icc 0 b) → ℂ) (hE : Continuous E)
    (hmatch : ∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b),
      (z : ℂ) ∈ Complex.reProdIm (Ioo 0 a) (Ioo 0 b) → E z = f z) :
    ∃ g : ℝ → ℂ, Continuous g ∧
      (∀ (x : ℝ) (hx : x ∈ Icc 0 a),
        g x = E ⟨(x : ℂ) + (y : ℂ) * Complex.I, by
          simpa [Complex.mem_reProdIm] using And.intro hx ⟨hy.1.le, hy.2.le⟩⟩) ∧
      (∀ x ∈ Ioo 0 a,
        HasDerivAt g (deriv f ((x : ℂ) + (y : ℂ) * Complex.I)) x) := by
  let p : ℝ → Complex.reProdIm (Icc 0 a) (Icc 0 b) := fun x ↦
    ⟨((projIcc 0 a ha x : ℝ) : ℂ) + (y : ℂ) * Complex.I, by
      simpa [Complex.mem_reProdIm] using
        And.intro (projIcc 0 a ha x).property ⟨hy.1.le, hy.2.le⟩⟩
  have hp : Continuous p := by
    apply Continuous.subtype_mk
    exact (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_projIcc)).add continuous_const
  refine ⟨E ∘ p, hE.comp hp, ?_, ?_⟩
  · intro x hx
    simp only [Function.comp_apply, p, projIcc_of_mem ha hx]
  · intro x hx
    have hz : (x : ℂ) + (y : ℂ) * Complex.I ∈
        Complex.reProdIm (Ioo 0 a) (Ioo 0 b) := by
      simpa [Complex.mem_reProdIm] using And.intro hx hy
    have hd := (hf.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz)).hasDerivAt
    have hshift := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * Complex.I))
    simp only [mul_one] at hshift
    have hr := hshift.comp_ofReal
    apply hr.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    change E (p t) = f ((t : ℂ) + (y : ℂ) * Complex.I)
    have hpt : (p t : ℂ) = (t : ℂ) + (y : ℂ) * Complex.I := by
      simp only [p, projIcc_of_mem ha ⟨ht.1.le, ht.2.le⟩]
    rw [← hpt]
    apply hmatch
    rw [hpt]
    simpa [Complex.mem_reProdIm] using And.intro ht hy

end HolomorphicAnosov.Analysis.Complex

