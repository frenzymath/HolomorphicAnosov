import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # Winding-one loops and positive circles

The logarithm-lift interpolation follows Hatcher, Algebraic Topology,
Theorem 1.7, pp.29–30. The winding convention is Lyubich §3.3 p.107.
-/

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped _root_.Topology

/-- A continuous loop with winding one about `a` is freely homotopic in the
punctured plane to the counterclockwise circle of any positive radius.

Source: Hatcher, Algebraic Topology, Theorem 1.7, pp.29–30, its lifted linear
homotopy proof; Lyubich, Conformal Geometry, §3.3 p.107, winding convention.
Use the given logarithm lift L and interpolate it linearly with
`log r + 2πit`. Both lifts have endpoint increment `2πi`, so exponentiation
has equal endpoint values throughout the homotopy. Descend the interval
parameter to the circle through the endpoint quotient. The interpolated
exponential never vanishes, and the two endpoint maps are precisely the
original loop minus a and the radius-r circle. Translation by a finishes.
No injectivity or smoothness of the loop is needed. -/
theorem positive_loop_circle_homotopy (γ : ComplexLoop) (a : ℂ)
    (hpositive : WindsOncePositively (fun t ↦ γ (circlePhase t)) a)
    (r : ℝ) (hr : 0 < r) :
    LoopHomotopyAvoids γ
      ⟨fun z : Circle ↦ a + (r : ℂ) * (z : ℂ), by fun_prop⟩ a := by
  classical
  obtain ⟨_, _, L, hL, hinc⟩ := hpositive
  let K : C(↑unitInterval × ↑unitInterval, ℂ) :=
    ⟨fun ts ↦ a + Complex.exp
      ((1 - (ts.2 : ℝ) : ℂ) * L ts.1 + (ts.2 : ℝ) *
        ((Real.log r : ℂ) + (2 * Real.pi * (ts.1 : ℝ) : ℝ) * Complex.I)), by fun_prop⟩
  let f : ℝ → C(↑unitInterval, ℂ) :=
    fun t ↦ K.curry (projIcc 0 1 (by norm_num) t)
  have hK1 (t : unitInterval) : K (t, 1) = a + (r : ℂ) *
      Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I) := by
    simp [K, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  have hf : Continuous f := K.curry.continuous.comp continuous_projIcc
  have hend : f 0 = f 1 := by
    ext s
    change K (projIcc 0 1 _ 0, s) = K (projIcc 0 1 _ 1, s)
    simp only [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
      (by simp : (0 : ℝ) ∈ Icc 0 1),
      projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
        (by simp : (1 : ℝ) ∈ Icc 0 1)]
    have hLend : L 1 = L 0 + (2 * Real.pi : ℂ) * Complex.I := by
      linear_combination hinc
    dsimp [K]
    rw [hLend]
    push_cast
    have halg : (1 - (s : ℝ) : ℂ) * (L 0 + 2 * Real.pi * Complex.I) +
        (s : ℝ) * ((Real.log r : ℂ) + 2 * Real.pi * Complex.I) =
        (1 - (s : ℝ) : ℂ) * L 0 + (s : ℝ) * Real.log r +
          2 * Real.pi * Complex.I := by ring
    simp only [mul_zero, zero_mul, add_zero, mul_one] at *
    rw [halg]
    simp only [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let F : C(Circle, C(↑unitInterval, ℂ)) :=
    ⟨(AddCircle.liftIco 1 0 f) ∘ e.symm,
      (AddCircle.liftIco_zero_continuous hend hf.continuousOn).comp e.symm.continuous⟩
  let H : C(↑unitInterval × Circle, ℂ) := ⟨fun sz ↦ F sz.2 sz.1, by fun_prop⟩
  have hrep (z : Circle) :
      circlePhase ((AddCircle.equivIco (1 : ℝ) 0 (e.symm z) : ℝ)) = z := by
    calc
      _ = e ((AddCircle.equivIco (1 : ℝ) 0 (e.symm z) : ℝ) : AddCircle (1 : ℝ)) := by
        simp only [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
          div_one, circlePhase]
      _ = z := by rw [AddCircle.coe_equivIco]; exact e.apply_symm_apply z
  have hH (s : unitInterval) (z : Circle) :
      H (s, z) = K
        (⟨(AddCircle.equivIco (1 : ℝ) 0 (e.symm z) : ℝ),
          Ico_subset_Icc_self (by simpa using
            (AddCircle.equivIco (1 : ℝ) 0 (e.symm z)).property)⟩, s) := by
    change K (projIcc 0 1 _ (AddCircle.equivIco (1 : ℝ) 0 (e.symm z) : ℝ), s) = _
    rw [projIcc_of_mem _ (Ico_subset_Icc_self (by simpa using
      (AddCircle.equivIco (1 : ℝ) 0 (e.symm z)).property))]
  refine ⟨H, ?_, ?_, ?_⟩
  · intro z
    rw [hH]
    simp [K, hL, hrep]
  · intro z
    rw [hH, hK1]
    have hz := congrArg (fun z : Circle ↦ (z : ℂ)) (hrep z)
    simpa only [circlePhase, Circle.coe_exp, ContinuousMap.coe_mk] using
      congrArg (fun w : ℂ ↦ a + r * w) hz
  · intro s z heq
    rw [hH] at heq
    exact Complex.exp_ne_zero _ (add_left_cancel (heq.trans (add_zero a).symm))

end HolomorphicAnosov

