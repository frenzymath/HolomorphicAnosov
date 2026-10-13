import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic

/-!
# The disk Möbius transformation used in Conway's extremal argument

Source: Conway, *Functions of One Complex Variable*, VII Lemma 4.3, pp.161–162.
-/

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- The rational disk transformation with parameter `w` preserves the disk, is injective
there, vanishes at `w`, and has its explicit complex derivative.

Source: Conway VII Lemma 4.3, pp.161–162, the transformation preceding (4.6).
For points in the disk, the denominator is nonzero because its subtracted product has
norm less than one. The identity
`|1-conj(w)z|²-|z-w|²=(1-|w|²)(1-|z|²)>0` proves disk preservation.
Cross multiplication proves injectivity since `1-|w|²` is nonzero. Substitution gives
the value at `w`, and the quotient rule gives the stated derivative. -/
theorem conway_disk_mobius (w : ℂ) (hw : ‖w‖ < 1) :
    let T : ℂ → ℂ := fun z ↦ (z - w) / (1 - conj w * z)
    DifferentiableOn ℂ T (Metric.ball (0 : ℂ) 1) ∧
      InjOn T (Metric.ball (0 : ℂ) 1) ∧
      MapsTo T (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) ∧
      T w = 0 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        HasDerivAt T ((1 - conj w * w) / (1 - conj w * z) ^ 2) z := by
  intro T
  have hd : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 - conj w * z ≠ 0 := by
    intro z hz heq
    have hz' := mem_ball_zero_iff.mp hz
    have hnorm : ‖conj w * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg w, norm_nonneg z]
    have : conj w * z = 1 := (sub_eq_zero.mp heq).symm
    simp [this] at hnorm
  have hw0 : 1 - conj w * w ≠ 0 := hd w (mem_ball_zero_iff.mpr hw)
  have hder : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt T ((1 - conj w * w) / (1 - conj w * z) ^ 2) z := by
    intro z hz
    convert ((hasDerivAt_id z).sub_const w).div
      ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj w)))
      (hd z hz) using 1 <;> (dsimp [T]; congr 1 <;> ring)
  refine ⟨fun z hz ↦ (hder z hz).differentiableAt.differentiableWithinAt,
    ?_, ?_, ?_, hder⟩
  · intro z hz v hv heq
    have heq' : (z - w) * (1 - conj w * v) =
        (v - w) * (1 - conj w * z) := (div_eq_div_iff (hd z hz) (hd v hv)).mp heq
    have hfactor : (z - v) * (1 - conj w * w) = 0 := by
      linear_combination heq'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hw0)
  · intro z hz
    rw [mem_ball_zero_iff]
    change ‖(z - w) / (1 - conj w * z)‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hd z hz))]
    have hz' := mem_ball_zero_iff.mp hz
    have hwSq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg w]
    have hzSq : Complex.normSq z < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg z]
    have hid : Complex.normSq (1 - conj w * z) - Complex.normSq (z - w) =
        (1 - Complex.normSq w) * (1 - Complex.normSq z) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hpos := mul_pos (sub_pos.mpr hwSq) (sub_pos.mpr hzSq)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hid
    nlinarith [norm_nonneg (1 - conj w * z), norm_nonneg (z - w)]
  · simp [T]

end HolomorphicAnosov
