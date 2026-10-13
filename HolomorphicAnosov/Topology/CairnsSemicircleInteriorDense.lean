import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.UnitInterval

namespace HolomorphicAnosov
open Set

/-- The strict side of a nondegenerate closed semicircle is dense in it.

Source: Cairns (1951), §4(A), printed pp.863–864. Fix a strictly interior unit
vector `w`. For a unit vector `v` on the closed side, normalize `v + t w` for
`0 ≤ t ≤ 1`. This vector is nonzero: at zero it is `v`, and for positive `t`
its signed transverse coordinate is positive. Normalization is continuous,
fixes `v` at zero, and has strictly positive signed coordinate for positive
`t`. Thus every closed-side direction is a limit of strict-side directions. -/
theorem cairns_semicircle_interior_dense (c : ℝ) (d : ℂ)
    (w : Circle) (hw : 0 < c * (star d * (w : ℂ)).im) :
    Dense {v : {v : Circle | 0 ≤ c * (star d * (v : ℂ)).im} |
      0 < c * (star d * ((v : Circle) : ℂ)).im} := by
  intro v
  let x : unitInterval → ℂ := fun t ↦ ((v : Circle) : ℂ) + (t : ℝ) • (w : ℂ)
  have hxside (t : unitInterval) : c * (star d * x t).im =
      c * (star d * ((v : Circle) : ℂ)).im +
        (t : ℝ) * (c * (star d * (w : ℂ)).im) := by
    simp [x, mul_add, Complex.mul_im, Complex.mul_re, Complex.real_smul]
    ring
  have hxne (t : unitInterval) : x t ≠ 0 := by
    by_cases ht : (t : ℝ) = 0
    · dsimp [x]
      rw [ht]
      norm_num
    · have hp : 0 < c * (star d * x t).im := by
        rw [hxside]
        exact add_pos_of_nonneg_of_pos v.property (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hw)
      intro h
      simp [h] at hp
  have hxnorm (t : unitInterval) : 0 < ‖x t‖ := norm_pos_iff.mpr (hxne t)
  let f : unitInterval → Circle := fun t ↦ ⟨x t / (‖x t‖ : ℂ), by
    have hn : ‖x t / (‖x t‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hxnorm t)]
      exact div_self (hxnorm t).ne'
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hn⟩
  have hfside (t : unitInterval) : c * (star d * (f t : ℂ)).im =
      (c * (star d * x t).im) / ‖x t‖ := by
    change c * (star d * (x t / (‖x t‖ : ℂ))).im = _
    rw [← mul_div_assoc, Complex.div_ofReal_im, mul_div_assoc]
  have hfmem (t : unitInterval) : 0 ≤ c * (star d * (f t : ℂ)).im := by
    rw [hfside, hxside]
    exact div_nonneg (add_nonneg v.property (mul_nonneg t.property.1 hw.le)) (hxnorm t).le
  let g : unitInterval → {v : Circle | 0 ≤ c * (star d * (v : ℂ)).im} :=
    fun t ↦ ⟨f t, hfmem t⟩
  have hxcont : Continuous x := by fun_prop
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    exact hxcont.div (Complex.continuous_ofReal.comp hxcont.norm)
      (fun t ↦ Complex.ofReal_ne_zero.mpr (hxnorm t).ne')
  have hgcont : Continuous g := hfcont.subtype_mk hfmem
  have hgzero : g 0 = v := by
    apply Subtype.ext
    apply Subtype.ext
    simp [g, f, x, Circle.norm_coe]
  rw [← hgzero]
  apply hgcont.continuousWithinAt.mem_closure (s := Ioo (0 : unitInterval) 1)
  · rw [closure_Ioo (show (0 : unitInterval) ≠ 1 by norm_num)]
    exact ⟨le_rfl, zero_le_one⟩
  · intro t ht
    change 0 < c * (star d * (f t : ℂ)).im
    rw [hfside, hxside]
    apply div_pos _ (hxnorm t)
    exact add_pos_of_nonneg_of_pos v.property (mul_pos ht.1 hw)

end HolomorphicAnosov
