import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

noncomputable section
open scoped _root_.Topology
namespace HolomorphicAnosov.Ghys

/-! This file gives a quantitative boundary separation estimate for a straight comparison homotopy
in a real normed space. (Ghys, Prop. 2.2, pp.589–590) -/

/-- If `g a` is separated from `g` on a boundary set by `m` and perturbation errors there and at `a`
are less than `m / 4`, the straight homotopy between `g` and `F` preserves boundary separation
from the corresponding image of `a`. (Ghys, Prop. 2.2, pp.589–590) -/
theorem comparison_boundary_avoidance_g18
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g F : E → E} {a : E} {B : Set E} {m : ℝ}
    (hm : 0 < m)
    (hsep : ∀ z ∈ B, m ≤ ‖g z - g a‖)
    (hF : ∀ z ∈ B, ‖F z - g z‖ < m / 4)
    (ha : ‖F a - g a‖ < m / 4) :
    ∀ z ∈ B, ∀ t : unitInterval,
      (1 - (t : ℝ)) • g z + (t : ℝ) • F z ≠
        (1 - (t : ℝ)) • g a + (t : ℝ) • F a := by
  intro z hz t heq
  have hbase : m ≤ ‖g z - g a‖ := hsep z hz
  have herr : ‖(F z - g z) - (F a - g a)‖ < m / 2 := by
    calc
      ‖(F z - g z) - (F a - g a)‖ ≤
          ‖F z - g z‖ + ‖F a - g a‖ := by
            calc
              _ = ‖(F z - g z) + (-(F a - g a))‖ := by rw [sub_eq_add_neg]
              _ ≤ ‖F z - g z‖ + ‖-(F a - g a)‖ := norm_add_le _ _
              _ = ‖F z - g z‖ + ‖F a - g a‖ := by rw [norm_neg]
      _ < m / 2 := by
        have hzsmall := hF z hz
        have hasmall := ha
        linarith
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg t.property.1] using t.property.2
  have hrewrite :
      g z - g a + (t : ℝ) • ((F z - g z) - (F a - g a)) = 0 := by
    have hzero :
        ((1 - (t : ℝ)) • g z + (t : ℝ) • F z) -
          ((1 - (t : ℝ)) • g a + (t : ℝ) • F a) = 0 :=
      sub_eq_zero.mpr heq
    calc
      g z - g a + (t : ℝ) • ((F z - g z) - (F a - g a)) =
          ((1 - (t : ℝ)) • g z + (t : ℝ) • F z) -
            ((1 - (t : ℝ)) • g a + (t : ℝ) • F a) := by
              rw [smul_sub, smul_sub]
              module
      _ = 0 := hzero
  have hcancel : ‖g z - g a‖ ≤
      ‖(t : ℝ) • ((F z - g z) - (F a - g a))‖ := by
    exact le_of_eq ((congrArg norm (eq_neg_of_add_eq_zero_left hrewrite)).trans (norm_neg _))
  have hsmall : ‖(t : ℝ) • ((F z - g z) - (F a - g a))‖ < m / 2 := by
    rw [norm_smul]
    have hmul :=
      mul_le_mul_of_nonneg_right ht
        (norm_nonneg ((F z - g z) - (F a - g a)))
    rw [one_mul] at hmul
    exact hmul.trans_lt herr
  linarith

end HolomorphicAnosov.Ghys

