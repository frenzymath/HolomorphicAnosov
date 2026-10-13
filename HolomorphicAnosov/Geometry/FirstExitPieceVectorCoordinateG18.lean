import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
open Set MeasureTheory Filter Topology _root_.Topology
open scoped ENNReal
noncomputable section
namespace HolomorphicAnosov

/-- A coordinate derivative lower bound for a closed C¹ path piece gives an `ENNReal` length lower
bound in terms of its coordinate displacement. (Hirsch–Pugh–Shub, proof of Thm (6.7), p.86; Lee,
§11, pp.275–279) -/
theorem first_exit_piece_vector_coordinate_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {c : ℝ → E} {a b m : ℝ} {speed : ℝ → ℝ}
    (hab : a < b) (hc : ContDiffOn ℝ 1 c (Icc a b)) (hm : 0 < m)
    (hbound : ∀ t ∈ Icc a b,
      m * ‖L (derivWithin c (Icc a b) t)‖ ≤ speed t) :
    ENNReal.ofReal (m * ‖L (c b - c a)‖) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (speed t) := by
  have hcont_comp : ContDiffOn ℝ 1 (L ∘ c) (Icc a b) :=
    L.contDiff.comp_contDiffOn hc
  have hchord : ‖(L ∘ c) b - (L ∘ c) a‖ₑ ≤
      ∫⁻ t in Icc a b, ‖derivWithin (L ∘ c) (Icc a b) t‖ₑ :=
    enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hcont_comp hab.le
  have hderiv : ∀ t ∈ Icc a b,
      derivWithin (L ∘ c) (Icc a b) t = L (derivWithin c (Icc a b) t) := by
    intro t ht
    exact (L.hasFDerivAt.comp_hasDerivWithinAt t
      ((hc.differentiableOn one_ne_zero t ht).hasDerivWithinAt)).derivWithin
      (uniqueDiffOn_Icc hab t ht)
  have hmono : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      ENNReal.ofReal (m * ‖L (derivWithin c (Icc a b) t)‖) ≤
        ENNReal.ofReal (speed t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ENNReal.ofReal_le_ofReal (hbound t ht)
  have hlin : (ENNReal.ofReal m) *
      (∫⁻ t in Icc a b, ‖derivWithin (L ∘ c) (Icc a b) t‖ₑ) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (speed t) := by
    calc
      (ENNReal.ofReal m) *
          (∫⁻ t in Icc a b, ‖derivWithin (L ∘ c) (Icc a b) t‖ₑ) =
          ∫⁻ t in Icc a b,
            ENNReal.ofReal m * ‖derivWithin (L ∘ c) (Icc a b) t‖ₑ := by
              rw [MeasureTheory.lintegral_const_mul' _ _ (by simp)]
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (speed t) := by
        apply lintegral_mono_ae
        filter_upwards [hmono, ae_restrict_mem measurableSet_Icc] with t ht htm
        rw [hderiv t htm]
        calc
          ENNReal.ofReal m * ‖L (derivWithin c (Icc a b) t)‖ₑ =
              ENNReal.ofReal (m * ‖L (derivWithin c (Icc a b) t)‖) := by
            rw [ENNReal.ofReal_mul hm.le]
            congr 1
            rw [enorm_eq_nnnorm]
            exact ENNReal.coe_nnreal_eq _
          _ ≤ ENNReal.ofReal (speed t) := ht
  calc
    ENNReal.ofReal (m * ‖L (c b - c a)‖) =
        (ENNReal.ofReal m) * ‖(L ∘ c) b - (L ∘ c) a‖ₑ := by
      rw [Function.comp_apply, Function.comp_apply, map_sub,
        ENNReal.ofReal_mul hm.le]
      congr 1
      rw [enorm_eq_nnnorm]
      symm
      exact ENNReal.coe_nnreal_eq _
    _ ≤ (ENNReal.ofReal m) *
        (∫⁻ t in Icc a b, ‖derivWithin (L ∘ c) (Icc a b) t‖ₑ) :=
      by simpa [mul_comm] using mul_le_mul_left hchord (ENNReal.ofReal m)
    _ ≤ _ := hlin

end HolomorphicAnosov

