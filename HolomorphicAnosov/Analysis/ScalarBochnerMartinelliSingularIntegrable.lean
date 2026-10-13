import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace HolomorphicAnosov.Analysis

/-- Compactly supported measurable functions with the scalar Bochner–Martinelli
singularity bound are integrable for the original product complex volume.

Source: Demailly, *Complex Analytic and Differential Geometry* (2012), I §3.D,
pp.25–27, local integrability of the radial kernel and its compact-support use.
The comparison with the coordinate maximum norm is an agent-written estimate;
the Euclidean radius in the hypothesis is retained exactly.

Proof. Translate the centre to zero. The maximum coordinate norm is bounded by
the square root of the sum of coordinate norm squares. Hence, off zero, the
given bound is at most C times the maximum norm to power −(2n−1). Product
complex volume is additive Haar measure on a real space of dimension 2n.
Mathlib's radial integrability theorem applies since 2n−1<2n: in polar
coordinates the singular radial exponent after the Jacobian is zero. The
translated function is therefore locally integrable. Its topological support
is compact, so local integrability there and vanishing outside it imply global
integrability. Translation preserves volume. The excluded point has measure
zero because n≥1, and no condition on its assigned value is needed. -/
theorem scalar_bochnerMartinelli_singular_integrable
    {n : ℕ} (hn : 1 ≤ n) (f : (Fin n → ℂ) → ℂ)
    (hf : AEStronglyMeasurable f volume) (hs : HasCompactSupport f)
    (z : Fin n → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ζ, ζ ≠ z → ‖f ζ‖ ≤
      C / Real.sqrt (∑ j, ‖(ζ-z) j‖ ^ 2) ^ (2*n-1)) :
    Integrable f volume := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g := fun w : Fin n → ℂ ↦ f (z+w)
  have htrans := measurePreserving_add_left (volume : Measure (Fin n → ℂ)) z
  have hg : AEStronglyMeasurable g volume := hf.comp_measurePreserving htrans
  have hsg : HasCompactSupport g := hs.comp_homeomorph (Homeomorph.addLeft z)
  have hdim : Module.finrank ℝ (Fin n → ℂ) = 2*n := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  have hlocal : LocallyIntegrable g volume := by
    apply locallyIntegrable_of_norm_le_rpow (by rw [hdim]; omega)
      (α := ((2*n-1 : ℕ) : ℝ)) (C := C)
    · rw [hdim]
      exact_mod_cast (show 2*n-1 < 2*n by omega)
    · filter_upwards [volume.ae_ne (0 : Fin n → ℂ)] with w hw
      have hsum : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
      have hr : ‖w‖ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
        apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
        intro j
        have hj := Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖w k‖) (Finset.mem_univ j)
        have heq := Real.sq_sqrt hsum
        nlinarith [Real.sqrt_nonneg (∑ k, ‖w k‖ ^ 2), norm_nonneg (w j)]
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hbound : ‖g w‖ ≤ C / Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ (2*n-1) := by
        simpa only [g, add_sub_cancel_left] using hb (z+w) (by simpa using hw)
      calc
        _ ≤ C / Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ (2*n-1) := hbound
        _ ≤ C / ‖w‖ ^ (2*n-1) := div_le_div_of_nonneg_left hC
          (pow_pos hwpos _) (pow_le_pow_left₀ (norm_nonneg _) hr _)
        _ = C * ‖w‖ ^ (-((2*n-1 : ℕ) : ℝ)) := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv]
    · exact hg
  have hgintegrable : Integrable g volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport g)).mp
      (hlocal.integrableOn_isCompact hsg)
  exact (htrans.integrable_comp hf).mp hgintegrable

end HolomorphicAnosov.Analysis
