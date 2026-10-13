import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Real coordinate transport for the scalar Bochner–Martinelli formula

The product complex Lebesgue measure is carried to real Euclidean volume by splitting real and
imaginary coordinates. Source: Demailly, *Complex Analytic and Differential Geometry*, I §3.D,
pp.25–26, with positive Lebesgue normalization; the measure identities are Mathlib's product
measure and complex Lebesgue equivalences.
-/

noncomputable section
open MeasureTheory

namespace HolomorphicAnosov.Analysis

/-- Real coordinates ordered as all real parts followed by all imaginary parts. This reordering
preserves the positive Lebesgue measure used in Demailly I §3.D, pp.25–26. -/
def bochnerMartinelliCoordinateEquiv (n : ℕ) :
    (Fin n → ℂ) ≃ᵐ EuclideanSpace ℝ (Fin (2 * n)) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin n ↦ Complex.measurableEquivRealProd)).trans <|
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).trans <|
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ ℝ)).symm.trans <|
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n) ↦ ℝ)
          (finSumFinEquiv.trans (finCongr (by omega)))).trans <|
            MeasurableEquiv.toLp 2 (Fin (2 * n) → ℝ)

/-- The real coordinate identification preserves positive Lebesgue volume.

Source: Demailly I §3.D, pp.25–26, coordinate Lebesgue normalization. Apply the standard planar
complex-to-real equivalence in each coordinate. The product-of-pairs equivalence groups the real
and imaginary tuples, the sum-index equivalence concatenates them, finite reindexing identifies
that tuple with `Fin (2*n)`, and the PiLp equivalence identifies coordinate volume with Euclidean
volume. Every constituent map preserves volume, so their composition does as well. The assertion
also covers `n=0`, where both spaces are singletons with unit Dirac volume.
-/
theorem bochnerMartinelliCoordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (bochnerMartinelliCoordinateEquiv n) := by
  unfold bochnerMartinelliCoordinateEquiv
  exact (volume_preserving_pi (fun _ : Fin n ↦
    Complex.volume_preserving_equiv_real_prod)).trans <|
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).trans <|
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin n ↦ ℝ)).trans <|
        (volume_measurePreserving_piCongrLeft (fun _ : Fin (2 * n) ↦ ℝ)
          (finSumFinEquiv.trans (finCongr (by omega)))).trans <|
            PiLp.volume_preserving_toLp (Fin (2 * n))


/-- The real Euclidean norm of the coordinate image equals Demailly's explicit radius.

Source: Demailly I §3.D pp.25–26. Expand the Euclidean norm as the square root of a coordinate
square sum. Reindex the sum along the finite coordinate equivalence, split its two blocks, and
combine each real/imaginary pair using the complex norm-square identity. The empty-dimensional
case is included, since both sums are empty and both norms are zero.
-/
theorem bochnerMartinelliCoordinateEquiv_norm {n : ℕ} (w : Fin n → ℂ) :
    ‖bochnerMartinelliCoordinateEquiv n w‖ = Real.sqrt (∑ j, ‖w j‖ ^ 2) := by

  rw [EuclideanSpace.norm_eq]
  congr 1
  let e : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.sum_comp]
  change (∑ i : Fin n ⊕ Fin n,
    ‖(MeasurableEquiv.piCongrLeft (fun _ : Fin (2*n) ↦ ℝ) e)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ ℝ)).symm
        ((fun j ↦ (w j).re), (fun j ↦ (w j).im))) (e i)‖ ^ 2) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp [MeasurableEquiv.sumPiEquivProdPi, pow_two]
  simp_rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply, Finset.sum_add_distrib]


end HolomorphicAnosov.Analysis
