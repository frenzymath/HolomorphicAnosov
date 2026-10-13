import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Ring

/-!
# Integration by parts for regularized Bochner–Martinelli coefficients

Source: Demailly, *Complex Analytic and Differential Geometry* (2012),
I §2 (2.6), p.15, and I §3.D, pp.26–27. Only the smooth test function
has compact support; the positive regularization keeps the coefficients smooth.
-/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped ContDiff BigOperators
namespace HolomorphicAnosov.Analysis

/-- Demailly, *Complex Analytic and Differential Geometry* (2012), I §2 (2.6), p.15, and I §3.D, pp.26–27,
the integration-by-parts step for the epsilon-regularized scalar coefficients.

Proof. The denominator is strictly positive for epsilon>0, so each coefficient is
smooth everywhere. Bundle the given compactly supported smooth function as a test
on the whole coordinate space. Apply real directional integration by parts in the
real and imaginary directions of each coordinate. Every product is integrable:
the test and its derivatives have compact support, and the regularized coefficients
and their derivatives are continuous. Multiply the imaginary identity by i, add,
and divide by two. Finally sum over the finite coordinate set. The pairing is
complex-linear, without conjugation; hence the sign is negative. Only the test
function, not the regularized coefficient, is required to have compact support. -/
theorem scalar_bochnerMartinelli_regularized_integration_by_parts
    {n : ℕ} (ε : ℝ) (hε : 0 < ε) (u : (Fin n → ℂ) → ℂ)
    (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    let g := fun (j : Fin n) (w : Fin n → ℂ) ↦
      star (w j) / ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ n
    (∫ w, ∑ j : Fin n, g j w *
      ((fderiv ℝ u w (Pi.single j 1) +
        Complex.I * fderiv ℝ u w (Pi.single j Complex.I)) / 2)) =
    -(∫ w, ∑ j : Fin n,
      ((fderiv ℝ (g j) w (Pi.single j 1) +
        Complex.I * fderiv ℝ (g j) w (Pi.single j Complex.I)) / 2) * u w) := by
  classical
  dsimp only
  let g := fun (j : Fin n) (w : Fin n → ℂ) ↦
    star (w j) / ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ n
  change (∫ w, ∑ j : Fin n, g j w * _) = -(∫ w, ∑ j : Fin n, _ * u w)
  have hg (j : Fin n) : ContDiff ℝ ∞ (g j) := by
    dsimp [g]
    simp only [div_eq_mul_inv]
    apply ContDiff.mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ j))
    apply ContDiff.inv
    · apply ContDiff.pow
      have hsum : ContDiff ℝ ∞ (fun w : Fin n → ℂ ↦ ∑ k : Fin n, ‖w k‖ ^ 2) :=
        ContDiff.sum (fun k _ ↦ (contDiff_apply ℝ ℂ k).norm_sq ℂ)
      convert Complex.ofRealCLM.contDiff.comp (hsum.add (contDiff_const (c := ε ^ 2))) using 1
      ext w
      simp
    · intro w
      apply pow_ne_zero
      have hpos : 0 < (∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 :=
        add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (sq_pos_of_pos hε)
      exact_mod_cast hpos.ne'
  let φ : TestFunction (⊤ : Opens (Fin n → ℂ)) ℂ ⊤ := ⟨u, hu, hs, Set.subset_univ _⟩
  have hleft (j : Fin n) (v : Fin n → ℂ) :
      Integrable (fun w ↦ g j w * fderiv ℝ u w v) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hg j).continuous.mul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact (hs.fderiv_apply ℝ v).mul_left
  have hright (j : Fin n) (v : Fin n → ℂ) :
      Integrable (fun w ↦ fderiv ℝ (g j) w v * u w) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (((hg j).continuous_fderiv (by simp)).clm_apply continuous_const).mul hu.continuous
    · exact hs.mul_left
  have hdir (j : Fin n) (v : Fin n → ℂ) :
      (∫ w, g j w * fderiv ℝ u w v) = -(∫ w, fderiv ℝ (g j) w v * u w) :=
    HolomorphicAnosov.local_directional_integration_by_parts ⊤ (g j) (hg j).contDiffOn φ v
  have hl (j : Fin n) : Integrable (fun w ↦ g j w *
      ((fderiv ℝ u w (Pi.single j 1) +
        Complex.I * fderiv ℝ u w (Pi.single j Complex.I)) / 2)) := by
    convert ((hleft j (Pi.single j 1)).add
      ((hleft j (Pi.single j Complex.I)).const_mul Complex.I)).div_const 2 using 1
    ext w
    simp only [Pi.add_apply]
    ring
  have hr (j : Fin n) : Integrable (fun w ↦
      ((fderiv ℝ (g j) w (Pi.single j 1) +
        Complex.I * fderiv ℝ (g j) w (Pi.single j Complex.I)) / 2) * u w) := by
    convert ((hright j (Pi.single j 1)).add
      ((hright j (Pi.single j Complex.I)).const_mul Complex.I)).div_const 2 using 1
    ext w
    simp only [Pi.add_apply]
    ring
  rw [integral_finsetSum _ (fun j _ ↦ hl j), integral_finsetSum _ (fun j _ ↦ hr j),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have heql : (fun w ↦ g j w *
      ((fderiv ℝ u w (Pi.single j 1) +
        Complex.I * fderiv ℝ u w (Pi.single j Complex.I)) / 2)) =
      (fun w ↦ (g j w * fderiv ℝ u w (Pi.single j 1) +
        Complex.I * (g j w * fderiv ℝ u w (Pi.single j Complex.I))) / 2) := by
    ext w
    ring
  have heqr : (fun w ↦
      ((fderiv ℝ (g j) w (Pi.single j 1) +
        Complex.I * fderiv ℝ (g j) w (Pi.single j Complex.I)) / 2) * u w) =
      (fun w ↦ (fderiv ℝ (g j) w (Pi.single j 1) * u w +
        Complex.I * (fderiv ℝ (g j) w (Pi.single j Complex.I) * u w)) / 2) := by
    ext w
    ring
  rw [heql, heqr, integral_div, integral_div,
    integral_add (hleft j _) ((hleft j _).const_mul _),
    integral_add (hright j _) ((hright j _).const_mul _),
    integral_const_mul, integral_const_mul, hdir, hdir]
  ring

end HolomorphicAnosov.Analysis
