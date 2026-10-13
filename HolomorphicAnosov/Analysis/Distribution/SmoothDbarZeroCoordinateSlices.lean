import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic

open MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Set
open scoped ContDiff Topology _root_.Topology

/-- The scalar Cauchy--Riemann step in Demailly I §3.E, p.29: vanishing
coordinate antiholomorphic derivatives makes every coordinate slice
complex differentiable on its actual open domain. -/
theorem smooth_dbar_zero_coordinate_slices {n : ℕ}
    (V : Opens (Fin n → ℂ)) (g : (Fin n → ℂ) → ℂ)
    (hg : ContDiffOn ℝ ∞ g (V : Set _))
    (hbar : ∀ j x, x ∈ V → Analysis.antiholomorphicPartial g j x = 0) :
    ∀ (z : Fin n → ℂ) (j : Fin n),
      DifferentiableOn ℂ (fun t : ℂ ↦ g (Function.update z j t))
        ((fun t : ℂ ↦ Function.update z j t) ⁻¹' (V : Set _)) := by
  intro z j t ht
  let w : Fin n → ℂ := Function.update z j t
  have hgR : DifferentiableAt ℝ g w :=
    (hg.differentiableOn (by simp) w ht).differentiableAt (V.isOpen.mem_nhds ht)
  have huR : DifferentiableAt ℝ (Function.update z j) t :=
    (hasFDerivAt_update z t).differentiableAt
  have hderiv :
      fderiv ℝ (fun s : ℂ ↦ g (Function.update z j s)) t =
        (fderiv ℝ g w).comp (fderiv ℝ (Function.update z j) t) := by
    simpa only [Function.comp_def, w] using
      (fderiv_comp (g := g) (f := Function.update z j) (x := t) hgR huR)
  have hslice (v : ℂ) :
      fderiv ℝ (fun s : ℂ ↦ g (Function.update z j s)) t v =
        fderiv ℝ g w (Pi.single j v) := by
    rw [hderiv, ContinuousLinearMap.comp_apply, fderiv_update]
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  have hz := hbar j w ht
  change ((fderiv ℝ g w) (Pi.single j 1) +
    Complex.I * (fderiv ℝ g w) (Pi.single j Complex.I)) / 2 = 0 at hz
  have hsum : (fderiv ℝ g w) (Pi.single j 1) +
      Complex.I * (fderiv ℝ g w) (Pi.single j Complex.I) = 0 := by
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · norm_num at h
  have hA : (fderiv ℝ g w) (Pi.single j 1) =
      -(Complex.I * (fderiv ℝ g w) (Pi.single j Complex.I)) := by
    linear_combination hsum
  have hCR : (fderiv ℝ g w) (Pi.single j Complex.I) =
      Complex.I * (fderiv ℝ g w) (Pi.single j 1) := by
    calc
      _ = -((Complex.I * Complex.I) * (fderiv ℝ g w) (Pi.single j Complex.I)) := by
        rw [Complex.I_mul_I]
        ring
      _ = Complex.I * (-(Complex.I * (fderiv ℝ g w) (Pi.single j Complex.I))) := by
        ring
      _ = _ := by rw [hA]
  have hcomplex : DifferentiableAt ℂ (fun s : ℂ ↦ g (Function.update z j s)) t := by
    apply (differentiableAt_complex_iff_differentiableAt_real).mpr
    constructor
    · exact hgR.comp t huR
    · simpa only [hslice, smul_eq_mul] using hCR
  exact hcomplex.differentiableWithinAt


end HolomorphicAnosov
