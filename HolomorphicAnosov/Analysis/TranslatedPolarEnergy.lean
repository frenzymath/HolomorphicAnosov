import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section
open Set Filter MeasureTheory
open scoped Topology _root_.Topology ENNReal

namespace HolomorphicAnosov.Analysis

/-- Tao, 246C Notes 2, Theorem 20 proof, local text lines 255–265.
Translate the density, apply the complex polar lower-integral identity, use Tonelli
on the measurable product density, and pull the finite radial scalar outside. -/
theorem translated_polar_energy (F : ℂ → ℝ≥0∞) (hF : Measurable F) (ζ : ℂ) :
    (∫⁻ z, F z ∂volume) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r •
        (∫⁻ t in Ioo (-Real.pi) Real.pi,
          F (ζ + Complex.polarCoord.symm (r, t)) ∂volume) ∂volume := by
  let G : ℂ → ℝ≥0∞ := fun a ↦ F (ζ + a)
  have hG : Measurable G := hF.comp (measurable_const.add measurable_id)
  have hpolar : (∫⁻ z, F z ∂volume) =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p) := by
    calc
      (∫⁻ z, F z ∂volume) = ∫⁻ a, G a ∂volume := by
        rw [show G = fun a ↦ F (ζ + a) from rfl]
        exact (measurePreserving_add_left volume ζ).lintegral_comp hF |>.symm
      _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p) := by
        exact (Complex.lintegral_comp_polarCoord_symm G).symm
  rw [hpolar, Complex.polarCoord_target]
  have hpolarMeas : Measurable (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) :=
    by simp only [Complex.polarCoord_symm_apply]; fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p)) := by
    exact (ENNReal.measurable_ofReal.comp measurable_fst).smul
      (hG.comp hpolarMeas)
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro r
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)


end HolomorphicAnosov.Analysis
