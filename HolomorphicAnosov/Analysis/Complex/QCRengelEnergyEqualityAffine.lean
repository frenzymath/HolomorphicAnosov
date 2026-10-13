import HolomorphicAnosov.Analysis.Complex.QCRengelSliceEquality
import HolomorphicAnosov.Analysis.Complex.QCRengelConstantDerivativeNorm
import Mathlib.Analysis.Complex.Convex

/-! # The equality case of Rengel's integrated energy estimate

Source: Lehto–Virtanen (1973), I §4.3 p.23, necessity of equality in Rengel's
inequality. We first obtain slice equality almost everywhere, and only then
extend the derivative-norm equality by continuity; no boundary derivatives occur.
-/
namespace HolomorphicAnosov
open Set MeasureTheory

/-- Equality in Rengel's total energy bound makes the holomorphic rectangle map affine.

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973), I §4.3 p.23.
Write L(x) for the integral of the derivative norm on the vertical unit interval
and E(x) for its squared integral. The probability-space variance inequality gives
E(x) ≥ L(x)² ≥ s² almost everywhere. Equality of the total integrals therefore
gives E(x)=s² almost everywhere. Since L(x)≥s≥0, the two inequalities force
L(x)=s and E(x)=L(x)². The slice equality theorem gives norm s on each good
vertical interval. For each height, continuity in the horizontal variable extends
this equality from almost every horizontal coordinate to all of them. The
constant-derivative-norm theorem on the connected open rectangle makes the map
affine, with slope norm exactly s. The zero-slope case is included.
-/
theorem qc_rengel_energy_equality_affine {w s : ℝ} {f : ℂ → ℂ}
    (hw : 0 < w) (hs : 0 ≤ s)
    (hf : DifferentiableOn ℂ f (Complex.reProdIm (Ioo 0 w) (Ioo 0 1)))
    (hLp : ∀ᵐ x ∂volume.restrict (Ioo 0 w),
      MemLp (fun y : ℝ ↦ ‖deriv f (⟨x,y⟩ : ℂ)‖) 2 (volume.restrict (Ioo 0 1)))
    (hLength : ∀ᵐ x ∂volume.restrict (Ioo 0 w),
      s ≤ ∫ y in Ioo (0 : ℝ) 1, ‖deriv f (⟨x,y⟩ : ℂ)‖)
    (hEnergy : IntegrableOn
      (fun x : ℝ ↦ ∫ y in Ioo (0 : ℝ) 1, ‖deriv f (⟨x,y⟩ : ℂ)‖ ^ 2) (Ioo 0 w))
    (hEqual : (∫ x in Ioo (0 : ℝ) w, ∫ y in Ioo (0 : ℝ) 1,
      ‖deriv f (⟨x,y⟩ : ℂ)‖ ^ 2) = w * s ^ 2) :
    ∃ c d : ℂ, ‖c‖ = s ∧ ∀ z ∈ Complex.reProdIm (Ioo 0 w) (Ioo 0 1), f z = c * z + d := by
  let E (x : ℝ) := ∫ y in Ioo (0 : ℝ) 1, ‖deriv f (⟨x,y⟩ : ℂ)‖ ^ 2
  let L (x : ℝ) := ∫ y in Ioo (0 : ℝ) 1, ‖deriv f (⟨x,y⟩ : ℂ)‖
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hSchwarz : ∀ᵐ x ∂volume.restrict (Ioo 0 w), L x ^ 2 ≤ E x := by
    filter_upwards [hLp] with x hx
    have hv := ProbabilityTheory.variance_nonneg
      (fun y : ℝ ↦ ‖deriv f (⟨x,y⟩ : ℂ)‖) (volume.restrict (Ioo 0 1))
    rw [ProbabilityTheory.variance_eq_sub hx] at hv
    exact sub_nonneg.mp hv
  have hLower : (fun _ : ℝ ↦ s ^ 2) ≤ᵐ[volume.restrict (Ioo 0 w)] E := by
    filter_upwards [hSchwarz, hLength] with x hx hxs
    exact (pow_le_pow_left₀ hs hxs 2).trans hx
  have hSliceEnergy : (fun _ : ℝ ↦ s ^ 2) =ᵐ[volume.restrict (Ioo 0 w)] E := by
    apply (integral_eq_iff_of_ae_le (integrableOn_const (by simp [Real.volume_Ioo])) hEnergy hLower).mp
    simpa [E, integral_const, Real.volume_Ioo, hw.le, mul_comm] using hEqual.symm
  have hc : ContinuousOn (deriv f) (Complex.reProdIm (Ioo 0 w) (Ioo 0 1)) :=
    (hf.deriv (isOpen_Ioo.reProdIm isOpen_Ioo)).continuousOn
  have hNormSlices : ∀ᵐ x ∂volume.restrict (Ioo 0 w),
      ∀ y ∈ Ioo (0 : ℝ) 1, ‖deriv f (⟨x,y⟩ : ℂ)‖ = s := by
    filter_upwards [hLp, hLength, hSchwarz, hSliceEnergy,
      ae_restrict_mem measurableSet_Ioo] with x hx hxs hxe he hxw
    have hmean : L x = s := by
      have hsq : L x ^ 2 ≤ s ^ 2 := he ▸ hxe
      nlinarith
    have hvcont : ContinuousOn (fun y : ℝ ↦ ‖deriv f (⟨x,y⟩ : ℂ)‖) (Ioo 0 1) :=
      hc.norm.comp
        ((Complex.equivRealProdCLM.symm.continuous.comp
          (continuous_const.prodMk continuous_id)).continuousOn) (fun y hy ↦ ⟨hxw, hy⟩)
    have heq : E x = L x ^ 2 := by rw [← he, hmean]
    intro y hy
    exact (qc_rengel_slice_equality hvcont hx heq y hy).trans hmean
  have hNorm (z : ℂ) (hz : z ∈ Complex.reProdIm (Ioo 0 w) (Ioo 0 1)) : ‖deriv f z‖ = s := by
    have hy : z.im ∈ Ioo (0 : ℝ) 1 := hz.2
    have hx : z.re ∈ Ioo (0 : ℝ) w := hz.1
    have hhorizontal : ContinuousOn (fun x : ℝ ↦ ‖deriv f (⟨x,z.im⟩ : ℂ)‖) (Ioo 0 w) :=
      hc.norm.comp
        ((Complex.equivRealProdCLM.symm.continuous.comp
          (continuous_id.prodMk continuous_const)).continuousOn) (fun x h ↦ ⟨h, hy⟩)
    have he := Measure.eqOn_open_of_ae_eq
      (hNormSlices.mono (fun x h ↦ h z.im hy)) isOpen_Ioo hhorizontal continuousOn_const
    exact he hx
  have hconv : Convex ℝ (Complex.reProdIm (Ioo 0 w) (Ioo 0 1)) := by
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹' (Ioo 0 w ×ˢ Ioo 0 1))
    exact ((convex_Ioo (0 : ℝ) w).prod (convex_Ioo (0 : ℝ) 1)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hconn : IsConnected (Complex.reProdIm (Ioo 0 w) (Ioo 0 1)) := hconv.isConnected
    ⟨⟨w / 2, 1 / 2⟩, ⟨by change 0 < w / 2 ∧ w / 2 < w; constructor <;> linarith, by norm_num⟩⟩
  exact qc_rengel_constant_derivative_norm (isOpen_Ioo.reProdIm isOpen_Ioo) hconn hf hNorm

end HolomorphicAnosov
