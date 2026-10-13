import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set
open scoped Interval

/-- Extract finite, strictly increasing real Cayley prevertices from positive cyclic marks.

Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp.177, 184--186:
choose a point on the positive complementary arc as the Cayley pole; its real boundary
coordinate is strictly increasing on the resulting lifted interval. -/
theorem exists_cayley_real_prevertices_of_cyclic
    (ζ : Fin 4 → ℂ)
    (hcyclic : ∃ θ : Fin 4 → ℝ, StrictMono θ ∧ θ 3 < θ 0 + 2 * Real.pi ∧
      ∀ i, circleMap 0 1 (θ i) = ζ i) :
    ∃ θ : Fin 4 → ℝ, ∃ τ : ℝ, ∃ q : ℂ, ∃ x : Fin 4 → ℝ,
      StrictMono θ ∧ θ 3 < τ ∧ τ < θ 0 + 2 * Real.pi ∧
      q = circleMap 0 1 τ ∧ ‖q‖ = 1 ∧ q ≠ 0 ∧ StrictMono x ∧
      (∀ i : Fin 4, circleMap 0 1 (θ i) = ζ i ∧ q - ζ i ≠ 0 ∧
        Complex.I * (q + ζ i) / (q - ζ i) = (x i : ℂ)) := by
  rcases hcyclic with ⟨θ, hθ, hlast, hζ⟩
  let τ : ℝ := (θ 3 + (θ 0 + 2 * Real.pi)) / 2
  have hτ0 : θ 3 < τ := by dsimp [τ]; linarith
  have hτ1 : τ < θ 0 + 2 * Real.pi := by dsimp [τ]; linarith
  let q : ℂ := circleMap 0 1 τ
  have hqnorm : ‖q‖ = 1 := by
    dsimp [q]
    simp
  have hcircle_inj : (Ico τ (τ + 2 * Real.pi)).InjOn (circleMap 0 1) := by
    apply injOn_circleMap_of_abs_sub_le' (by norm_num)
    linarith [Real.pi_pos]
  have hq_ne (t : ℝ) (ht : t ∈ Ioo τ (τ + 2 * Real.pi)) :
      q ≠ circleMap 0 1 t := by
    intro he
    have hte : τ ∈ Ico τ (τ + 2 * Real.pi) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hte' : t ∈ Ico τ (τ + 2 * Real.pi) := ⟨le_of_lt ht.1, ht.2⟩
    have := hcircle_inj hte hte' (by simpa [q] using he)
    exact (ne_of_lt ht.1) this
  have hq_ne_z (i : Fin 4) : q ≠ ζ i := by
    intro he
    have hqi := hq_ne (θ i + 2 * Real.pi) (by
      have hi0 : θ 0 ≤ θ i := hθ.monotone (Fin.zero_le i)
      have hi3 : θ i ≤ θ 3 := hθ.monotone (Fin.le_last i)
      constructor <;> linarith [hτ0, hτ1, Real.pi_pos])
    apply hqi
    rw [periodic_circleMap 0 1 (θ i), hζ i]
    exact he
  have hq0 : q ≠ 0 := by
    intro h
    have := hqnorm
    rw [h] at this
    norm_num at this
  have cayley_real (z : ℂ) (hz : ‖z‖ = 1) (hne : q ≠ z) :
      Complex.I * (q + z) / (q - z) =
        ((Complex.I * (q + z) / (q - z)).re : ℂ) := by
    have hqi : q⁻¹ = (starRingEnd ℂ) q := by
      rw [Complex.inv_def]
      have hn : Complex.normSq q = 1 := by
        rw [Complex.normSq_eq_norm_sq, hqnorm]
        norm_num
      rw [hn]
      simp
    have hzi : z⁻¹ = (starRingEnd ℂ) z := by
      rw [Complex.inv_def]
      have hn : Complex.normSq z = 1 := by
        rw [Complex.normSq_eq_norm_sq, hz]
        norm_num
      rw [hn]
      simp
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hconj : (starRingEnd ℂ) (Complex.I * (q + z) / (q - z)) =
        Complex.I * (q + z) / (q - z) := by
      rw [map_div₀, map_mul, map_add, map_sub]
      rw [show (starRingEnd ℂ) Complex.I = -Complex.I by simp]
      rw [← hqi, ← hzi]
      have hden : (q⁻¹ - z⁻¹) ≠ 0 := by
        intro hh
        apply hne
        field_simp [hq0, hz0] at hh
        have hzq : z = q := sub_eq_zero.mp (by simpa using hh)
        exact hzq.symm
      field_simp [hne, hden, hq0, hz0]
      ring
    have him := congrArg Complex.im hconj
    simp only [Complex.conj_im] at him
    apply Complex.ext_iff.mpr
    constructor
    · rfl
    · have him0 : (Complex.I * (q + z) / (q - z)).im = 0 := by linarith
      simpa using him0
  let f : ℝ → ℝ := fun t ↦
    (Complex.I * (q + circleMap 0 1 t) /
      (q - circleMap 0 1 t)).re
  have hcircle_cont : Continuous (circleMap 0 1) := by
    have he : circleMap 0 1 = (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) := by
      funext t
      simp [circleMap_zero]
    rw [he]
    exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hf_cont : ContinuousOn f (Ioo τ (τ + 2 * Real.pi)) := by
    intro t ht
    have hden : q - circleMap 0 1 t ≠ 0 := sub_ne_zero.mpr (hq_ne t ht)
    apply ContinuousAt.continuousWithinAt
    exact Complex.continuous_re.continuousAt.comp
      ((continuousAt_const.mul (continuousAt_const.add
        hcircle_cont.continuousAt)).div
        (continuousAt_const.sub hcircle_cont.continuousAt) hden)
  have hf_inj : (Ioo τ (τ + 2 * Real.pi)).InjOn f := by
    intro u hu v hv huv
    have huq := hq_ne u hu
    have hvq := hq_ne v hv
    have hcu := cayley_real (circleMap 0 1 u) (by simp) huq
    have hcv := cayley_real (circleMap 0 1 v) (by simp) hvq
    have hcomp : Complex.I * (q + circleMap 0 1 u) /
          (q - circleMap 0 1 u) =
        Complex.I * (q + circleMap 0 1 v) /
          (q - circleMap 0 1 v) := by
      rw [hcu, hcv]
      exact congrArg (fun r : ℝ ↦ (r : ℂ)) huv
    have hz : circleMap 0 1 u = circleMap 0 1 v := by
      have hh := (div_eq_div_iff (sub_ne_zero.mpr huq) (sub_ne_zero.mpr hvq)).mp hcomp
      field_simp at hh
      have hqz : q * circleMap 0 1 u = q * circleMap 0 1 v := by
        linear_combination hh / 2
      exact mul_left_cancel₀ hq0 hqz
    have hinj := hcircle_inj
      ⟨le_of_lt hu.1, hu.2⟩ ⟨le_of_lt hv.1, hv.2⟩ hz
    exact hinj
  have hτmid : τ < τ + Real.pi / 2 := by linarith [Real.pi_pos]
  have hτhigh : τ + Real.pi / 2 < τ + 2 * Real.pi := by linarith [Real.pi_pos]
  have hτmid' : τ + 3 * Real.pi / 2 < τ + 2 * Real.pi := by linarith [Real.pi_pos]
  have hshift (t : ℝ) : circleMap 0 1 (t + Real.pi / 2) =
      circleMap 0 1 t * Complex.I := by
    rw [circleMap_zero, circleMap_zero]
    rw [show ((↑(t + Real.pi / 2) : ℂ) * Complex.I) =
      (↑t : ℂ) * Complex.I + (↑Real.pi / 2 : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]
    ring
  have hshift' (t : ℝ) : circleMap 0 1 (t + 3 * Real.pi / 2) =
      circleMap 0 1 t * (-Complex.I) := by
    rw [circleMap_zero, circleMap_zero]
    rw [show ((↑(t + 3 * Real.pi / 2) : ℂ) * Complex.I) =
      (↑t : ℂ) * Complex.I + (↑Real.pi : ℂ) * Complex.I +
        (↑Real.pi / 2 : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_pi_div_two_mul_I]
    ring
  have hmid : f (τ + Real.pi / 2) = -1 := by
    dsimp only [f]
    rw [hshift]
    change (Complex.I * (q + q * Complex.I) / (q - q * Complex.I)).re = -1
    have he : Complex.I * (q + q * Complex.I) / (q - q * Complex.I) = -1 := by
      apply (div_eq_iff (by
        rw [← mul_one_sub q Complex.I]
        exact mul_ne_zero hq0 (by norm_num [Complex.ext_iff]))).2
      linear_combination q * Complex.I_sq
    rw [he]
    simp
  have hhigh : f (τ + 3 * Real.pi / 2) = 1 := by
    dsimp only [f]
    rw [hshift']
    change (Complex.I * (q + q * (-Complex.I)) / (q - q * (-Complex.I))).re = 1
    have he : Complex.I * (q + q * (-Complex.I)) / (q - q * (-Complex.I)) = 1 := by
      apply (div_eq_iff (by
        rw [← mul_one_sub q (-Complex.I)]
        exact mul_ne_zero hq0 (by norm_num [Complex.ext_iff]))).2
      linear_combination -q * Complex.I_sq
    rw [he]
    simp
  have hmono_or_anti := ContinuousOn.strictMonoOn_of_injOn_Ioo
    (show τ < τ + 2 * Real.pi by linarith [Real.pi_pos]) hf_cont hf_inj
  have hf_mono : StrictMonoOn f (Ioo τ (τ + 2 * Real.pi)) := by
    rcases hmono_or_anti with hm | ha
    · exact hm
    · exfalso
      have hh := ha ⟨hτmid, hτhigh⟩ ⟨by linarith [Real.pi_pos], hτmid'⟩
        (by linarith [Real.pi_pos])
      linarith [hmid, hhigh]
  let x : Fin 4 → ℝ := fun i ↦ f (θ i + 2 * Real.pi)
  have hx : StrictMono x := by
    intro i j hij
    apply hf_mono
    · constructor
      · have hi0 : θ 0 ≤ θ i := hθ.monotone (Fin.zero_le i)
        linarith [hτ1]
      · have hi3 : θ i ≤ θ 3 := hθ.monotone (Fin.le_last i)
        linarith [hτ0, Real.pi_pos]
    · constructor
      · have hj0 : θ 0 ≤ θ j := hθ.monotone (Fin.zero_le j)
        linarith [hτ1]
      · have hj3 : θ j ≤ θ 3 := hθ.monotone (Fin.le_last j)
        linarith [hτ0, Real.pi_pos]
    · linarith [hθ hij]
  refine ⟨θ, τ, q, x, hθ, hτ0, hτ1, rfl, hqnorm, hq0, hx, ?_⟩
  intro i
  refine ⟨hζ i, sub_ne_zero.mpr (hq_ne_z i), ?_⟩
  dsimp only [x, f]
  rw [periodic_circleMap 0 1 (θ i), hζ i]
  apply cayley_real (ζ i) _ (hq_ne_z i)
  rw [← hζ i]
  simp

end HolomorphicAnosov.Analysis.MarkedRectangle

