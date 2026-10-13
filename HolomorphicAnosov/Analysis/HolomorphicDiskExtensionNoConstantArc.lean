import HolomorphicAnosov.Analysis.SchwarzZeroRealBoundary
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition

open Set Filter Metric Complex
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- An injective holomorphic map of the open disk has no continuous closed-disk
extension which is constant on a nonempty relatively open circle arc.

Source: Tao, 246C Notes 2, Theorem 20, final injectivity paragraph,
`literature/Tao-246C-Notes2-2018.txt:269`; McMullen, Complex Analysis 213a,
Theorem 1.36 and following circular-reflection remark and zero-boundary example,
`literature/McMullen-Complex-Analysis-213a-2010.txt:1131–1152`, printed pp.24–25.
The local coordinate calculations below expand the change of variables explicitly.
No smoothness or rectifiability of a target boundary is needed.

Proof: Choose a point ζ of the constant arc. The Cayley map
N(v)=ζ(i-v)/(i+v) takes zero to ζ, the upper half-plane into the disk, and the real
axis into its boundary. The squared-norm difference of its denominator and numerator
is 4 Im(v); the denominator is nonzero when Im(v)≥0. Cross multiplication proves
injectivity on that half-plane. Relative openness of the arc and continuity of N at
zero give r>0 such that the real diameter of B(0,r) maps into the constant arc.
Compose the given continuous extension with N and subtract its constant value.
The composition is continuous on the closed upper half-disk, holomorphic on its
open upper half by analytic division and composition, and zero on its real diameter.
The public flat-reflection zero theorem therefore makes it identically zero.
But ir/4 and ir/2 are distinct upper-half-disk points. Injectivity of N and of the
original disk map makes their composite values distinct, a contradiction.
Only this local pair of points is needed; there is no additional global continuation
premise and no appeal to a boundary extension theorem. -/
theorem no_constant_open_circle_arc (φ : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hinj : InjOn φ (ball (0 : ℂ) 1))
    (F : closedBall (0 : ℂ) 1 → ℂ) (hF : Continuous F)
    (hagree : ∀ z (hz : z ∈ ball (0 : ℂ) 1),
      F ⟨z, ball_subset_closedBall hz⟩ = φ z)
    (A : Set Circle) (hA : IsOpen A) (hAne : A.Nonempty) (p : ℂ)
    (hconstant : ∀ ζ ∈ A, F ⟨(ζ : ℂ), sphere_subset_closedBall ζ.property⟩ = p) :
    False := by
  obtain ⟨ζ, hζA⟩ := hAne
  let N : ℂ → ℂ := fun v ↦ (ζ : ℂ) * ((I - v) / (I + v))
  have hden (v : ℂ) (hv : 0 ≤ v.im) : I + v ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im, I_im, zero_im] at hi
    linarith
  have hnorm (v : ℂ) : ‖N v‖ = ‖I - v‖ / ‖I + v‖ := by
    simp only [N, norm_mul, Circle.norm_coe, one_mul, norm_div]
  have hsquares (v : ℂ) : ‖I + v‖ ^ 2 - ‖I - v‖ ^ 2 = 4 * v.im := by
    simp only [Complex.sq_norm, normSq_apply, add_re, add_im, sub_re, sub_im,
      I_re, I_im]
    ring
  have hle (v : ℂ) (hv : 0 ≤ v.im) : ‖N v‖ ≤ 1 := by
    rw [hnorm, div_le_one (norm_pos_iff.mpr (hden v hv))]
    have hs := hsquares v
    nlinarith [norm_nonneg (I - v), norm_nonneg (I + v)]
  have hlt (v : ℂ) (hv : 0 < v.im) : ‖N v‖ < 1 := by
    rw [hnorm, div_lt_one (norm_pos_iff.mpr (hden v hv.le))]
    have hs := hsquares v
    nlinarith [norm_nonneg (I - v), norm_nonneg (I + v)]
  have heq (v : ℂ) (hv : v.im = 0) : ‖N v‖ = 1 := by
    rw [hnorm, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hden v hv.ge))]
    have hs := hsquares v
    nlinarith [norm_nonneg (I - v), norm_nonneg (I + v)]
  have hNinj : InjOn N {v : ℂ | 0 ≤ v.im} := by
    intro v hv w hw he
    have hz : (ζ : ℂ) ≠ 0 := by
      intro hez
      have := Circle.norm_coe ζ
      simp [hez] at this
    have hc : (I - v) * (I + w) = (I - w) * (I + v) :=
      (div_eq_div_iff (hden v hv) (hden w hw)).mp (mul_left_cancel₀ hz he)
    have hzero : (2 * I) * (v - w) = 0 := by linear_combination -hc
    have htwo : (2 : ℂ) * I ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left htwo)
  obtain ⟨U, hU, hUA⟩ :=
    (show Topology.IsInducing (fun ζ : Circle ↦ (ζ : ℂ)) from
      Topology.IsInducing.subtypeVal).isOpen_iff.mp hA
  have hζU : (ζ : ℂ) ∈ U := by
    change ζ ∈ (fun ζ : Circle ↦ (ζ : ℂ)) ⁻¹' U
    rwa [hUA]
  have hNcont (v : ℂ) (hv : 0 ≤ v.im) : ContinuousAt N v := by
    exact continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.add continuousAt_id) (hden v hv))
  have hNzero : N 0 = ζ := by simp [N]
  have hnear : ∀ᶠ v in 𝓝 (0 : ℂ), N v ∈ U :=
    (hNcont 0 (by simp)).eventually (hU.mem_nhds (hNzero.symm ▸ hζU))
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hnear
  let f : {v : ℂ // v ∈ ball (0 : ℂ) r ∧ 0 ≤ v.im} → ℂ :=
    fun v ↦ F ⟨N v, by simpa only [mem_closedBall, dist_zero_right] using hle v v.property.2⟩ - p
  have hfcont : Continuous f := by
    refine (hF.comp (Continuous.subtype_mk ?_ _)).sub continuous_const
    rw [continuous_iff_continuousAt]
    intro v
    exact (hNcont v v.property.2).comp continuous_subtype_val.continuousAt
  have hNholo (v : ℂ) (hv : 0 ≤ v.im) : AnalyticAt ℂ N v := by
    exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.add analyticAt_id) (hden v hv))
  have hfhol : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {v : ℂ | v ∈ ball (0 : ℂ) r ∧ 0 < v.im} := by
    have hg : DifferentiableOn ℂ (fun v ↦ φ (N v) - p)
        {v : ℂ | v ∈ ball (0 : ℂ) r ∧ 0 < v.im} := by
      intro v hv
      have hNv : N v ∈ ball (0 : ℂ) 1 := by
        simpa only [mem_ball, dist_zero_right] using hlt v hv.2
      exact ((((hhol.analyticOnNhd isOpen_ball) (N v) hNv).comp
        (hNholo v hv.2.le)).sub analyticAt_const).differentiableAt.differentiableWithinAt
    apply hg.congr
    intro v hv
    have hNv : N v ∈ ball (0 : ℂ) 1 := by
      simpa only [mem_ball, dist_zero_right] using hlt v hv.2
    rw [Subtype.val_injective.extend_apply _ _ ⟨v, hv.1, hv.2.le⟩]
    exact congrArg (fun z : ℂ ↦ z - p) (hagree (N v) hNv)
  have hfzero (v : {v : ℂ // v ∈ ball (0 : ℂ) r ∧ 0 ≤ v.im})
      (hv : (v : ℂ).im = 0) : f v = 0 := by
    let η : Circle := ⟨N v, by change dist (N v) 0 = 1; simpa only [dist_zero_right] using heq v hv⟩
    have hη : η ∈ A := by
      rw [← hUA]
      exact hrU v.property.1
    exact sub_eq_zero.mpr (hconstant η hη)
  let u : {v : ℂ // v ∈ ball (0 : ℂ) r ∧ 0 ≤ v.im} :=
    ⟨(r / 4 : ℝ) * I, by
      constructor
      · simp only [mem_ball, dist_zero_right, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity : 0 < r / 4)]
        linarith
      · simp; positivity⟩
  let v : {v : ℂ // v ∈ ball (0 : ℂ) r ∧ 0 ≤ v.im} :=
    ⟨(r / 2 : ℝ) * I, by
      constructor
      · simp only [mem_ball, dist_zero_right, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity : 0 < r / 2)]
        linarith
      · simp; positivity⟩
  have huim : 0 < (u : ℂ).im := by dsimp [u]; simp; positivity
  have hvim : 0 < (v : ℂ).im := by dsimp [v]; simp; positivity
  have huN : N u ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hlt u huim
  have hvN : N v ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hlt v hvim
  have hune : f u ≠ f v := by
    intro he
    have heF : F ⟨N u, by simpa only [mem_closedBall, dist_zero_right] using hle u huim.le⟩ =
        F ⟨N v, by simpa only [mem_closedBall, dist_zero_right] using hle v hvim.le⟩ :=
      sub_left_inj.mp he
    have heφ : φ (N u) = φ (N v) := (hagree (N u) huN).symm.trans
      (heF.trans (hagree (N v) hvN))
    have huv := hNinj huim.le hvim.le (hinj huN hvN heφ)
    have him := congrArg Complex.im huv
    simp only [u, v, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul, add_zero] at him
    linarith
  have hflat := eq_zero_of_schwarz_real_zero_boundary 0 r hr f hfcont hfhol hfzero
  exact hune ((hflat u).trans (hflat v).symm)

end HolomorphicAnosov
