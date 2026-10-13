import HolomorphicAnosov.Analysis.Complex.LoopHomotopyOfNormSubLt
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingCongrSub
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.Compact

namespace HolomorphicAnosov
open Set Filter _root_.Topology

/-- Uniformly converging loops have eventually the same winding about converging
omitted points. Source: McMullen, Advanced Complex Analysis, Corollary 1.23 p.12,
straight-line homotopy stability, as used in the limit argument of
Lehto--Virtanen I.Theorem 5.2 p.29.

Proof: the distance of the compact limiting loop from its omitted point has a
strictly positive minimum δ. Eventually both the uniform loop error and the
point error are smaller than δ/2. Translating each approximating loop by
b−b_n makes it omit the fixed point b and changes it from the limiting loop by
less than δ. Straight interpolation therefore avoids b. Homotopy invariance
and translation of the puncture give the claimed equality. -/
theorem qc_limit_loop_winding (γ : ComplexLoop) (γn : ℕ → ComplexLoop)
    (b : ℂ) (bn : ℕ → ℂ) (hb : ∀ z, γ z ≠ b)
    (hbn : ∀ n z, γn n z ≠ bn n)
    (hγ : TendstoUniformly (fun n z ↦ γn n z) γ atTop)
    (hpoint : Tendsto bn atTop (𝓝 b)) :
    ∀ᶠ n in atTop, loopWinding (γn n) (bn n) (hbn n) = loopWinding γ b hb := by
  obtain ⟨z₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (s := (univ : Set Circle)) Set.univ_nonempty
    ((γ.continuous.sub continuous_const).norm.continuousOn)
  let δ := ‖γ z₀ - b‖
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hb z₀))
  have hloop := (Metric.tendstoUniformly_iff.mp hγ) (δ / 2) (half_pos hδ)
  have hpt := (Metric.tendsto_nhds.mp hpoint) (δ / 2) (half_pos hδ)
  filter_upwards [hloop, hpt] with n hn hnpt
  let σ : ComplexLoop := ⟨fun z ↦ γn n z + (b - bn n), by fun_prop⟩
  have hσ : ∀ z, σ z ≠ b := by
    intro z he
    apply hbn n z
    change γn n z + (b - bn n) = b at he
    linear_combination he
  have hsmall : ∀ z, ‖σ z - γ z‖ < ‖γ z - b‖ := by
    intro z
    have hsum : ‖σ z - γ z‖ ≤ ‖γn n z - γ z‖ + ‖b - bn n‖ := by
      have he : σ z - γ z = (γn n z - γ z) + (b - bn n) := by
        dsimp [σ]
        ring
      rw [he]
      exact norm_add_le _ _
    have hfirst : ‖γn n z - γ z‖ < δ / 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hn z
    have hsecond : ‖b - bn n‖ < δ / 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hnpt
    have hbound : δ ≤ ‖γ z - b‖ := hmin (mem_univ z)
    exact (hsum.trans_lt (by linarith)).trans_le hbound
  have hhom := loopHomotopyAvoids_of_norm_sub_lt γ σ b hsmall
  have hw := loopWinding_homotopy γ σ b hb hσ hhom
  have htrans := loopWinding_congr_sub (γn n) σ (bn n) b (hbn n) hσ
    (fun z ↦ by dsimp [σ]; ring)
  exact htrans.trans hw.symm


namespace Ghys

/-- The imaginary part of a logarithmic winding lift is the normalized angle lift.
Source: Lyubich §3.3, p.107. Extend its interval domain by the continuous nearest-point
projection onto `[0,1]`; the logarithmic endpoint increment `2πi` becomes `2π` on
imaginary parts. Dividing the exponential by its norm removes the real part. -/
theorem winding_one_angle_lift (γ : ComplexLoop) (b : ℂ)
    (hb : ∀ z, γ z ≠ b) (hw : loopWinding γ b hb = 1) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp ((θ t : ℂ) * Complex.I) =
          (γ (Circle.exp (2 * Real.pi * t)) - b) /
            (‖γ (Circle.exp (2 * Real.pi * t)) - b‖ : ℂ)) ∧
      θ 1 = θ 0 + 2 * Real.pi := by
  obtain ⟨L, hL, hend⟩ := loopWinding_lift γ b hb
  let θ : ℝ → ℝ := fun t ↦ (L (projIcc 0 1 (by norm_num) t)).im
  refine ⟨θ, (Complex.continuous_im.comp (L.continuous.comp
    continuous_projIcc)).continuousOn, ?_, ?_⟩
  · intro t ht
    have hLt := hL (⟨t, ht⟩ : unitInterval)
    change Complex.exp (L ⟨t, ht⟩) = γ (Circle.exp (2 * Real.pi * t)) - b at hLt
    dsimp [θ]
    rw [projIcc_of_mem _ ht, ← hLt]
    rw [Complex.norm_exp]
    rw [show L ⟨t, ht⟩ = ((L ⟨t, ht⟩).re : ℂ) +
      ((L ⟨t, ht⟩).im : ℂ) * Complex.I by exact (Complex.re_add_im _).symm,
      Complex.exp_add, ← Complex.ofReal_exp]
    field_simp
    simp [Complex.mul_re, Complex.mul_im, mul_comm]
  · rw [hw] at hend
    have hi := congrArg Complex.im hend
    simpa [θ, projIcc_of_mem, Complex.mul_im] using hi

end Ghys

/-- An injective holomorphic map with nonzero derivative at the disk center
has a normalized boundary phase of increment `2π`. Its only preimage of the
center value is the center, of analytic order one; the disk argument principle
therefore gives winding one, and the logarithm lift gives the real phase. -/
lemma normalized_phase_of_holomorphic_disk {a : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r))
    (hi : InjOn f (Metric.closedBall a r)) (hd : deriv f a ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        Complex.exp ((θ t : ℂ) * Complex.I) = (f c - f a) / (‖f c - f a‖ : ℂ)) ∧
      θ 1 = θ 0 + 2 * Real.pi := by
  have ha : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  have havoid (z : ℂ) (hz : z ∈ Metric.sphere a r) : f z ≠ f a := by
    intro heq
    have hza := hi (Metric.sphere_subset_closedBall hz) ha heq
    have hz' := Metric.mem_sphere.mp hz
    rw [hza, dist_self] at hz'
    exact hr.ne' hz'.symm
  obtain ⟨s, hs, hord, hwind, _⟩ :=
    winding_holomorphic_zero_count.2.2.2.2 a (f a) r f hr hf havoid
  have hsingle : s = {a} := by
    ext z
    rw [Finset.mem_singleton, hs]
    constructor
    · intro hz
      exact hi (Metric.ball_subset_closedBall hz.1) ha hz.2
    · rintro rfl
      exact ⟨Metric.mem_ball_self hr, rfl⟩
  have horder : analyticOrderNatAt (fun z ↦ f z - f a) a = 1 := by
    rw [analyticOrderNatAt, (hf a ha).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd]
    rfl
  rw [hsingle, Finset.sum_singleton, horder] at hwind
  obtain ⟨θ, hθ, hphase, hθend⟩ := Ghys.winding_one_angle_lift
    (diskBoundaryLoop a r f hr hf.continuousOn) (f a) _ hwind
  refine ⟨θ, hθ, ?_, hθend⟩
  intro t ht
  have hp := hphase t ht
  change Complex.exp ((θ t : ℂ) * Complex.I) =
    (f (a + (r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)) - f a) /
      (‖f (a + (r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)) - f a‖ : ℂ) at hp
  simpa only [Circle.coe_exp] using hp

end HolomorphicAnosov


