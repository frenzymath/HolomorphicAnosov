import HolomorphicAnosov.Topology.ConvexCapComponent
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter Metric
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

noncomputable section

/-- The source circular arc used by the Conway short-cap argument.

Source: Conway, *Functions of One Complex Variable II*, Chapter 14, Theorem 5.5,
p.50. -/
def markedRectangleG3CircularArc (ζ : ℂ) (r t : ℝ) : ℂ :=
  ζ * circleMap 1 r (Real.arccos (-r / 2) +
    (2 * Real.pi - 2 * Real.arccos (-r / 2)) * t)

/-- The circular crosscut cuts off precisely the convex cap in the unit disk.

Source: Conway, *Functions of One Complex Variable II*, Chapter 14, Theorem 5.5,
p.50, where the source circular arc is used to identify the two components of the
disk minus the crosscut. The proof is the elementary rotation calculation: after
multiplying by `ζ⁻¹`, the circle has equation `1 + r exp(i θ)`, its disk part is
the open arc with `cos θ < -r/2`, and the complementary side containing `0` is
connected by horizontal and radial segments. The convex-cap component theorem
then gives the displayed component exactly, including all `0 < r < 1`. -/
theorem markedRectangleG3CircularArc_component
    (ζ : ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hζ : ζ ∈ sphere (0 : ℂ) 1)
    {x : ℂ} (hx : x ∈ ball ζ r ∩ ball (0 : ℂ) 1) :
    connectedComponentIn (ball (0 : ℂ) 1 \ 
      range (markedRectangleG3CircularArc ζ r)) x =
      ball ζ r ∩ ball (0 : ℂ) 1 := by
  have hζnorm : ‖ζ‖ = 1 := by simpa using hζ
  have hcap_sphere_subset : sphere ζ r ∩ ball (0 : ℂ) 1 ⊆
      range (markedRectangleG3CircularArc ζ r) := by
    intro z hz
    have hzd : ‖z - ζ‖ = r := by
      simpa [dist_eq_norm] using hz.1
    let u : ℂ := (z - ζ) / (ζ * r)
    have hz0 : ζ ≠ 0 := by intro h; simp [h] at hζnorm
    have hden : ζ * (r : ℂ) ≠ 0 :=
      mul_ne_zero hz0 (Complex.ofReal_ne_zero.mpr hr.ne')
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [Complex.norm_div, Complex.norm_mul, hζnorm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
      rw [show ‖z - ζ‖ = r from hzd]
      field_simp
    have hu_repr : u = Complex.exp (u.arg * Complex.I) := by
      have h := Complex.norm_mul_exp_arg_mul_I u
      simpa [hu_norm] using h.symm
    have hzu : ζ * (r : ℂ) * u = z - ζ := by
      dsimp [u]
      calc
        ζ * (r : ℂ) * ((z - ζ) / (ζ * (r : ℂ))) =
            (z - ζ) / (ζ * (r : ℂ)) * (ζ * (r : ℂ)) := by ring
        _ = z - ζ := div_mul_cancel₀ _ hden
    have hnorm (θ : ℝ) : ‖ζ * circleMap 1 r θ‖ ^ 2 =
        1 + r ^ 2 + 2 * r * Real.cos θ := by
      rw [norm_mul, hζnorm, one_mul, Complex.sq_norm]
      simp only [circleMap, Complex.normSq_apply, Complex.add_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.exp_re, Complex.ofReal_im,
        Complex.exp_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, zero_add, mul_zero, add_zero,
        mul_one, Real.exp_zero, one_mul]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hz_repr : z = ζ * circleMap 1 r u.arg := by
      change z = ζ * (1 + (r : ℂ) * Complex.exp (↑u.arg * Complex.I))
      calc
        z = ζ + (z - ζ) := by ring
        _ = ζ + ζ * (r : ℂ) * u := by rw [hzu]
        _ = ζ + ζ * (r : ℂ) * Complex.exp (↑u.arg * Complex.I) := by
          exact congrArg (fun w : ℂ ↦ ζ + ζ * (r : ℂ) * w) hu_repr
        _ = ζ * (1 + (r : ℂ) * Complex.exp (↑u.arg * Complex.I)) := by ring
    have hz_norm_lt : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz.2
    have hcos : Real.cos u.arg < -r / 2 := by
      have hh := hnorm u.arg
      rw [← hz_repr] at hh
      have hzsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
      nlinarith [mul_pos hr (by norm_num : (0 : ℝ) < 2)]
    let a : ℝ := Real.arccos (-r / 2)
    have ha0 : 0 < a := by
      dsimp [a]
      exact Real.arccos_pos.mpr (by linarith [hr1])
    have haπ : a < Real.pi := by
      dsimp [a]
      exact Real.arccos_lt_pi.mpr (by linarith [hr1])
    have hca : Real.cos a = -r / 2 := by
      dsimp [a]
      exact Real.cos_arccos (by linarith) (by linarith)
    let d : ℝ := 2 * Real.pi - 2 * a
    have hd : 0 < d := by dsimp [d]; nlinarith
    have harglo : -Real.pi < u.arg := Complex.neg_pi_lt_arg u
    have harghi : u.arg ≤ Real.pi := Complex.arg_le_pi u
    have hangle_pos : 0 ≤ u.arg → a < u.arg := by
      intro hu
      by_contra hn
      have hua : u.arg ≤ a := le_of_not_gt hn
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi hu haπ.le hua
      linarith
    have hangle_neg : u.arg < 0 → u.arg < -a := by
      intro hu
      by_contra hn
      have hua : -u.arg ≤ a := by linarith
      have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [harglo]) haπ.le hua
      rw [Real.cos_neg] at hc
      linarith
    by_cases hu : 0 ≤ u.arg
    · let t : ℝ := (u.arg - a) / d
      have ht0 : 0 < t := by
        dsimp [t]
        exact div_pos (sub_pos.mpr (hangle_pos hu)) hd
      have ht1 : t < 1 := by
        dsimp [t]
        rw [div_lt_one hd]
        nlinarith [harghi, ha0]
      refine ⟨t, ?_⟩
      change ζ * circleMap 1 r (a + d * t) = z
      rw [show a + d * t = u.arg by
        dsimp [t]
        field_simp [hd.ne']
        ring]
      exact hz_repr.symm
    · have hu' : u.arg < 0 := lt_of_not_ge hu
      let θ : ℝ := u.arg + 2 * Real.pi
      let t : ℝ := (θ - a) / d
      have ht0 : 0 < t := by
        dsimp [t, θ]
        apply div_pos
        · nlinarith [hangle_neg hu', Real.pi_pos]
        · exact hd
      have ht1 : t < 1 := by
        dsimp [t, θ]
        rw [div_lt_one hd]
        nlinarith [hangle_neg hu', harglo]
      refine ⟨t, ?_⟩
      change ζ * circleMap 1 r (a + d * t) = z
      rw [show a + d * t = θ by
        dsimp [t]
        field_simp [hd.ne']
        ring]
      rw [show θ = u.arg + 2 * Real.pi by rfl]
      rw [periodic_circleMap (1 : ℂ) r u.arg]
      exact hz_repr.symm
  have harc_sphere : range (markedRectangleG3CircularArc ζ r) ⊆ sphere ζ r := by
    rintro z ⟨t, rfl⟩
    dsimp [markedRectangleG3CircularArc]
    rw [mem_sphere, dist_eq_norm]
    have he (u : ℝ) : ζ * circleMap 1 r u - ζ =
        ζ * (circleMap 1 r u - 1) := by ring
    rw [he, norm_mul, hζnorm, one_mul, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hr]
  have hset : ball (0 : ℂ) 1 \ range (markedRectangleG3CircularArc ζ r) =
      ball (0 : ℂ) 1 \ sphere ζ r := by
    ext z
    constructor
    · rintro ⟨hzU, hzg⟩
      refine ⟨hzU, ?_⟩
      intro hzS
      exact hzg (hcap_sphere_subset ⟨hzS, hzU⟩)
    · rintro ⟨hzU, hzS⟩
      refine ⟨hzU, ?_⟩
      intro hzg
      exact hzS (harc_sphere hzg)
  rw [hset]
  simpa only [inter_comm] using
    (HolomorphicAnosov.Topology.convex_cap_component
      (ball (0 : ℂ) 1) (convex_ball (0 : ℂ) 1) ζ r x ⟨hx.2, hx.1⟩)
