import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- A map with derivative close to one injective linear map has segment
speeds controlled by its endpoint chord, with factor tending to one as the
derivative error tends to zero. Source: Petersen, Riemannian Geometry,
third edition, pp.149–150, the coordinate polygonal length comparison.
The convex mean-value inequality bounds the chord error by δ times the
parameter chord. The lower bound for A converts this to δC times the
linear chord. The same operator error bounds each segment velocity by
(1+δC) times the linear chord. Multiplying the two inequalities gives the
claim, including a zero-dimensional parameter space. -/
theorem derivative_segment_chord_bound
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set V} (hs : Convex ℝ s) (f : V → E) (D : V → V →L[ℝ] E)
    (A : V →L[ℝ] E) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hsmall : δ * C < 1)
    (hanti : ∀ v : V, ‖v‖ ≤ C * ‖A v‖)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (D z) s z)
    (hclose : ∀ z ∈ s, ‖D z - A‖ ≤ δ)
    {u v z : V} (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    (1 - δ * C) * ‖D z (u - v)‖ ≤ (1 + δ * C) * ‖f u - f v‖ := by
  have hrem : ‖f u - f v - A (u - v)‖ ≤ δ * ‖u - v‖ :=
    hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf hclose hv hu
  have hlinear : (1 - δ * C) * ‖A (u - v)‖ ≤ ‖f u - f v‖ := by
    have ht : ‖A (u - v)‖ ≤ ‖f u - f v‖ + ‖f u - f v - A (u - v)‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le (f u - f v) (f u - f v - A (u - v))
    have he := hrem.trans (mul_le_mul_of_nonneg_left (hanti (u - v)) hδ)
    nlinarith
  have hspeed : ‖D z (u - v)‖ ≤ (1 + δ * C) * ‖A (u - v)‖ := by
    have he : ‖(D z - A) (u - v)‖ ≤ δ * C * ‖A (u - v)‖ := by
      calc
        _ ≤ ‖D z - A‖ * ‖u - v‖ := (D z - A).le_opNorm _
        _ ≤ δ * ‖u - v‖ := mul_le_mul_of_nonneg_right (hclose z hz) (norm_nonneg _)
        _ ≤ δ * (C * ‖A (u - v)‖) := mul_le_mul_of_nonneg_left (hanti (u - v)) hδ
        _ = _ := (mul_assoc _ _ _).symm
    have ht : ‖D z (u - v)‖ ≤ ‖A (u - v)‖ + ‖(D z - A) (u - v)‖ := by
      simpa only [sub_apply, add_sub_cancel] using
        norm_add_le (A (u - v)) ((D z - A) (u - v))
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hspeed (by linarith : 0 ≤ 1 - δ * C)
  have hq := mul_le_mul_of_nonneg_left hlinear (by positivity : 0 ≤ 1 + δ * C)
  nlinarith

/-- The chord-speed comparison is uniform in a continuous external parameter
when the spatial derivative is jointly continuous at the marked center.
Choose an inverse bound C for the marked injective derivative and request
operator error ε/C. Product neighborhoods of derivative continuity provide
one parameter neighborhood and one inner spatial ball. The preceding convex
estimate then applies to every segment in that ball. Source: the finite-C1
plaque-family argument in HPS (1977), pp.61–63, together with the preceding
coordinate chord estimate. -/
theorem parametric_injective_derivative_segment_chord_bound
    {P V E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : P → V → E) (D : P × V → V →L[ℝ] E) (p₀ : P)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε1 : ε < 1)
    (hf : ∀ p v, v ∈ Metric.ball (0 : V) R → HasFDerivAt (f p) (D (p, v)) v)
    (hD : ContinuousAt D (p₀, 0)) (hinj : Function.Injective (D (p₀, 0))) :
    ∃ N : Set P, IsOpen N ∧ p₀ ∈ N ∧ ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ p ∈ N, ∀ u ∈ Metric.ball (0 : V) r, ∀ v ∈ Metric.ball (0 : V) r,
        ∀ z ∈ Metric.ball (0 : V) r,
          (1 - ε) * ‖D (p, z) (u - v)‖ ≤ (1 + ε) * ‖f p u - f p v‖ := by
  let A := D (p₀, 0)
  obtain ⟨C, hC, hanti⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hCr : 0 < (C : ℝ) := hC
  let δ := ε / (C : ℝ)
  have hδ : 0 < δ := div_pos hε hCr
  have hδC : δ * (C : ℝ) = ε := div_mul_cancel₀ _ (ne_of_gt hCr)
  have hnear : {q : P × V | ‖D q - A‖ < δ} ∈ 𝓝 (p₀, 0) :=
    hD.eventually (eventually_norm_sub_lt A hδ)
  obtain ⟨N₀, hN₀, W₀, hW₀, hprod⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨N, hNN₀, hN, hpN⟩ := mem_nhds_iff.mp hN₀
  obtain ⟨a, ha, haW⟩ := Metric.mem_nhds_iff.mp hW₀
  let r := min a R / 2
  have hr : 0 < r := half_pos (lt_min ha hR)
  have hra : r < a := (half_lt_self (lt_min ha hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min ha hR)).trans_le (min_le_right _ _)
  refine ⟨N, hN, hpN, r, hr, hrR, ?_⟩
  intro p hp u hu v hv z hz
  have hh := derivative_segment_chord_bound (convex_ball (0 : V) r) (f p)
    (fun v ↦ D (p, v)) A hCr.le hδ.le (hδC ▸ hε1)
    (fun v ↦ by
      have ht := hanti.le_mul_dist v 0
      change dist v 0 ≤ (C : ℝ) * dist (A v) (A 0) at ht
      simpa only [dist_zero_right, map_zero] using ht)
    (fun v hv ↦ (hf p v ((Metric.ball_subset_ball hrR.le) hv)).hasFDerivWithinAt)
    (fun v hv ↦ (hprod ⟨hNN₀ hp, haW ((Metric.ball_subset_ball hra.le) hv)⟩).le)
    hu hv hz
  simpa only [hδC] using hh

end HolomorphicAnosov.Analysis

