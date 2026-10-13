import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import HolomorphicAnosov.Analysis.MarkedRectangleG3CanonicalPrevertices
import HolomorphicAnosov.Analysis.MarkedRectangleG3CrossRatioParameter

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- Positive real Möbius normalization of four strictly ordered marks.

Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp.184–186,
Theorem 13.16 and Lemma 13.20: three-point real fractional-linear
normalization followed by cross-ratio preservation. The determinant and
interval denominator conditions record the positive orientation and exclude
a pole on the marked interval. -/
theorem exists_real_positive_mobius_canonical_prevertices
    (x : Fin 4 → ℝ) (hx : StrictMono x) :
    ∃ k a b c d : ℝ,
      0 < k ∧ k < 1 ∧ 0 < a * d - b * c ∧
      (∀ t ∈ Set.Icc (x 0) (x 3), c * t + d ≠ 0) ∧
      (∀ i : Fin 4,
        (a * x i + b) / (c * x i + d) = canonicalPrevertex k i) := by
  have h01 : x 0 < x 1 := hx (by decide)
  have h12 : x 1 < x 2 := hx (by decide)
  have h23 : x 2 < x 3 := hx (by decide)
  have h02 : x 0 < x 2 := lt_trans h01 h12
  have h13 : x 1 < x 3 := lt_trans h12 h23
  have h03 : x 0 < x 3 := lt_trans h02 h23
  let p : ℝ := x 1 - x 0
  let q : ℝ := x 3 - x 1
  let r : ℝ := x 2 - x 0
  let s : ℝ := x 3 - x 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hs : 0 < s := by dsimp [s]; linarith
  have hcross : p * s < r * q := by
    dsimp [p, q, r, s]
    nlinarith [mul_pos (sub_pos.mpr h01) (sub_pos.mpr h23),
      mul_pos (sub_pos.mpr h12) (sub_pos.mpr h13)]
  obtain ⟨U, V, k, hU, hV, hUV, hUsq, hVsq, hkdef, hk0, hk1⟩ :=
    canonical_cross_ratio_parameter hp hq hr hs hcross
  let α : ℝ := q * U
  let β : ℝ := p * V
  have hα : 0 < α := mul_pos hq hU
  have hβ : 0 < β := mul_pos hp hV
  have hsum : 0 < V + U := by positivity
  have hdiff : 0 < V - U := sub_pos.mpr hUV
  have hk_mul : k * (V + U) = V - U := by
    rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hsum)]
  let a : ℝ := (V + U) * (α + β)
  let b : ℝ := -(V + U) * (α * x 0 + β * x 3)
  let c : ℝ := (V - U) * (α - β)
  let d : ℝ := (V - U) * (β * x 3 - α * x 0)
  have hnum (t : ℝ) : a * t + b =
      (V + U) * (α * (t - x 0) - β * (x 3 - t)) := by
    dsimp [a, b]; ring
  have hden (t : ℝ) : c * t + d =
      (V - U) * (α * (t - x 0) + β * (x 3 - t)) := by
    dsimp [c, d]; ring
  have hden_pos (t : ℝ) (ht : t ∈ Set.Icc (x 0) (x 3)) : 0 < c * t + d := by
    rw [hden]
    apply mul_pos hdiff
    have ht0 : 0 ≤ t - x 0 := sub_nonneg.mpr ht.1
    have ht3 : 0 ≤ x 3 - t := sub_nonneg.mpr ht.2
    by_cases hte : t = x 0
    · subst t
      simpa using mul_pos hβ (sub_pos.mpr h03)
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hα (lt_of_le_of_ne ht0 (by
          intro hz
          apply hte
          linarith)))
        (mul_nonneg (le_of_lt hβ) ht3)
  have hdet : 0 < a * d - b * c := by
    have hid : a * d - b * c =
        2 * (V + U) * (V - U) * α * β * (x 3 - x 0) := by
      dsimp [a, b, c, d]; ring
    rw [hid]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hsum) hdiff) hα) hβ)
      (sub_pos.mpr h03)
  refine ⟨k, a, b, c, d, hk0, hk1, hdet, ?_, ?_⟩
  · intro t ht
    exact ne_of_gt (hden_pos t ht)
  · intro i
    have hi : x i ∈ Set.Icc (x 0) (x 3) :=
      ⟨hx.monotone (Fin.zero_le i), hx.monotone (Fin.le_last i)⟩
    have hDi : c * x i + d ≠ 0 := ne_of_gt (hden_pos (x i) hi)
    fin_cases i
    · simp only [canonicalPrevertex]
      apply (div_eq_div_iff hDi (ne_of_gt hk0)).2
      rw [hnum, hden]
      simp
      have hkmul : V - U = k * (V + U) := hk_mul.symm
      rw [hkmul]
      ring
    · simp only [canonicalPrevertex]
      apply (div_eq_iff hDi).2
      rw [hnum, hden]
      simp
      dsimp [p, q, α, β]
      ring
    · simp only [canonicalPrevertex]
      apply (div_eq_iff hDi).2
      rw [hnum, hden]
      simp
      have hid : (V + U) * (α * r - β * s) -
          1 * ((V - U) * (α * r + β * s)) =
          2 * (U ^ 2 * (r * q) - V ^ 2 * (p * s)) := by
        dsimp [α, β]; ring
      rw [hUsq, hVsq] at hid
      nlinarith only [hid]
    · simp only [canonicalPrevertex]
      apply (div_eq_div_iff hDi (ne_of_gt hk0)).2
      rw [hnum, hden]
      simp
      have hkmul : V - U = k * (V + U) := hk_mul.symm
      rw [hkmul]
      ring

end HolomorphicAnosov.Analysis.MarkedRectangle

