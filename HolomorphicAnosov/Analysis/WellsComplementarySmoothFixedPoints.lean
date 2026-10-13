import HolomorphicAnosov.Paper.HPS.ComplementaryPicardRange
import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse

/-!
# Smooth complementary fixed points on the whole original base ball

Source: Wells (1976), pp.290–291, the formula w = G⁻¹ ∘ I and the
corrected Picard iteration in the final Remark. This binds the range and
smooth inverse theorems before either graph projection is taken.
DAG node: `analysis.wells_complementary_smooth_fixed_points_g18`.
-/

namespace HolomorphicAnosov
open Set
open scoped ContDiff

/-- The complementary maximum estimate gives a fixed point above every base
point in the original ball. The smooth inverse of Id−Γ evaluated on the base
injection selects these points smoothly. Their norms do not exceed the base
norm, and the complementary difference estimate makes the selection unit
Lipschitz. This is Wells pp.290–291 before projection to a graph coordinate.

Proof: Picard iteration on the closed ball of radius ‖I p‖ supplies the unique
solution in the open ball, so I p belongs to the inverse domain. Compose the
smooth inverse with I and identify it with the Picard solution by uniqueness.
Subtract two fixed equations and use the maximum estimate. If their distance
exceeded the base distance it would be at most Q times itself, impossible for
Q<1. At the zero base the norm estimate forces the solution to vanish. -/
theorem wells_complementary_smooth_fixed_points
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (I : P →L[ℝ] X) (hI : ∀ p, ‖I p‖ = ‖p‖)
    (Γ : X → X) (s Q : ℝ) (hs : 0 < s) (hQ : 0 ≤ Q) (hQ1 : Q < 1)
    (r : ℕ∞) (hr : 1 ≤ r)
    (hΓ : ContDiffOn ℝ (r : ℕ∞ω) Γ (Metric.ball 0 s))
    (hLip : ∀ x ∈ Metric.ball (0 : X) s, ∀ y ∈ Metric.ball (0 : X) s,
      ‖Γ x - Γ y‖ ≤ Q * ‖x - y‖)
    (hmax : ∀ p ∈ Metric.ball (0 : P) s, ∀ w, ‖w‖ ≤ ‖p‖ →
      ‖I p + Γ w‖ ≤ max ‖p‖ (Q * ‖w‖))
    (hmaxdiff : ∀ p q : P, ∀ w ∈ Metric.ball (0 : X) s,
      ∀ z ∈ Metric.ball (0 : X) s,
      ‖(I p + Γ w) - (I q + Γ z)‖ ≤ max ‖p - q‖ (Q * ‖w - z‖)) :
    ∃ f : P → X,
      ContDiffOn ℝ (r : ℕ∞ω) f (Metric.ball 0 s) ∧ f 0 = 0 ∧
      (∀ p ∈ Metric.ball (0 : P) s, ‖f p‖ ≤ ‖p‖ ∧ f p - Γ (f p) = I p) ∧
      (∀ p ∈ Metric.ball (0 : P) s, ∀ q ∈ Metric.ball (0 : P) s,
        ‖f p - f q‖ ≤ ‖p - q‖) ∧
      (∀ p ∈ Metric.ball (0 : P) s, ∀ z ∈ Metric.ball (0 : X) s,
        z - Γ z = I p → z = f p) := by
  obtain ⟨hopen, hbij, J, hJmap, hJleft, hJright, hJsmooth, _⟩ :=
    Analysis.wellsLipschitzPerturbationSmoothInverse Metric.isOpen_ball hr hΓ hQ hQ1 hLip
  have hpic (p : P) (hp : p ∈ Metric.ball (0 : P) s) :
      ∃ w : X, ‖w‖ ≤ ‖p‖ ∧ w - Γ w = I p ∧
        ∀ z ∈ Metric.ball (0 : X) s, z - Γ z = I p → z = w := by
    have hb : ‖I p‖ < s := by simpa [hI] using hp
    simpa only [hI] using hps_complementary_picard_range Γ (I p) s Q hb hQ hQ1 hLip
      (by simpa only [hI] using hmax p hp)
  have hImem (p : P) (hp : p ∈ Metric.ball (0 : P) s) :
      I p ∈ (fun x ↦ x - Γ x) '' Metric.ball (0 : X) s := by
    obtain ⟨w, hw, heq, _⟩ := hpic p hp
    exact ⟨w, Metric.mem_ball.mpr (by simpa using hw.trans_lt (by simpa using hp)), heq⟩
  have hnorm (p : P) (hp : p ∈ Metric.ball (0 : P) s) : ‖J (I p)‖ ≤ ‖p‖ := by
    obtain ⟨w, hw, heq, _⟩ := hpic p hp
    have hwmem : w ∈ Metric.ball (0 : X) s :=
      Metric.mem_ball.mpr (by simpa using hw.trans_lt (by simpa using hp))
    have hwJ : J (I p) = w := by simpa only [heq] using hJleft w hwmem
    simpa only [hwJ] using hw
  refine ⟨fun p ↦ J (I p), hJsmooth.comp I.contDiff.contDiffOn hImem, ?_, ?_, ?_, ?_⟩
  · apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hnorm 0 (by simpa using hs)) (norm_nonneg _)
  · intro p hp
    exact ⟨hnorm p hp, hJright _ (hImem p hp)⟩
  · intro p hp q hq
    have hep : I p + Γ (J (I p)) = J (I p) :=
      (sub_eq_iff_eq_add.mp (hJright _ (hImem p hp))).symm
    have heq : I q + Γ (J (I q)) = J (I q) :=
      (sub_eq_iff_eq_add.mp (hJright _ (hImem q hq))).symm
    have hb := hmaxdiff p q (J (I p)) (hJmap (hImem p hp))
      (J (I q)) (hJmap (hImem q hq))
    rw [hep, heq] at hb
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hpos : 0 < ‖J (I p) - J (I q)‖ := (norm_nonneg _).trans_lt hlt
    exact (not_lt_of_ge hb) (max_lt hlt (mul_lt_of_lt_one_left hpos hQ1))
  · intro p hp z hz heq
    change z = J (I p)
    rw [← heq]
    exact (hJleft z hz).symm

end HolomorphicAnosov
