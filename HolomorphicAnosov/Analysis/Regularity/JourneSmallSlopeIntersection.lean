import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
This file establishes quantitative intersection and sampling estimates for transverse small-slope graphs (Journé, 1988).
-/ 

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Two transverse graphs with slope at most ε≤1/4 have a unique intersection near their anchors. (Journé, 1988) -/
theorem small_slope_graph_intersection
    {D E : Type*} [NormedAddCommGroup D] [CompleteSpace D]
    [NormedAddCommGroup E] [CompleteSpace E]
    (φ : D → E) (ψ : E → D) (a : D) (b : E)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1/4)
    (ha : ‖a‖ ≤ R/2) (hb : ‖b‖ ≤ R/2)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0)
    (hφ : ∀ u ∈ Metric.closedBall (0 : D) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖φ u - φ v‖ ≤ ε * ‖u-v‖)
    (hψ : ∀ u ∈ Metric.closedBall (0 : E) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖ψ u - ψ v‖ ≤ ε * ‖u-v‖) :
    ∃ z : D × E, ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R ∧
      z.1 = a + ψ z.2 ∧ z.2 = b + φ z.1 ∧
      ‖z - (a,b)‖ ≤ ε * R ∧
      ∀ w : D × E, ‖w.1‖ ≤ R → ‖w.2‖ ≤ R →
        w.1 = a + ψ w.2 → w.2 = b + φ w.1 → w = z := by
  let S := Metric.closedBall (0 : D × E) R
  have hz : (0 : D × E) ∈ S := Metric.mem_closedBall_self hR.le
  have hφn (u : D) (hu : ‖u‖ ≤ R) : ‖φ u‖ ≤ ε * R := by
    have h := hφ u (by simpa using hu) 0 (Metric.mem_closedBall_self hR.le)
    rw [hφ0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hu hε)
  have hψn (u : E) (hu : ‖u‖ ≤ R) : ‖ψ u‖ ≤ ε * R := by
    have h := hψ u (by simpa using hu) 0 (Metric.mem_closedBall_self hR.le)
    rw [hψ0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hu hε)
  let T : D × E → D × E := fun z ↦ (a + ψ z.2, b + φ z.1)
  have hmap : MapsTo T S S := by
    intro z hz
    have hn : ‖z.1‖ ≤ R ∧ ‖z.2‖ ≤ R := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using hz
    simp only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    dsimp [T]
    constructor
    · have := norm_add_le a (ψ z.2)
      have := hψn z.2 hn.2
      nlinarith
    · have := norm_add_le b (φ z.1)
      have := hφn z.1 hn.1
      nlinarith
  let t : S → S := hmap.restrict T S S
  have hcon : ContractingWith ⟨ε,hε⟩ t := by
    refine ⟨by change ε < 1; linarith, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    change dist (T u.val) (T v.val) ≤ ε * dist u.val v.val
    rw [dist_eq_norm, dist_eq_norm, Prod.norm_def, max_le_iff]
    have hun : ‖u.val.1‖ ≤ R ∧ ‖u.val.2‖ ≤ R := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using u.property
    have hvn : ‖v.val.1‖ ≤ R ∧ ‖v.val.2‖ ≤ R := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using v.property
    constructor
    · dsimp [T]
      simp only [add_sub_add_left_eq_sub]
      exact (hψ _ (by simpa using hun.2) _ (by simpa using hvn.2)).trans
        (mul_le_mul_of_nonneg_left (show ‖u.val.2-v.val.2‖ ≤ ‖u.val-v.val‖ from le_max_right _ _) hε)
    · dsimp [T]
      simp only [add_sub_add_left_eq_sub]
      exact (hφ _ (by simpa using hun.1) _ (by simpa using hvn.1)).trans
        (mul_le_mul_of_nonneg_left (show ‖u.val.1-v.val.1‖ ≤ ‖u.val-v.val‖ from le_max_left _ _) hε)
  have : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty S := ⟨⟨0,hz⟩⟩
  let z := hcon.fixedPoint t
  have hzfixed := hcon.fixedPoint_isFixedPt
  have heq : T z.val = z.val := congrArg Subtype.val hzfixed
  have hzn : ‖z.val.1‖ ≤ R ∧ ‖z.val.2‖ ≤ R := by
    simpa only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using z.property
  have h₁ : z.val.1 = a + ψ z.val.2 := (congrArg Prod.fst heq).symm
  have h₂ : z.val.2 = b + φ z.val.1 := (congrArg Prod.snd heq).symm
  refine ⟨z.val, hzn.1, hzn.2, h₁, h₂, ?_, ?_⟩
  · rw [Prod.norm_def, max_le_iff]
    change ‖z.val.1-a‖ ≤ ε*R ∧ ‖z.val.2-b‖ ≤ ε*R
    constructor
    · rw [h₁]
      simpa using hψn z.val.2 hzn.2
    · rw [h₂]
      simpa using hφn z.val.1 hzn.1
  · intro w hw₁ hw₂ hwe₁ hwe₂
    have hw : w ∈ S := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro hw₁ hw₂
    apply congrArg Subtype.val (hcon.fixedPoint_unique (x := ⟨w,hw⟩) ?_)
    apply Subtype.ext
    exact Prod.ext hwe₁.symm hwe₂.symm

/-- A finite family of small-slope graphs produces a crossed interpolation grid. -/
theorem small_slope_crossed_grid
    {D E I J : Type*} [NormedAddCommGroup D] [CompleteSpace D]
    [NormedAddCommGroup E] [CompleteSpace E] [Fintype I] [Fintype J]
    (φ : J → D → E) (ψ : I → E → D) (a : I → D) (b : J → E)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1/4)
    (ha : ∀ i, ‖a i‖ ≤ R/2) (hb : ∀ j, ‖b j‖ ≤ R/2)
    (hφ0 : ∀ j, φ j 0 = 0) (hψ0 : ∀ i, ψ i 0 = 0)
    (hφ : ∀ j, ∀ u ∈ Metric.closedBall (0:D) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖φ j u-φ j v‖ ≤ ε*‖u-v‖)
    (hψ : ∀ i, ∀ u ∈ Metric.closedBall (0:E) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖ψ i u-ψ i v‖ ≤ ε*‖u-v‖) :
    ∃ z : I × J → D × E,
      (∀ i j, ‖(z (i,j)).1‖ ≤ R ∧ ‖(z (i,j)).2‖ ≤ R ∧
        (z (i,j)).1 = a i+ψ i (z (i,j)).2 ∧
        (z (i,j)).2 = b j+φ j (z (i,j)).1) ∧
      ‖z-(fun ij ↦ (a ij.1,b ij.2))‖ ≤ ε*R ∧
      (∀ j, ‖(fun i ↦ (z (i,j)).1)-a‖ ≤ ε*R) ∧
      (∀ i, ‖(fun j ↦ (z (i,j)).2)-b‖ ≤ ε*R) := by
  classical
  have H (ij : I × J) := small_slope_graph_intersection
    (φ ij.2) (ψ ij.1) (a ij.1) (b ij.2) R ε hR hε hεquarter
    (ha ij.1) (hb ij.2) (hφ0 ij.2) (hψ0 ij.1) (hφ ij.2) (hψ ij.1)
  choose z hz₁ hz₂ he₁ he₂ hd _ using H
  have hnonneg : 0 ≤ ε*R := mul_nonneg hε hR.le
  refine ⟨z,fun i j ↦ ⟨hz₁ (i,j),hz₂ (i,j),he₁ (i,j),he₂ (i,j)⟩,
    (pi_norm_le_iff_of_nonneg hnonneg).mpr hd,?_,?_⟩
  · intro j
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro i
    exact (le_max_left _ _).trans (hd (i,j))
  · intro i
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro j
    exact (le_max_right _ _).trans (hd (i,j))

/-- A graph through a small target point has a small anchor and meets every sampled transverse graph. -/
theorem small_slope_target_crossings
    {D E J : Type*} [NormedAddCommGroup D] [CompleteSpace D]
    [NormedAddCommGroup E] [CompleteSpace E] [Fintype J]
    (φ : J → D → E) (ψ : E → D) (b : J → E) (w : D × E)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1/4)
    (hb : ∀ j, ‖b j‖ ≤ R/2) (hw : ‖w‖ ≤ R/4)
    (hφ0 : ∀ j, φ j 0 = 0) (hψ0 : ψ 0 = 0)
    (hφ : ∀ j, ∀ u ∈ Metric.closedBall (0:D) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖φ j u-φ j v‖ ≤ ε*‖u-v‖)
    (hψ : ∀ u ∈ Metric.closedBall (0:E) R, ∀ v ∈ Metric.closedBall 0 R,
      ‖ψ u-ψ v‖ ≤ ε*‖u-v‖) :
    ∃ a : D, ‖a‖ ≤ R/2 ∧ w.1 = a+ψ w.2 ∧ ∃ z : J → D × E,
      (∀ j, ‖(z j).1‖ ≤ R ∧ ‖(z j).2‖ ≤ R ∧
        (z j).1 = a+ψ (z j).2 ∧ (z j).2 = b j+φ j (z j).1) ∧
      ‖(fun j ↦ (z j).2)-b‖ ≤ ε*R := by
  classical
  let a := w.1-ψ w.2
  have hw₁ : ‖w.1‖ ≤ R/4 := (le_max_left _ _).trans hw
  have hw₂ : ‖w.2‖ ≤ R/4 := (le_max_right _ _).trans hw
  have hψw : ‖ψ w.2‖ ≤ ε*(R/4) := by
    have H := hψ w.2 (by simp only [Metric.mem_closedBall,dist_zero_right]; linarith)
      0 (Metric.mem_closedBall_self hR.le)
    rw [hψ0,sub_zero,sub_zero] at H
    exact H.trans (mul_le_mul_of_nonneg_left hw₂ hε)
  have ha : ‖a‖ ≤ R/2 := by
    have H := norm_sub_le w.1 (ψ w.2)
    dsimp [a]
    nlinarith
  have H (j : J) := small_slope_graph_intersection (φ j) ψ a (b j)
    R ε hR hε hεquarter ha (hb j) (hφ0 j) hψ0 (hφ j) hψ
  choose z hz₁ hz₂ he₁ he₂ hd _ using H
  refine ⟨a,ha,by dsimp [a]; abel,z,
    fun j ↦ ⟨hz₁ j,hz₂ j,he₁ j,he₂ j⟩,?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε hR.le)).mpr
  intro j
  exact (le_max_right _ _).trans (hd j)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
