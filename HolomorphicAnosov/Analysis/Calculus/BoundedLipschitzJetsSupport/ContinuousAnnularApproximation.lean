import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularWeight
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.BoundedRepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularInterpolation
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularRadii
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.EventuallySlopeBound
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS p.28's continuous annular approximation. Choose representatives continuous
on open neighborhoods U_n. At step n intersect the finite pair-estimate neighborhood
with U_n and U_(n+1), then choose a closed ball in that intersection. Decreasing radii
inside these balls make the adjacent affine interpolation continuous off zero. Its
difference from q_m is a convex combination of the two controlled differences.
Cauchyness and the vanishing geometric error give the asserted eventual slope bound. -/
theorem continuous_annular_approximation
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (q : ℕ → BoundedRepresentative X Y) (hqcont : ∀ n, ∃ U : Set X, IsOpen U ∧ 0 ∈ U ∧ ContinuousOn (q n : X → Y) U)
    (hc : CauchySeq (fun n ↦ jetClass X Y (q n))) :
    ∃ g : X → Y, g 0 = 0 ∧
      (∃ R > 0, ∀ x, x ≠ 0 → ‖x‖ < R → ContinuousAt g x) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,
      ∀ᶠ x in 𝓝 (0 : X), ‖g x - (q m : X → Y) x‖ ≤ ε * ‖x‖ := by
  classical
  choose U hU h0U hqc using hqcont
  have he (n : ℕ) : ∀ᶠ x in 𝓝 (0 : X), ∀ i m : Fin (n+2),
      ‖(q i : X → Y) x - (q m : X → Y) x‖ ≤
        (‖jetClass X Y (q i) - jetClass X Y (q m)‖ + (1/2:ℝ)^n) * ‖x‖ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro m
    have hb := eventually_slope_le X Y (q i - q m)
      (C := ‖jetClass X Y (q i) - jetClass X Y (q m)‖ + (1/2:ℝ)^n) (by
        change ‖jetClass X Y (q i - q m)‖ < _
        simp only [jetClass]
        exact lt_add_of_pos_right _ (pow_pos (by norm_num : (0:ℝ)<1/2) n))
    filter_upwards [eventually_nhdsWithin_iff.mp hb] with x hx
    by_cases hx0 : x = 0
    · subst x; simp [(q i).property.1, (q m).property.1]
    · exact hx (by simpa using hx0)
  have heU (n : ℕ) : ∀ᶠ x in 𝓝 (0 : X),
      (∀ i m : Fin (n+2), ‖(q i : X → Y) x - (q m : X → Y) x‖ ≤
        (‖jetClass X Y (q i) - jetClass X Y (q m)‖ + (1/2:ℝ)^n) * ‖x‖) ∧
        x ∈ U n ∧ x ∈ U (n+1) := by
    filter_upwards [he n, (hU n).mem_nhds (h0U n),
      (hU (n+1)).mem_nhds (h0U (n+1))] with x hx hx0 hx1
    exact ⟨hx, hx0, hx1⟩
  choose δ hδ hb using fun n ↦ Metric.nhds_basis_closedBall.eventually_iff.mp (heU n)
  obtain ⟨r, hrpos, hra, hrd, hrt⟩ := annular_radii δ hδ
  have hi (x : X) (hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0) :
      ∃ n, r (n+1) < ‖x‖ ∧ ‖x‖ ≤ r n := annular_index hrt hx.1 hx.2
  obtain ⟨g, hg0, hgeq, hgcont⟩ := annular_interpolation
    (fun n ↦ (q n : X → Y)) hrpos hra hrt (fun n ↦ ⟨
      (hqc n).mono (fun x hx ↦ (hb n (Metric.closedBall_subset_closedBall (hrd n) hx)).2.1),
      (hqc (n+1)).mono (fun x hx ↦ (hb n (Metric.closedBall_subset_closedBall (hrd n) hx)).2.2)⟩)
  refine ⟨g, hg0, ⟨r 0, hrpos 0, hgcont⟩, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/2) (half_pos hε)
  have ht : Tendsto (fun n : ℕ ↦ (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (ε/2) (half_pos hε))
  refine ⟨max N K, fun m hm ↦ ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : X) (hrpos m)] with x hx
  have hxm : ‖x‖ ≤ r m := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hx0 : x = 0
  · subst x; simp [hg0, (q m).property.1]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨k, hkl, hku⟩ := hi x ⟨hxpos, hxm.trans (hra.antitone (Nat.zero_le m))⟩
  have hmk : m ≤ k := by
    by_contra hh
    have hkm : k + 1 ≤ m := by omega
    have hh := hra.antitone hkm
    linarith
  have hxd : x ∈ Metric.closedBall 0 (δ k) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hku.trans (hrd _)
  have hbound0 := (hb k hxd).1 ⟨k, by omega⟩ ⟨m, by omega⟩
  have hbound1 := (hb k hxd).1 ⟨k+1, by omega⟩ ⟨m, by omega⟩
  have hd0 : ‖jetClass X Y (q k) - jetClass X Y (q m)‖ < ε/2 := by
    simpa [dist_eq_norm] using hN k (by omega) m (by omega)
  have hd1 : ‖jetClass X Y (q (k+1)) - jetClass X Y (q m)‖ < ε/2 := by
    simpa [dist_eq_norm] using hN (k+1) (by omega) m (by omega)
  have hg := hK k (by omega)
  have hb0 : ‖(q k : X → Y) x - (q m : X → Y) x‖ ≤ ε * ‖x‖ :=
    hbound0.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
  have hb1 : ‖(q (k+1) : X → Y) x - (q m : X → Y) x‖ ≤ ε * ‖x‖ :=
    hbound1.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
  rw [hgeq k x hkl.le hku]
  have hw : 0 ≤ annularWeight r k ‖x‖ ∧ annularWeight r k ‖x‖ ≤ 1 := by
    have hd : 0 < r k - r (k+1) := sub_pos.mpr (hra (Nat.lt_succ_self k))
    constructor
    · exact div_nonneg (sub_nonneg.mpr hku) hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have heq : annularWeight r k ‖x‖ • (q (k+1) : X → Y) x +
      (1-annularWeight r k ‖x‖) • (q k : X → Y) x - (q m : X → Y) x =
      annularWeight r k ‖x‖ • ((q (k+1) : X → Y) x - (q m : X → Y) x) +
      (1-annularWeight r k ‖x‖) • ((q k : X → Y) x - (q m : X → Y) x) := by
    module
  rw [heq]
  calc
    _ ≤ ‖annularWeight r k ‖x‖ • ((q (k+1) : X → Y) x - (q m : X → Y) x)‖ +
        ‖(1-annularWeight r k ‖x‖) • ((q k : X → Y) x - (q m : X → Y) x)‖ := norm_add_le _ _
    _ = annularWeight r k ‖x‖ * ‖(q (k+1) : X → Y) x - (q m : X → Y) x‖ +
        (1-annularWeight r k ‖x‖) * ‖(q k : X → Y) x - (q m : X → Y) x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hw.1, Real.norm_of_nonneg (sub_nonneg.mpr hw.2)]
    _ ≤ annularWeight r k ‖x‖ * (ε * ‖x‖) + (1-annularWeight r k ‖x‖) * (ε * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hb1 hw.1)
        (mul_le_mul_of_nonneg_left hb0 (sub_nonneg.mpr hw.2))
    _ = ε * ‖x‖ := by ring

end HolomorphicAnosov.BoundedLipschitzJets

