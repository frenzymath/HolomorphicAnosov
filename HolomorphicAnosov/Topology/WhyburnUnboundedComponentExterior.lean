import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

namespace HolomorphicAnosov

open Set Metric

/- A nonempty unbounded complementary component contains the exterior of a
closed ball about every pole, when the removed set is compact.

Source: Whyburn, *Topological Analysis*, Chapter III (2.12), p.33; this is
the radial-exterior step used in the inversion reduction. -/
theorem unbounded_component_contains_exterior
    (H R : Set (EuclideanSpace ℝ (Fin 2)))
    (hH_compact : IsCompact H) (_hR_nonempty : R.Nonempty)
    (hR_unbounded : ¬ Bornology.IsBounded R)
    (hR_component : ∃ x ∈ R, connectedComponentIn Hᶜ x = R)
    (q : EuclideanSpace ℝ (Fin 2)) :
    ∃ B : ℝ, 0 < B ∧ H ⊆ Metric.closedBall q B ∧
      (Metric.closedBall q B)ᶜ ⊆ R := by
  obtain ⟨x, hxR, hxcomp⟩ := hR_component
  obtain ⟨B₀, hB₀⟩ := (isBounded_iff_subset_closedBall q).mp hH_compact.isBounded
  let B := max B₀ 0 + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right B₀ 0]
  have hHB : H ⊆ closedBall q B := hB₀.trans (closedBall_subset_closedBall (by
    dsimp [B]
    linarith [le_max_left B₀ 0]))
  let E := (closedBall q B)ᶜ
  have hpolar :
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ q + p.1 • p.2) ''
        (Ioi B ×ˢ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) = E := by
    ext z
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hu
      change ¬ dist (q + r • u) q ≤ B
      simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hB.trans hr), hu'] using hr
    · intro hz
      have hz' : B < ‖z - q‖ := by
        simpa [E, mem_closedBall, dist_eq_norm] using hz
      have hnorm : 0 < ‖z - q‖ := hB.trans hz'
      refine ⟨(‖z - q‖, (‖z - q‖⁻¹ : ℝ) • (z - q)), ⟨hz', ?_⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ hnorm.ne']
      · change q + ‖z - q‖ • ((‖z - q‖⁻¹ : ℝ) • (z - q)) = z
        rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul, add_sub_cancel]
  have hE : IsPreconnected E := by
    rw [← hpolar]
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank]
      simp
    exact (isPreconnected_Ioi.prod (isPreconnected_sphere hrank 0 1)).image _
      (continuous_const.add (continuous_fst.smul continuous_snd)).continuousOn
  have hER : (E ∩ R).Nonempty := by
    by_contra h
    apply hR_unbounded
    apply isBounded_closedBall.subset
    intro z hz
    by_contra hzB
    exact h ⟨z, hzB, hz⟩
  have hRsub : R ⊆ Hᶜ := hxcomp ▸ connectedComponentIn_subset Hᶜ x
  have hRconn : IsPreconnected R := hxcomp ▸ isPreconnected_connectedComponentIn
  have hEsub : E ⊆ Hᶜ := fun _ hz hzh ↦ hz (hHB hzh)
  obtain ⟨y, hyE, hyR⟩ := hER
  have hsub := (hE.union y hyE hyR hRconn).subset_connectedComponentIn
    (Or.inr hxR) (union_subset hEsub hRsub)
  refine ⟨B, hB, hHB, ?_⟩
  exact subset_union_left.trans (hxcomp ▸ hsub)

end HolomorphicAnosov

