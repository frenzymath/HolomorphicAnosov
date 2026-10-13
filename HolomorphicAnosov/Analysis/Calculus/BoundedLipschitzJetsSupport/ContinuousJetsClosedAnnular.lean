import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.ContinuousAnnularApproximation
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.ContinuousRepresentativeStructure

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS (3.3), p.28: continuous annular interpolation gives a complete continuous-jet
subspace. The eventual slope bound gives continuity at zero; complete subsets of
the ambient norm metric are closed. Choose representatives continuous on open
neighborhoods of zero, and choose each annular radius inside the two neighborhoods
needed for the adjacent interpolation, exactly as in the printed local-domain proof. -/
theorem continuousJets_closed_annular
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    @IsClosed (BoundedJet X Y)
      (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
      (continuousJets X Y : Set (BoundedJet X Y)) := by
  classical
  let : TopologicalSpace (BoundedJet X Y) :=
    (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hrep (j : ↥(continuousJets X Y)) :
      ∃ q : BoundedRepresentative X Y, jetClass X Y q = j ∧
        ∃ U : Set X, IsOpen U ∧ 0 ∈ U ∧ ContinuousOn (q : X → Y) U := j.property
  have hccomplete : CompleteSpace ↥(continuousJets X Y) := by
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    choose q hq hqc using fun n ↦ hrep (u n)
    have huc : CauchySeq (fun n ↦ (u n : BoundedJet X Y)) :=
      (continuousJets X Y).subtypeL.uniformContinuous.comp_cauchySeq hu
    have hc : CauchySeq (fun n ↦ jetClass X Y (q n)) := by simpa only [hq] using huc
    obtain ⟨g, hg0, ⟨R, hR, hgcont⟩, hg⟩ := continuous_annular_approximation X Y q hqc hc
    obtain ⟨N, hN⟩ := hg 1 zero_lt_one
    obtain ⟨C, hC, hqb⟩ := (q N).property.2
    have hgb : ∀ᶠ x in 𝓝 (0 : X), ‖g x‖ ≤ (1+C) * ‖x‖ := by
      filter_upwards [hN N le_rfl, eventually_nhdsWithin_iff.mp hqb] with x hx hy
      by_cases hx0 : x = 0
      · subst x; simp [hg0]
      have hqy := hy (by simpa using hx0)
      have htri := norm_le_norm_sub_add (g x) ((q N : X → Y) x)
      nlinarith
    let r : BoundedRepresentative X Y :=
      ⟨g, hg0, 1+C, by linarith, hgb.filter_mono nhdsWithin_le_nhds⟩
    have hgzero : ContinuousAt g 0 := by
      change Tendsto g (𝓝 0) (𝓝 (g 0))
      rw [hg0]
      apply squeeze_zero_norm' hgb
      simpa using (tendsto_norm_zero (E := X)).const_mul (1+C)
    have hjr : jetClass X Y r ∈ continuousJets X Y := by
      refine ⟨r, rfl, Metric.ball 0 R, Metric.isOpen_ball, Metric.mem_ball_self hR, ?_⟩
      intro x hx
      by_cases hx0 : x = 0
      · subst x; exact hgzero.continuousWithinAt
      · exact (hgcont x hx0 (by simpa [Metric.mem_ball, dist_zero_right] using hx)).continuousWithinAt
    refine ⟨⟨jetClass X Y r, hjr⟩, ?_⟩
    apply tendsto_subtype_rng.mpr
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := hg (ε/2) (half_pos hε)
    refine ⟨M, fun m hm ↦ ?_⟩
    have hs : ‖jetClass X Y (r - q m)‖ ≤ ε/2 := by
      change sInf (slopeBounds X Y (r - q m)) ≤ ε/2
      exact csInf_le ⟨0, fun _ h ↦ h.1⟩ ⟨(half_pos hε).le,
        (hM m hm).filter_mono nhdsWithin_le_nhds⟩
    have heq : jetClass X Y (r - q m) = jetClass X Y r - (u m : BoundedJet X Y) :=
      (map_sub ((littleORepresentatives X Y).mkQ) r (q m)).trans
        (congrArg (fun z ↦ jetClass X Y r - z) (hq m))
    rw [heq] at hs
    rw [dist_eq_norm, norm_sub_rev]
    exact hs.trans_lt (by linarith)
  exact (completeSpace_coe_iff_isComplete.mp hccomplete).isClosed

end HolomorphicAnosov.BoundedLipschitzJets

