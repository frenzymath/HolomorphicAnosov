import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularApproximation

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS (3.3), p.28, first conclusion. The annular representative approximates
one bounded representative, so is bounded itself; its eventual slope differences
then bound the quotient norm and prove convergence of every Cauchy sequence. -/
theorem boundedJets_complete_annular
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : CompleteSpace (BoundedJet X Y) := by
  classical
  let : TopologicalSpace (BoundedJet X Y) :=
    (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  choose q hq using fun n ↦ (Submodule.Quotient.mk_surjective (littleORepresentatives X Y)) (u n)
  have hqu (n : ℕ) : jetClass X Y (q n) = u n := hq n
  have hc : CauchySeq (fun n ↦ jetClass X Y (q n)) := by simpa only [hqu] using hu
  obtain ⟨g, hg0, hg⟩ := annular_approximation X Y q hc
  obtain ⟨N, hN⟩ := hg 1 zero_lt_one
  obtain ⟨C, hC, hqb⟩ := (q N).property.2
  have hgb : ∀ᶠ x in 𝓝[≠] (0 : X), ‖g x‖ ≤ (1+C) * ‖x‖ := by
    filter_upwards [(hN N le_rfl).filter_mono nhdsWithin_le_nhds, hqb] with x hx hy
    have htri := norm_le_norm_sub_add (g x) ((q N : X → Y) x)
    nlinarith
  let r : BoundedRepresentative X Y := ⟨g, hg0, 1+C, by linarith, hgb⟩
  refine ⟨jetClass X Y r, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := hg (ε/2) (half_pos hε)
  refine ⟨M, fun m hm ↦ ?_⟩
  have hs : ‖jetClass X Y (r - q m)‖ ≤ ε/2 := by
    change sInf (slopeBounds X Y (r - q m)) ≤ ε/2
    exact csInf_le ⟨0, fun _ h ↦ h.1⟩ ⟨(half_pos hε).le,
      (hM m hm).filter_mono nhdsWithin_le_nhds⟩
  have heq : jetClass X Y (r - q m) = jetClass X Y r - u m := by
    exact (map_sub ((littleORepresentatives X Y).mkQ) r (q m)).trans
      (congrArg (fun z ↦ jetClass X Y r - z) (hqu m))
  rw [heq] at hs
  rw [dist_eq_norm, norm_sub_rev]
  exact hs.trans_lt (by linarith)

end HolomorphicAnosov.BoundedLipschitzJets

