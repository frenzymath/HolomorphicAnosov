import HolomorphicAnosov.Analysis.Complex.ConwayUnivalentLimit
import HolomorphicAnosov.Analysis.Complex.ConwayNormalizedDiskLimit
import HolomorphicAnosov.Analysis.Complex.ConwayBoundedHolomorphicSequenceNormality
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Order.IsLUB

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The derivative extremum in Conway VII Lemma 4.3, pp.161–163. A nonempty family
of zero-normalized disk injections containing a map with nonzero derivative has
an element maximizing derivative norm. Schwarz bounds the family on a source disk.
Take a sequence tending to the positive supremum and extract a compact-uniform
limit by bounded normality. Derivative convergence gives the supremum at the limit;
it excludes a constant limit. The univalent-limit theorem then gives injectivity. -/
theorem conway_extremal_disk_map
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {a : ℂ} (ha : a ∈ U)
    (hseed : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧
      MapsTo f U (Metric.ball (0 : ℂ) 1) ∧ f a = 0 ∧ deriv f a ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧
      MapsTo f U (Metric.ball (0 : ℂ) 1) ∧ f a = 0 ∧ deriv f a ≠ 0 ∧
      ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → InjOn g U →
        MapsTo g U (Metric.ball (0 : ℂ) 1) → g a = 0 →
        ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  classical
  let P : (ℂ → ℂ) → Prop := fun f ↦ DifferentiableOn ℂ f U ∧ InjOn f U ∧
    MapsTo f U (Metric.ball (0 : ℂ) 1) ∧ f a = 0
  let S : Set ℝ := {r | ∃ f : ℂ → ℂ, P f ∧ ‖deriv f a‖ = r}
  obtain ⟨f₀, hf₀, hi₀, hm₀, hz₀, hd₀⟩ := hseed
  have hs₀ : ‖deriv f₀ a‖ ∈ S := ⟨f₀, ⟨hf₀, hi₀, hm₀, hz₀⟩, rfl⟩
  have hSne : S.Nonempty := ⟨_, hs₀⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hU a ha
  have hSbdd : BddAbove S := by
    refine ⟨1 / r, ?_⟩
    rintro v ⟨g, hg, rfl⟩
    apply Complex.norm_deriv_le_div_of_mapsTo_ball (hg.1.mono hrsub) ?_ hr
    intro z hz
    rw [hg.2.2.2]
    exact Metric.ball_subset_closedBall (hg.2.2.1 (hrsub hz))
  obtain ⟨u, huMono, hut, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hFP hFnorm using huS
  obtain ⟨φ, hφ, f, hf, hlim⟩ := conway_bounded_holomorphic_sequence_normality_g2
    hU F (fun n ↦ (hFP n).1) (by
      intro K hK hKU
      exact ⟨1, zero_le_one, fun n z hz ↦ (mem_ball_zero_iff.mp ((hFP n).2.2.1 (hKU hz))).le⟩)
  obtain ⟨_, hfm, hfa, hderlim⟩ := conway_normalized_disk_limit hU hconn ha
    (fun n ↦ (hFP (φ n)).1) (fun n ↦ (hFP (φ n)).2.2.1)
    (fun n ↦ (hFP (φ n)).2.2.2) (fun K hKU hK ↦ hlim K hK hKU)
  have hder : ‖deriv f a‖ = sSup S := by
    apply tendsto_nhds_unique (hderlim.tendsto_at ha).norm
    simpa only [hFnorm, Function.comp_def] using hut.comp hφ.tendsto_atTop
  have hpos : 0 < ‖deriv f a‖ := by
    rw [hder]
    exact (norm_pos_iff.mpr hd₀).trans_le (le_csSup hSbdd hs₀)
  have hnc : ¬∃ c : ℂ, EqOn f (fun _ ↦ c) U := by
    rintro ⟨c, hc⟩
    have heq : f =ᶠ[𝓝 a] fun _ ↦ c := by
      filter_upwards [hU.mem_nhds ha] with z hz using hc hz
    have hd : deriv f a = 0 := by
      rw [heq.deriv_eq]
      exact deriv_const _ _
    simp [hd] at hpos
  have hfi := conway_univalent_limit hU hconn (fun n ↦ (hFP (φ n)).1)
    (fun n ↦ (hFP (φ n)).2.1) (fun K hKU hK ↦ hlim K hK hKU) hnc
  refine ⟨f, hf, hfi, hfm, hfa, norm_pos_iff.mp hpos, ?_⟩
  intro g hg hi hm hz
  rw [hder]
  exact le_csSup hSbdd ⟨g, ⟨hg, hi, hm, hz⟩, rfl⟩

end HolomorphicAnosov
