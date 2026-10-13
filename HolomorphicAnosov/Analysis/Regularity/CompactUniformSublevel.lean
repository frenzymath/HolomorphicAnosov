import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Uniform small sublevel sets on a compact family

A compact family in the uniform norm inherits one common positive sublevel
threshold from individual positive thresholds. This is the compactness step
in the measurable-subset lower-bound argument for polynomials.
-/

open MeasureTheory Set
open scoped Topology _root_.Topology ENNReal

namespace HolomorphicAnosov.Analysis.Regularity

/-- A compact family of continuous real functions on a compact space has a
uniform positive small-sublevel threshold whenever each member has one.

Source: agent-written compactness step for Campanato (1964), Lemma [2.I],
printed pp.140–143, filling the uniform lower-bound step by sublevel sets.
Proof: if the sublevel set of `f` at `r > 0` has measure below `ε`, every
function within uniform distance `r / 2` has its sublevel set at `r / 2`
contained in that set. Compactness gives finitely many such neighborhoods;
the minimum of their positive thresholds works. The proof uses compact-set
induction, whose empty, restriction and union cases express this finite-cover
argument. No measurability or finiteness of the measure is needed for this
step, since only monotonicity of outer measure is used.
DAG node: analysis.compact_uniform_sublevel_g18. -/
theorem compact_uniform_sublevel
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (μ : Measure X) (K : Set (C(X, ℝ))) (hK : IsCompact K) (ε : ℝ≥0∞)
    (hsmall : ∀ f ∈ K, ∃ r : ℝ, 0 < r ∧ μ {x | |f x| ≤ r} < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ f ∈ K, μ {x | |f x| ≤ r} < ε := by
  let P : Set (C(X, ℝ)) → Prop := fun S ↦
    ∃ r : ℝ, 0 < r ∧ ∀ f ∈ S, μ {x | |f x| ≤ r} < ε
  change P K
  apply hK.induction_on (p := P)
  · exact ⟨1, zero_lt_one, fun _ hf ↦ False.elim hf⟩
  · intro S U hSU hU
    obtain ⟨r, hr, h⟩ := hU
    exact ⟨r, hr, fun f hf ↦ h f (hSU hf)⟩
  · intro S U hS hU
    obtain ⟨r, hr, hS⟩ := hS
    obtain ⟨s, hs, hU⟩ := hU
    refine ⟨min r s, lt_min hr hs, fun f hf ↦ ?_⟩
    rcases hf with hf | hf
    · exact (measure_mono (fun _ hx ↦ hx.trans (min_le_left r s))).trans_lt (hS f hf)
    · exact (measure_mono (fun _ hx ↦ hx.trans (min_le_right r s))).trans_lt (hU f hf)
  · intro f hf
    obtain ⟨r, hr, hmeasure⟩ := hsmall f hf
    refine ⟨Metric.ball f (r / 2), ?_, r / 2, half_pos hr, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds f (half_pos hr))
    · intro g hg
      apply lt_of_le_of_lt (measure_mono ?_) hmeasure
      intro x hx
      have hdist : dist (f x) (g x) < r / 2 :=
        (ContinuousMap.dist_apply_le_dist x).trans_lt (by
          simpa only [Metric.mem_ball, dist_comm] using hg)
      have habs : |f x| ≤ |f x - g x| + |g x| := by
        simpa using abs_add_le (f x - g x) (g x)
      rw [Real.dist_eq] at hdist
      change |g x| ≤ r / 2 at hx
      change |f x| ≤ r
      linarith

end HolomorphicAnosov.Analysis.Regularity

