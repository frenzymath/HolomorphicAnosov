import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Normality for compact-uniform convergence implies equicontinuity at every point.

This is the necessity step of Conway, Functions of One Complex Variable I, VII §1,
Theorem 1.23, pp.148–150. The following sequence proof is agent-written, using Mathlib's
uniform convergence at varying points instead of Conway's finite-net argument.
If equicontinuity fails at a, choose ε>0, points x_n with dist(x_n,a)<1/(n+1), and
maps u_n from the family whose values at a and x_n differ by at least ε. The set
consisting of a and all x_n is compact. Normality extracts a subsequence converging
uniformly there to a continuous v. Its evaluations at a and at the corresponding x_n
both converge to v(a), contradicting the lower bound ε. Empty families and empty
domains are included, and neither openness nor target completeness is needed. -/
theorem equicontinuous_from_conway_normality
    {Ω : Type*} [MetricSpace Ω]
    {G : Set ℂ} (F : Set C(G, Ω))
    (hN : ∀ u : ℕ → C(G, Ω), (∀ n, u n ∈ F) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : C(G, Ω),
        ∀ K : Set G, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v atTop K) :
    ∀ a : G, EquicontinuousAt (fun u : F ↦ fun z : G ↦ u.val z) a := by
  classical
  intro a
  rw [Metric.equicontinuousAt_iff]
  by_contra h
  push Not at h
  obtain ⟨ε, hε, h⟩ := h
  have hw : ∀ n : ℕ, ∃ x : G, dist x a < 1 / ((n : ℝ) + 1) ∧
      ∃ u : F, ε ≤ dist (u.val a) (u.val x) := by
    intro n
    exact h _ (by positivity)
  choose x hx u hu using hw
  have hxlim : Tendsto x atTop (𝓝 a) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hx n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, v, hv⟩ := hN (fun n ↦ (u n).val) (fun n ↦ (u n).property)
  let K : Set G := insert a (range x)
  have hK : IsCompact K := hxlim.isCompact_insert_range
  have hfixed : Tendsto (fun n ↦ (u (φ n)).val a) atTop (𝓝 (v a)) :=
    (hv K hK).tendsto_at (mem_insert a _)
  have hvar : Tendsto (fun n ↦ (u (φ n)).val (x (φ n))) atTop (𝓝 (v a)) := by
    apply (hv K hK).tendsto_comp v.continuous.continuousAt.continuousWithinAt
    exact tendsto_nhdsWithin_iff.mpr ⟨hxlim.comp hφ.tendsto_atTop,
      Eventually.of_forall (fun n ↦ mem_insert_of_mem _ (mem_range_self (φ n)))⟩
  have hdist : Tendsto (fun n ↦ dist ((u (φ n)).val a) ((u (φ n)).val (x (φ n))))
      atTop (𝓝 0) := by simpa using hfixed.dist hvar
  have := ge_of_tendsto' hdist (fun n ↦ hu (φ n))
  exact (not_le_of_gt hε) this

end HolomorphicAnosov
