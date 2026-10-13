import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Quantitative fixed-support seminorm continuity

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69, equation (6.8).  Uniform continuity of the spatial jets on a fixed
compact support gives a single modulus for any finite family of seminorms.
-/

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- Uniform continuity of the spatial jets of a fixed-support family yields a
quantitative modulus for every finite fixed-support seminorm family. -/
theorem fixed_support_seminorm_uniform_modulus
    {E X : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : TopologicalSpace.Compacts X}
    (Ψ : E → ContDiffMapSupportedIn X ℂ ⊤ K) (s : Finset ℕ)
    (hjet : ∀ i ∈ s, UniformContinuous
      (fun z : E × K ↦ iteratedFDeriv ℝ i (Ψ z.1) z.2.1)) :
    ∀ ε > 0, ∃ δ > 0, ∀ p q : E, dist p q < δ →
      s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ K) (Ψ p - Ψ q) ≤ ε := by
  classical
  intro ε hε
  have hfinite : ∀ t : Finset ℕ, t ⊆ s → ∃ δ > 0,
      ∀ p q : E, dist p q < δ →
        (∀ i ∈ t, ∀ y : X, ∀ hy : y ∈ K,
          ‖iteratedFDeriv ℝ i (Ψ p) y - iteratedFDeriv ℝ i (Ψ q) y‖ ≤ ε) := by
    intro t hts
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨1, by positivity, ?_⟩
        intro p q hpq i hi
        simp at hi
    | @insert i t hi ih =>
        obtain ⟨δt, hδt, ht⟩ := ih (fun j hj ↦ hts (Finset.mem_insert_of_mem hj))
        obtain ⟨δi, hδi, hju⟩ := Metric.uniformContinuous_iff.mp
          (hjet i (hts (Finset.mem_insert_self i t))) ε hε
        refine ⟨min δt δi, lt_min hδt hδi, ?_⟩
        intro p q hpq j hj y hy
        rcases Finset.mem_insert.mp hj with rfl | hj
        · have hpqy : dist (p, (⟨y, hy⟩ : K)) (q, (⟨y, hy⟩ : K)) < δi := by
            simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using
              (lt_of_lt_of_le hpq (min_le_right _ _))
          simpa only [dist_eq_norm] using (hju hpqy).le
        · exact ht p q (lt_of_lt_of_le hpq (min_le_left _ _)) j hj y hy
  obtain ⟨δ, hδ, hd⟩ := hfinite s (fun _ hi ↦ hi)
  refine ⟨δ, hδ, ?_⟩
  intro p q hpq
  apply Seminorm.finset_sup_apply_le hε.le
  intro i hi
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ hε.le i (Ψ p - Ψ q)).mpr
  intro y hy
  change ‖iteratedFDeriv ℝ i ((Ψ p : X → ℂ) - (Ψ q : X → ℂ)) y‖ ≤ ε
  rw [iteratedFDeriv_sub_apply ((Ψ p).contDiff.of_le (by simp)).contDiffAt
    ((Ψ q).contDiff.of_le (by simp)).contDiffAt]
  exact hd p q hpq i hi y hy


end HolomorphicAnosov.Analysis

