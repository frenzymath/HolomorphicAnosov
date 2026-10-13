import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Cauchy

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

theorem pointwise_compact_from_conway_normality
    {Ω : Type*} [MetricSpace Ω] [CompleteSpace Ω]
    {G : Set ℂ} (F : Set C(G, Ω))
    (hN : ∀ u : ℕ → C(G, Ω), (∀ n, u n ∈ F) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : C(G, Ω),
        ∀ K : Set G, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v atTop K) :
    ∀ a : G, IsCompact (closure ((fun u : C(G, Ω) ↦ u a) '' F)) := by
  intro a
  let S : Set Ω := (fun u : C(G, Ω) ↦ u a) '' F
  have hCauchy : ∀ w : ℕ → Ω, (∀ n, w n ∈ S) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (w ∘ φ) := by
    intro w hw
    choose f hfF hfw using fun n ↦ hw n
    obtain ⟨φ, hφ, v, hv⟩ := hN f hfF
    have hta : Tendsto (fun n ↦ f (φ n) a) atTop (𝓝 (v a)) :=
      (hv {a} isCompact_singleton).tendsto_at (x := a) (mem_singleton a)
    exact ⟨φ, hφ, by simpa [Function.comp_def, hfw] using hta.cauchySeq⟩
  have htot : TotallyBounded S := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_contra hcover
    have hbad : ∀ t : Set Ω, t.Finite → ¬ S ⊆ ⋃ y ∈ t, Metric.ball y ε := by
      intro t ht
      exact fun hs ↦ hcover ⟨t, ht, hs⟩
    obtain ⟨w, hwS, hsep⟩ : ∃ w : ℕ → Ω, (∀ n, w n ∈ S) ∧
        ∀ n m, m < n → w n ∉ Metric.ball (w m) ε := by
      simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at hbad
      simpa only [forall_and, forall_mem_image, not_and] using!
        seq_of_forall_finite_exists hbad
    obtain ⟨φ, hφ, hc⟩ := hCauchy w hwS
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 hc) ε hε
    exact hsep (φ (N + 1)) (φ N) (hφ (Nat.lt_add_one N))
      (by simpa [Metric.mem_ball] using hN (N + 1) (Nat.le_add_right N 1) N le_rfl)
  exact htot.closure.isCompact_of_isClosed isClosed_closure

end HolomorphicAnosov

