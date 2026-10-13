import HolomorphicAnosov.Analysis.Complex.ConwayPointwiseCompactFromNormality
import HolomorphicAnosov.Analysis.Complex.ConwayEquicontinuousFromNormality
import HolomorphicAnosov.Analysis.Complex.CompactOpenEquicontinuousSubsequence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Conway's compact-open Arzelà–Ascoli normality criterion

Source: Conway, *Functions of One Complex Variable I*, second edition (1978),
Chapter VII, §1, Theorem 1.23, printed pp.148–150 (PDF pp.159–161).
The domain has the subspace topology of the given open subset of `ℂ`.
-/

open Filter

namespace HolomorphicAnosov

/--
Conway's Arzelà–Ascoli theorem, Chapter VII, §1, Theorem 1.23, printed pp.148–150.
A family of continuous maps into a complete metric space is sequentially normal for
compact-uniform convergence exactly when it is equicontinuous at each point and its
pointwise value sets have compact closures. The limit is a continuous map on the original
domain and is not required to lie in the family. `EquicontinuousAt` has exactly Conway's
epsilon-delta meaning by `Metric.equicontinuousAt_iff` and the inherited complex metric.

The necessity direction uses the named pointwise compactness and equicontinuity
helpers. For sufficiency, a sequence in the family inherits equicontinuity by
reindexing; at each point its values lie in the family's compact point-value closure.
The compact-open Ascoli subsequence theorem supplies the required continuous limit.
The helpers document their proofs and their relation to Conway's source argument.
No connectedness, boundedness, or nonemptiness assumption is imposed.
-/
theorem conway_compact_open_ascoli_normality_g2
    {Ω : Type*} [MetricSpace Ω] [CompleteSpace Ω]
    {G : Set ℂ} (hG : IsOpen G) (F : Set C(G, Ω)) :
    (∀ u : ℕ → C(G, Ω), (∀ n, u n ∈ F) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : C(G, Ω),
        ∀ K : Set G, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v atTop K) ↔
      ((∀ a : G, EquicontinuousAt (fun u : F ↦ fun z : G ↦ u.val z) a) ∧
        ∀ a : G, IsCompact (closure ((fun u : C(G, Ω) ↦ u a) '' F))) := by
  constructor
  · intro hN
    exact ⟨equicontinuous_from_conway_normality F hN,
      pointwise_compact_from_conway_normality F hN⟩
  · rintro ⟨hEq, hComp⟩ u hu
    have heq : Equicontinuous (fun n x ↦ u n x) := by
      intro a
      exact (hEq a).comp (fun n ↦ ⟨u n, hu n⟩)
    have hpoint : ∀ x : G, ∃ Q : Set Ω, IsCompact Q ∧ ∀ n, u n x ∈ Q := by
      intro x
      refine ⟨closure ((fun f : C(G, Ω) ↦ f x) '' F), hComp x, ?_⟩
      intro n
      exact subset_closure ⟨u n, hu n, rfl⟩
    obtain ⟨φ, hφ, v, _, hunif⟩ :=
      compact_open_equicontinuous_subsequence hG u heq hpoint
    exact ⟨φ, hφ, v, hunif⟩

end HolomorphicAnosov

