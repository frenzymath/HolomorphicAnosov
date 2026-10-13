import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences

/-!
# Compact-open extraction on an open complex domain

Source: Conway, *Functions of One Complex Variable I*, VII §1 Theorem 1.23,
pp.148–150, and Lyubich, *Conformal Geometry and Dynamics of Quadratic
Polynomials*, §4.3 Theorem 4.8, pp.111–112. This is the compact-open Ascoli
extraction used after establishing equicontinuity; it asserts no holomorphic
estimate and includes punctured open domains and compact metric targets.
-/

open Set Filter
open scoped Topology _root_.Topology UniformConvergence

namespace HolomorphicAnosov

/-- An equicontinuous sequence with pointwise relatively compact range on an open
complex domain has a strictly increasing subsequence converging in the native
compact-open topology, equivalently uniformly on every compact subset.

Source: Conway VII §1 Theorem 1.23, pp.148–150. Apply Mathlib's general Ascoli
compact-closure theorem to the range of the sequence. The continuous-map space
embeds uniformly in the space of functions with compact convergence; completeness
makes this embedding closed. Equicontinuity and pointwise compact enclosures are
exactly Ascoli's hypotheses. The open domain is locally compact and second
countable, hence sigma compact; its continuous-map space has countably generated
uniformity. Compactness therefore supplies a convergent strictly increasing
subsequence. Mathlib's compact-convergence equivalence gives the stated uniform
convergence. The empty domain and compact targets are included. -/
theorem compact_open_equicontinuous_subsequence
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {U : Set ℂ} (hU : IsOpen U) (F : ℕ → C(U, Y))
    (heq : Equicontinuous (fun n x ↦ F n x))
    (hpoint : ∀ x : U, ∃ Q : Set Y, IsCompact Q ∧ ∀ n, F n x ∈ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : C(U, Y),
      Tendsto (F ∘ φ) atTop (𝓝 f) ∧
      ∀ K : Set U, IsCompact K →
        TendstoUniformlyOn (fun n x ↦ F (φ n) x) f atTop K := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : T2Space (U →ᵤ[{K | IsCompact K}] Y) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  have hclosed : Topology.IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact : C(U, Y) → U →ᵤ[{K | IsCompact K}] Y) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hfamily : Equicontinuous (fun f : range F ↦ fun x : U ↦ f.val x) := by
    let select : range F → ℕ := fun f ↦ Classical.choose f.property
    have hselect (f : range F) : F (select f) = f.val := Classical.choose_spec f.property
    simpa only [Function.comp_def, hselect] using heq.comp select
  have hcompact : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(U, Y) ↦ (f : U → Y)) (𝔖 := {K | IsCompact K})
      (fun _ h ↦ h) hclosed
    · intro K _
      exact hfamily.equicontinuousOn K
    · intro K _ x _
      obtain ⟨Q, hQ, hFQ⟩ := hpoint x
      refine ⟨Q, hQ, ?_⟩
      rintro f ⟨n, rfl⟩
      exact hFQ n
  obtain ⟨f, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨φ, hφ, f, hlim,
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim⟩

end HolomorphicAnosov
