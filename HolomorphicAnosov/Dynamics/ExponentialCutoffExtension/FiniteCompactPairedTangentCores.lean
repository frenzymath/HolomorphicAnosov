import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base
import HolomorphicAnosov.Topology.Homology.FiniteCompactChartCover

/-!
# Finite paired source and receiving tangent cores

DAG node: `analysis.finite_compact_paired_tangent_cores_g4`.
Source: Lee (2003), Lemma 1.6 and Proposition 2.24, for compact frame cores;
Hirsch–Pugh–Shub (1977), proof of Theorem 5.5, pp. 61–62, for paired frames.
The finite-pair packaging is an agent-written expansion, developed in G4's
`PairedCoreReview.lean` and adapted here to an upstream public interface.
-/

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology

/-- Any prescribed compact cores whose interiors cover an invariant compact set
admit finitely many paired source/receiving cores covering its compact subtype.
This topological form retains the prescribed cores, so every frame-containment
property of those cores remains valid.

Source: the finite-subcover argument in Lee (2003), Proposition 2.24, applied
to the paired frames in HPS (1977), proof of Theorem 5.5, pp. 61–62.
The pairing is an agent-written application: select a finite interior subcover.
Each pair is an intersection of closed inverse images in the compact subtype.
For any point select one core containing it and one containing its image; both
indices belong to the same finite subcover by invariance. Empty sets are allowed.
-/
theorem finite_compact_paired_cores
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (A : Set M) (hA : IsCompact A) (f : M → M)
    (hf : Continuous f) (hfA : MapsTo f A A)
    (K : A → Set M) (hK : ∀ p, IsCompact (K p))
    (hcover : A ⊆ ⋃ p : A, interior (K p)) :
    ∃ t : Finset A,
      (∀ p q : A, IsCompact {x : A | (x : M) ∈ K p ∧ f (x : M) ∈ K q}) ∧
      (Set.univ : Set A) ⊆ ⋃ p ∈ t, ⋃ q ∈ t,
        {x : A | (x : M) ∈ K p ∧ f (x : M) ∈ K q} := by
  classical
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun p ↦ interior (K p))
    (fun _ ↦ isOpen_interior) hcover
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  refine ⟨t, ?_, ?_⟩
  · intro p q
    have hp : IsClosed {x : A | (x : M) ∈ K p} :=
      (hK p).isClosed.preimage continuous_subtype_val
    have hq : IsClosed {x : A | f (x : M) ∈ K q} :=
      (hK q).isClosed.preimage (hf.comp continuous_subtype_val)
    exact (hp.inter hq).isCompact
  · intro x _
    obtain ⟨p, hpt, hp⟩ := mem_iUnion₂.mp (ht x.property)
    obtain ⟨q, hqt, hq⟩ := mem_iUnion₂.mp (ht (hfA x.property))
    exact mem_iUnion₂.mpr ⟨p, hpt, mem_iUnion₂.mpr
      ⟨q, hqt, interior_subset hp, interior_subset hq⟩⟩

/-- Compact tangent-frame cores can be chosen so finitely many paired relative
cores cover an invariant compact set. Each original core remains in its frame.

Source: Lee (2003), Lemma 1.6 and Proposition 2.24; HPS (1977), proof of
Theorem 5.5, pp. 61–62. Choose the canonical compact tangent-frame cores,
then apply `finite_compact_paired_cores` to their interior cover. This uses no
nonemptiness or positive-dimensional hypothesis.
-/
theorem exists_finite_compact_paired_cores
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (A : Set M) (hA : IsCompact A) (f : M → M)
    (hf : Continuous f) (hfA : MapsTo f A A) :
    ∃ (K : A → Set M) (t : Finset A),
      (∀ p, IsCompact (K p) ∧ (p : M) ∈ interior (K p) ∧
        K p ⊆ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M)).baseSet) ∧
      (∀ p q : A, IsCompact {x : A | (x : M) ∈ K p ∧ f (x : M) ∈ K q}) ∧
      (Set.univ : Set A) ⊆ ⋃ p ∈ t, ⋃ q ∈ t,
        {x : A | (x : M) ∈ K p ∧ f (x : M) ∈ K q} := by
  obtain ⟨K, t, hK, hcover⟩ := exists_finite_compact_tangent_frame_cores (E := E) A hA
  have hcover' : A ⊆ ⋃ p : A, interior (K p) := by
    intro x hx
    obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨p, hp⟩
  obtain ⟨s, hs⟩ := finite_compact_paired_cores A hA f hf hfA K (fun p ↦ (hK p).1) hcover'
  exact ⟨K, s, hK, hs⟩

end HolomorphicAnosov.ExponentialCutoff
