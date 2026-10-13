import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- An open tangent-bundle set containing the zero section over a compact set contains
a uniform positive-radius metric tube over a neighborhood of that set.
(Hirsch–Pugh–Shub, p. 62) -/
theorem compact_metric_tube
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {Ω : Set (TangentBundle 𝓘(ℝ, E) M)} (hΩ : IsOpen Ω)
    (A : Set M) (hA : IsCompact A)
    (hzero : ∀ p ∈ A, (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ Ω) :
    ∃ (U : Opens M) (ε : ℝ), A ⊆ U ∧ 0 < ε ∧ normalTube g U ε ⊆ Ω := by
  classical
  choose U ε hpU hε hU using fun p : A ↦ local_metric_tube g hΩ p (hzero p p.property)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun p : A ↦ (U p : Set M))
    (fun p ↦ (U p).isOpen) (fun p hp ↦ mem_iUnion.mpr ⟨⟨p, hp⟩, hpU ⟨p, hp⟩⟩)
  have hmin : ∀ t : Finset A, ∃ δ > 0, ∀ p ∈ t, δ ≤ ε p := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert p t hpt ih =>
      obtain ⟨δ, hδ, hδt⟩ := ih
      refine ⟨min (ε p) δ, lt_min (hε p) hδ, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδt q hq)
  obtain ⟨δ, hδ, hδt⟩ := hmin t
  refine ⟨⟨⋃ p ∈ t, (U p : Set M), isOpen_biUnion fun p _ ↦ (U p).isOpen⟩,
    δ, ht, hδ, ?_⟩
  intro z hz
  obtain ⟨p, hp, hzU⟩ := mem_iUnion₂.mp hz.1
  exact hU p ⟨hzU, hz.2.trans_le (hδt p hp)⟩


end ExponentialLift
end HolomorphicAnosov
