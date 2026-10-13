import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube

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

/-- Over a neighborhood of a compact set, the Riemannian exponential addition is defined, injective,
and a local diffeomorphism on a metric tube of uniform positive radius. (HPS, p. 62) -/
theorem uniform_inverse_tube
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) :
    ∃ (U : Opens M) (ρ : ℝ), A ⊆ U ∧ 0 < ρ ∧
      normalTube g U ρ ⊆ riemannianExpDomain g ∧
      InjOn (riemannianExponentialAddition g) (normalTube g U ρ) ∧
      IsLocalDiffeomorphOn (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) ∞
        (riemannianExponentialAddition g) (normalTube g U ρ) := by
  classical
  have hexp := (riemannian_exponential_local_addition g).2.2.2.2.2
  choose e he0 heD hetarget heeq heinv using fun p : A ↦ hexp (p : M)
  choose U ε hpU hε hU using fun p : A ↦
    local_metric_tube g (e p).open_source p (he0 p)
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
  obtain ⟨ρ, hρ, hρt⟩ := hmin t
  let V : Opens M := ⟨⋃ p ∈ t, (U p : Set M),
    isOpen_biUnion fun p _ ↦ (U p).isOpen⟩
  have hchart : ∀ z ∈ normalTube g V ρ, ∃ p ∈ t, z ∈ (e p).source := by
    intro z hz
    obtain ⟨p, hp, hzU⟩ := mem_iUnion₂.mp hz.1
    exact ⟨p, hp, hU p ⟨hzU, hz.2.trans_le (hρt p hp)⟩⟩
  refine ⟨V, ρ, ht, hρ, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hze⟩ := hchart z hz
    exact heD p hze
  · intro z hz z' hz' hequal
    have hbase : z.proj = z'.proj := congrArg Prod.fst hequal
    obtain ⟨p, hp, hzU⟩ := mem_iUnion₂.mp hz.1
    have hze := hU p ⟨hzU, hz.2.trans_le (hρt p hp)⟩
    have hz'e := hU p ⟨hbase ▸ hzU, hz'.2.trans_le (hρt p hp)⟩
    apply (e p).toOpenPartialHomeomorph.injOn hze hz'e
    exact (heeq p hze).trans (hequal.trans (heeq p hz'e).symm)
  · intro z
    obtain ⟨p, hp, hze⟩ := hchart z z.property
    exact ⟨e p, hze, (heeq p).symm⟩


end ExponentialLift
end HolomorphicAnosov
