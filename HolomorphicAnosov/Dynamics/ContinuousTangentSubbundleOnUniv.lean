import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle

open Set
open scoped ContDiff Manifold

namespace HolomorphicAnosov
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Restrict an ambient continuous tangent subbundle to the full-set subtype.

Agent-written packaging step for the full-manifold application of Hirsch–Pugh
Fact One. The total spaces are homeomorphic by forgetting the proof of membership
in `univ`, since both topologies are induced by the same tangent inclusion.
Transport each original local trivialization through this homeomorphism and the
base homeomorphism. The fibre map is unchanged, hence remains linear. No rank
positivity or nonemptiness is needed. -/
theorem continuousRealTangentSubbundle_on_univ (s : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M) :
    ∃ t : ContinuousTangentSubbundleOn (E := E) (Set.univ : Set M),
      ∀ x, t.fibre x = s.toDistribution x := by
  refine ⟨{ fibre := fun x ↦ s.toDistribution x, locally_trivial := ?_ }, fun _ ↦ rfl⟩
  intro x
  obtain ⟨r, e, hx, he⟩ := s.locally_trivial x
  refine ⟨r, ?_⟩
  let full := Bundle.TotalSpace (Fin r → ℝ) (fun y : M ↦ ↥(s.toDistribution y))
  let restricted := Bundle.TotalSpace (Fin r → ℝ)
    (fun y : (Set.univ : Set M) ↦ ↥(s.toDistribution (y : M)))
  let : TopologicalSpace full := TopologicalSpace.induced
    (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  let : TopologicalSpace restricted := TopologicalSpace.induced
    (fun z ↦ (⟨(z.proj : M), z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  let H : restricted ≃ₜ full :=
    { toFun := fun z ↦ ⟨z.proj.val, z.snd⟩
      invFun := fun z ↦ ⟨⟨z.proj, Set.mem_univ _⟩, z.snd⟩
      left_inv := by intro z; cases z; rfl
      right_inv := by intro z; cases z; rfl
      continuous_toFun := by exact continuous_induced_rng.mpr continuous_induced_dom
      continuous_invFun := by exact continuous_induced_rng.mpr continuous_induced_dom }
  let B : M ≃ₜ (Set.univ : Set M) :=
    { toFun := fun y ↦ ⟨y, Set.mem_univ _⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let t := (e.compHomeomorph H).homeomorphComp B
  refine ⟨t, hx, ?_⟩
  constructor
  intro y hy
  exact he.linear y.val hy
end HolomorphicAnosov
