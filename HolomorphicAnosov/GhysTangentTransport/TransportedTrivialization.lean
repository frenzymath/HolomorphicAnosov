import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TransportedDistribution
import HolomorphicAnosov.GhysTangentTransport.SubbundleHomeomorph
import HolomorphicAnosov.GhysTangentTransport.SubbundleTopology

open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.GhysTangentTransport
noncomputable section
universe u v
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  (e : Diffeomorph I J M N ∞)

attribute [local instance] subbundleTopology

/-- Transport a local trivialization through the derivative homeomorphism over the inverse image of its base domain. -/
def transportedTrivialization (G : Type*) [TopologicalSpace G]
    (P : (x : M) → Submodule ℝ (TangentSpace I x))
    (t : Bundle.Trivialization G (Bundle.TotalSpace.proj (F := G) (E := fun x ↦ ↥(P x)))) :
    Bundle.Trivialization G
      (Bundle.TotalSpace.proj (F := G) (E := fun y ↦ ↥(transportedDistribution e P y))) := by
  let t' := (t.compHomeomorph (subbundleHomeomorph e G P).symm).homeomorphComp e.toHomeomorph
  have hp : (e.toHomeomorph ∘ (Bundle.TotalSpace.proj (F := G) ∘
      (subbundleHomeomorph e G P).symm)) =
      Bundle.TotalSpace.proj (F := G) (E := fun y ↦ ↥(transportedDistribution e P y)) := by
    funext z
    exact e.apply_symm_apply z.proj
  exact {
    toOpenPartialHomeomorph := t'.toOpenPartialHomeomorph
    baseSet := t'.baseSet
    open_baseSet := t'.open_baseSet
    source_eq := by simpa only [hp] using t'.source_eq
    target_eq := t'.target_eq
    proj_toFun := by
      intro z hz
      exact (t'.proj_toFun z hz).trans (e.apply_symm_apply z.proj) }


end
end HolomorphicAnosov.GhysTangentTransport
