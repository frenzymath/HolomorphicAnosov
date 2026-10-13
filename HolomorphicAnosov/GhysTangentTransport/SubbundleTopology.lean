import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph

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

/-- The topology on the subbundle is the topology induced by its inclusion in the tangent bundle. -/
abbrev subbundleTopology (G : Type*) (P : (x : M) → Submodule ℝ (TangentSpace I x)) :
    TopologicalSpace (Bundle.TotalSpace G (fun x ↦ ↥(P x))) :=
  TopologicalSpace.induced
    (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I M)) inferInstance


end
end HolomorphicAnosov.GhysTangentTransport
