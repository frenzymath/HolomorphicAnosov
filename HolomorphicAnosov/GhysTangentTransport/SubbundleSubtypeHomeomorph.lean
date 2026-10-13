import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
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

/-- This homeomorphism identifies the tangent subbundle with its ambient subtype. -/
def subbundleSubtypeHomeomorph (G : Type*) (P : (x : M) → Submodule ℝ (TangentSpace I x)) :
    Bundle.TotalSpace G (fun x ↦ ↥(P x)) ≃ₜ
      {z : TangentBundle I M // z.snd ∈ P z.proj} where
  toFun z := ⟨⟨z.proj, z.snd.val⟩, z.snd.property⟩
  invFun z := ⟨z.val.proj, ⟨z.val.snd, z.property⟩⟩
  left_inv := by intro z; cases z; rfl
  right_inv := by intro z; cases z; rfl
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val


end
end HolomorphicAnosov.GhysTangentTransport
