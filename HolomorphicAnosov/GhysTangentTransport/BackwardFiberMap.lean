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

/-- The inverse restricted derivative identifies a receiving fibre with the corresponding original fibre. -/
def backwardFiberMap (P : (x : M) → Submodule ℝ (TangentSpace I x)) (y : N) :
    transportedDistribution e P y →ₗ[ℝ] P (e.symm y) where
  toFun w := ((subbundleHomeomorph e ℝ P).symm ⟨y, w⟩).snd
  map_add' := by
    intro v w
    apply Subtype.ext
    exact (mfderiv J I e.symm y).map_add _ _
  map_smul' := by
    intro c w
    apply Subtype.ext
    exact (mfderiv J I e.symm y).map_smul _ _


end
end HolomorphicAnosov.GhysTangentTransport
