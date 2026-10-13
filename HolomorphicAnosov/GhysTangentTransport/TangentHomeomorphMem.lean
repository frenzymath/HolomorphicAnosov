import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TangentEquiv
import HolomorphicAnosov.GhysTangentTransport.TransportedDistribution
import HolomorphicAnosov.GhysTangentTransport.TangentHomeomorph

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

set_option backward.isDefEq.respectTransparency false in
/-- The tangent equivalence maps each original fibre subspace exactly to its transported subspace. -/
theorem tangentHomeomorph_mem (P : (x : M) → Submodule ℝ (TangentSpace I x))
    (z : TangentBundle I M) :
    z.snd ∈ P z.proj ↔
      (tangentHomeomorph e z).snd ∈
        transportedDistribution e P (tangentHomeomorph e z).proj := by
  rcases z with ⟨x, v⟩
  change v ∈ P x ↔ mfderiv I J e x v ∈
    (P (e.symm (e x))).map (tangentEquiv e (e.symm (e x))).toLinearEquiv.toLinearMap
  rw [e.symm_apply_apply]
  constructor
  · intro hv
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  · intro hv
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp hv
    have heq' : tangentEquiv e x w = tangentEquiv e x v := heq
    exact (tangentEquiv e x).injective heq' ▸ hw


end
end HolomorphicAnosov.GhysTangentTransport
