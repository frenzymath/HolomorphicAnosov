import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.GhysTangentTransport.TransportedTrivialization
import HolomorphicAnosov.GhysTangentTransport.BackwardFiberMap
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

/-- The transported local frame is linear on every fibre in its domain. -/
theorem transportedTrivialization_linear (G : Type*) [TopologicalSpace G]
    [AddCommMonoid G] [Module ℝ G]
    (P : (x : M) → Submodule ℝ (TangentSpace I x))
    (t : Bundle.Trivialization G (Bundle.TotalSpace.proj (F := G) (E := fun x ↦ ↥(P x))))
    [t.IsLinear ℝ] : (transportedTrivialization e G P t).IsLinear ℝ := by
  constructor
  intro y hy
  change e.symm y ∈ t.baseSet at hy
  have ht := t.linear ℝ hy
  constructor
  · intro v w
    change (t ⟨e.symm y, backwardFiberMap e P y (v+w)⟩).2 =
      (t ⟨e.symm y, backwardFiberMap e P y v⟩).2 +
      (t ⟨e.symm y, backwardFiberMap e P y w⟩).2
    rw [map_add]
    exact ht.map_add _ _
  · intro c w
    change (t ⟨e.symm y, backwardFiberMap e P y (c • w)⟩).2 =
      c • (t ⟨e.symm y, backwardFiberMap e P y w⟩).2
    rw [map_smul]
    exact ht.map_smul _ _


end
end HolomorphicAnosov.GhysTangentTransport
