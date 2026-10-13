import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
Reusable TangentHausdorff declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The inherited tangent-bundle topology is Hausdorff when the original base is Hausdorff. Distinct bases are separated by projection, and vectors over the same base by one actual bundle trivialization. -/
lemma tangentBundle_t2Space : T2Space (TangentBundle 𝓘(ℝ, E) M) := by
  apply t2_iff_nhds.mpr
  intro x y h
  let : Filter.NeBot (𝓝 x ⊓ 𝓝 y) := h
  have hp : x.proj = y.proj := tendsto_nhds_unique
    ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.tendsto.mono_left
      inf_le_left)
    ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.tendsto.mono_left
      inf_le_right)
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x.proj
  have hx : x ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have hy : y ∈ e.source := by
    change y.proj ∈ e.baseSet
    rw [← hp]
    exact mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) x.proj
  have heq : e x = e y := tendsto_nhds_unique
    (((e.toOpenPartialHomeomorph.continuousOn x hx).continuousAt
      (e.open_source.mem_nhds hx)).tendsto.mono_left inf_le_left)
    (((e.toOpenPartialHomeomorph.continuousOn y hy).continuousAt
      (e.open_source.mem_nhds hy)).tendsto.mono_left inf_le_right)
  exact e.toOpenPartialHomeomorph.injOn hx hy heq

end
end HolomorphicAnosov
