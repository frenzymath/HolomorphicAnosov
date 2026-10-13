import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Restricting chart domains leaves their transition germ unchanged near the evaluation point. (Andrews, Exercise 8.3.2) -/
theorem restricted_transition_germ (U : Opens M) (hU : Nonempty U)
    (c d : OpenPartialHomeomorph M E) (p : U) (hp : (p : M) ∈ c.source) :
    ((c.subtypeRestr hU).symm |> fun inv ↦ (d.subtypeRestr hU) ∘ inv) =ᶠ[𝓝 (c p)]
      (d ∘ c.symm) := by
  have hpc : p ∈ (c.subtypeRestr hU).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp
  filter_upwards [(c.subtypeRestr hU).open_target.mem_nhds
    ((c.subtypeRestr hU).map_source hpc)] with z hz
  exact congrArg d (c.subtypeRestr_symm_apply hU hz)

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
