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
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Coordinate vectors in two charts are related by the derivative of their transition map. (Andrews, §8.3) -/
theorem chartVector_transition (U : Opens M)
    (c d : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (hd : d ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (p : U) (hp : p ∈ c.source) (hpd : p ∈ d.source)
    (v : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) d p v =
      fderiv ℝ (d ∘ c.symm) (c p) (mvfderiv 𝓘(ℝ, E) c p v) := by
  have hh : ContDiffAt ℝ ∞ (d ∘ c.symm) (c p) :=
    ((contMDiffAt_of_mem_maximalAtlas hd hpd).comp_of_eq
      (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hp)) (c.left_inv hp)).contDiffAt
  have heq : ((d ∘ c.symm) ∘ c) =ᶠ[𝓝 p] d := by
    filter_upwards [c.open_source.mem_nhds hp] with q hq
    simp only [Function.comp_apply, c.left_inv hq]
  have hchain := mfderiv_comp_apply p
    (hh.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiffAt_of_mem_maximalAtlas hc hp).mdifferentiableAt (by simp)) v
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hchain
  exact hchain

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
