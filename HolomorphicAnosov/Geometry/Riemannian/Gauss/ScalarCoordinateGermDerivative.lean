import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Directional derivatives of scalar germs are expressed through smooth chart coordinates. -/

open Set IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- A scalar function locally represented as `F ∘ c` has directional derivative given by the Fréchet
derivative of `F` applied to the chart differential. (Gallier–Quaintance, Props. 16.7–16.8,
pp.451–454; Andrews, Prop. 8.3.1 and §8.4, pp.74–75) -/
lemma gauss_scalar_coordinate_germ_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (c : OpenPartialHomeomorph N E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ N)
    (p : N) (hp : p ∈ c.source) (f : N → ℝ) (F : E → ℝ)
    (hF : DifferentiableAt ℝ F (c p)) (he : f =ᶠ[𝓝 p] F ∘ c)
    (v : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) f p v = fderiv ℝ F (c p) (mvfderiv 𝓘(ℝ, E) c p v) := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p v = _
  rw [he.mfderiv_eq]
  have hh := mvfderiv_comp_apply p hF.mdifferentiableAt
    ((contMDiffAt_of_mem_maximalAtlas hc hp).mdifferentiableAt (by simp)) v
  rw [mvfderiv_eq_fderiv] at hh
  exact hh



end HolomorphicAnosov
