import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimension of the tangent distribution of a native HPS leaf

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, pp.68–72 and 115–116:
the intrinsic leaf immersion identifies its tangent space with the specified distribution.
-/

open scoped ContDiff Manifold
namespace HolomorphicAnosov.HPS
universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable {r : ℕ} {L : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
variable [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]

/-- A native leaf has the rank of its prescribed tangent distribution at every point.

Source: HPS pp.68–72 and 115–116, the immersed intrinsic leaf convention.
The immersion differential is injective and its range is the prescribed distribution.
The range therefore has the dimension of the leaf's real coordinate model, namely `r`.
This includes zero-dimensional leaves and uses no ambient connectedness assumption. -/
theorem NativeLeaf.finrank_tangent
    {D : RealTangentDistribution 𝓘(ℝ, E) M} (N : NativeLeaf (r := r) D L) (z : L) :
    Module.finrank ℝ (D (N.inclusion z)) = r := by
  rw [← N.tangent z, LinearMap.finrank_range_of_inj
    ((N.immersion.isImmersionAt z).mfderiv_injective (by simp))]
  exact Module.finrank_fin_fun ℝ

end HolomorphicAnosov.HPS

