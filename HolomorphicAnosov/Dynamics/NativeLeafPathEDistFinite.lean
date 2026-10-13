import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPath
import HolomorphicAnosov.Dynamics.NativeLeafPiecewiseSmoothPathExists

/-!
# Finiteness of intrinsic native-leaf path distance

Source: Hirsch--Pugh--Shub (1977), §6B, pp.111–114, together with Lee,
*Introduction to Smooth Manifolds* (2003), Lemma 6.17, pp.139–140: a
connected finite-dimensional smooth manifold is joined by a finite
piecewise-smooth path, and a smooth Riemannian norm has finite length on every
compact path segment.  This public interface records the exact path-distance
fact used by the adapted plaque construction.
-/

noncomputable section
open Set
open scoped ContDiff Manifold ENNReal

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Any two points on a connected native smooth leaf have finite intrinsic
piecewise-smooth path distance for the supplied smooth Riemannian metric. -/
theorem nativeLeafPathEDist_lt_top
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x)
    (y z : L.Carrier) :
    nativeLeafPathEDist 𝓘(ℝ, E) h L y z < ⊤ := by
  obtain ⟨p⟩ := nativeLeaf_piecewiseSmoothPath_exists L y z
  rw [nativeLeafPathEDist, iInf_lt_iff]
  exact ⟨p, ENNReal.ofReal_lt_top⟩

end HolomorphicAnosov
