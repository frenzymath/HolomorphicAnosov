import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoefficientSmoothness
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChartAtlas
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

/-!
Smoothness of Christoffel coefficients in chart coordinates. (Andrews, Prop. 8.3.1, p.74)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The Christoffel coefficients are smooth on the target of an admissible chart. (Andrews, Prop.
8.3.1, p.74) -/
theorem connectionChristoffel_contDiffOn (nabla : SmoothAffineConnection E M)
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M)) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun x : E ↦ connectionChristoffel nabla b c hc i j k (c.symm x))
      c.target := by
  have hs := ConnectionChristoffelLocal.extendedLocalChristoffel_contMDiffOn nabla b
    (ConnectionChristoffelLocal.wholeChart c)
    (ConnectionChristoffelLocal.wholeChart_mem_maximalAtlas c hc) i j k
  have hcomp := hs.comp
    (contMDiffOn_symm_of_mem_maximalAtlas
      (ConnectionChristoffelLocal.wholeChart_mem_maximalAtlas c hc))
    (ConnectionChristoffelLocal.wholeChart c).symm.mapsTo
  simpa [connectionChristoffel, ConnectionChristoffelLocal.wholeChart, Function.comp_def] using hcomp.contDiffOn
end
end HolomorphicAnosov

