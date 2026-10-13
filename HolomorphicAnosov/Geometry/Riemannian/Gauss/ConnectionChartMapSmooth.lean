import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Maximal-atlas charts on the whole-manifold open subtype define smooth coordinate maps on their
sources in the ambient manifold. (Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews,
Lecture 8, Prop. 8.3.1, pp.74–75) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- A maximal-atlas chart on the whole-manifold open subtype defines a smooth coordinate map at each
point of its source in the ambient manifold. (Gallier–Quaintance, Props. 16.7–16.8, pp.451–454) -/
theorem gauss_connectionChartMap_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (connectionChartMap c) p := by
  apply (contMDiffAt_subtype_iff (U := ⊤) (x := ⟨p, mem_univ p⟩)).mp
  exact contMDiffAt_of_mem_maximalAtlas hc hp

end HolomorphicAnosov

