import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
/-- Restricting a maximal-atlas chart to an open subtype gives a maximal-atlas chart. (Andrews, §8.3) -/
theorem maximalAtlas_subtypeRestr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (U : Opens M) (hU : Nonempty U) :
    c.subtypeRestr hU ∈ maximalAtlas 𝓘(ℝ, E) ∞ U := by
  let G := contDiffGroupoid ∞ 𝓘(ℝ, E)
  intro e' he'
  obtain ⟨x, hx⟩ := Opens.chart_eq hU he'
  rw [hx]
  have hcx := G.compatible_of_mem_maximalAtlas hc (G.subset_maximalAtlas (chart_mem_atlas E (x : M)))
  have hxc := G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas (chart_mem_atlas E (x : M))) hc
  exact ⟨G.mem_of_eqOnSource (closedUnderRestriction' hcx
      (c.isOpen_inter_preimage_symm U.2))
      (c.subtypeRestr_symm_trans_subtypeRestr hU (chartAt E (x : M))),
    G.mem_of_eqOnSource (closedUnderRestriction' hxc
      ((chartAt E (x : M)).isOpen_inter_preimage_symm U.2))
      ((chartAt E (x : M)).subtypeRestr_symm_trans_subtypeRestr hU c)⟩

end
end HolomorphicAnosov
