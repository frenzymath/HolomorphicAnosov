import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_frame
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_centered_frame_domain
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_radius
import HolomorphicAnosov.Geometry.UniformExponentialLift.vertical_jet_restriction
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_vertical_jets

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A `C^r` map on an open domain with a manifold parameter has jointly continuous
vertical jets through order `r`. (Hirsch–Pugh–Shub, p. 62) -/
theorem continuousOn_manifold_vertical_jets
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Q : M × E → G) (D : Set (M × E)) (hD : IsOpen D)
    (r : ℕ∞) (hQ : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ, G) r Q D)
    (j : ℕ) (hj : (j : ℕ∞) ≤ r) :
    ContinuousOn (fun z : M × E ↦ iteratedFDeriv ℝ j (fun u ↦ Q (z.1, u)) z.2) D := by
  intro z hz
  let c := (chartAt E z.1).prod (OpenPartialHomeomorph.refl E)
  let D₀ : Set (M × E) := D ∩ c.source
  let D₁ : Set (E × E) := c '' D₀
  let Q₁ : E × E → G := fun w ↦ Q ((chartAt E z.1).symm w.1, w.2)
  have hD₀ : IsOpen D₀ := hD.inter c.open_source
  have hD₁ : IsOpen D₁ := c.isOpen_image_of_subset_source hD₀ inter_subset_right
  have hcoords := (contMDiffOn_iff_of_subset_source
    (x := (z.1, (0 : E))) (y := (0 : G))
    (show D₀ ⊆ (chartAt (ModelProd E E) (z.1, (0 : E))).source from by
      simp [D₀, c, prodChartedSpace_chartAt, chartAt_self_eq])
    (show MapsTo Q D₀ (chartAt G (0 : G)).source from by simp [chartAt_self_eq])).mp
      (hQ.mono inter_subset_left)
  have hQ₁ : ContDiffOn ℝ r Q₁ D₁ := by
    simpa only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.prod_coe,
      PartialEquiv.prod_coe_symm, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      PartialEquiv.refl_coe, PartialEquiv.refl_symm, Function.comp_def, id_eq, c, D₁, Q₁,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply] using hcoords.2
  have hz₀ : z ∈ D₀ := ⟨hz, by simp [c, mem_chart_source]⟩
  have hj' : (j : ℕ∞ω) ≤ (r : ℕ∞ω) := WithTop.coe_le_coe.mpr hj
  have hjet := continuousOn_vertical_jets Q₁ D₁ hD₁ r hQ₁ j hj'
  have hcont : ContinuousAt
      (fun w : E × E ↦ iteratedFDeriv ℝ j (fun u ↦ Q₁ (w.1, u)) w.2) (c z) :=
    (hjet (c z) ⟨z, hz₀, rfl⟩).continuousAt (hD₁.mem_nhds ⟨z, hz₀, rfl⟩)
  have hc : ContinuousAt c z := c.continuousAt hz₀.2
  have heq : (fun w : M × E ↦ iteratedFDeriv ℝ j (fun u ↦ Q (w.1, u)) w.2)
      =ᶠ[𝓝 z] (fun w : M × E ↦
        iteratedFDeriv ℝ j (fun u ↦ Q₁ ((c w).1, u)) (c w).2) := by
    filter_upwards [c.open_source.mem_nhds hz₀.2] with w hw
    have hw' : w.1 ∈ (chartAt E z.1).source := hw.1
    simp only [Q₁, c, OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    rw [(chartAt E z.1).left_inv hw']
    rfl
  exact ((hcont.comp hc).congr_of_eventuallyEq heq).continuousWithinAt


end ExponentialLift
end HolomorphicAnosov
