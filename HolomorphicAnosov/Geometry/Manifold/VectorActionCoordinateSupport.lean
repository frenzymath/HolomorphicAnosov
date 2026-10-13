import HolomorphicAnosov.Analysis.Regularity.MontgomeryParameterDerivativeDenseJointContinuity
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Algebra.MulAction

namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped Topology _root_.Topology ContDiff

variable {V E M : Type*} [NormedAddCommGroup V]
  [NormedAddCommGroup E] [TopologicalSpace M]
  [AddAction V M] [ContinuousVAdd V M]

/-- Joint action continuity provides common positive parameter and spatial radii on which both chart guards hold (Montgomery, Lemmas 1 and 3, pp.383–386). -/
theorem exists_action_coordinate_product
    (e f : OpenPartialHomeomorph M E) (v : V) (y : E)
    (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source) :
    ∃ r > 0, ∀ w ∈ Metric.ball v r, ∀ z ∈ Metric.ball y r,
      z ∈ e.target ∧ w +ᵥ e.symm z ∈ f.source := by
  have hc : ContinuousAt (fun p : V × E ↦ p.1 +ᵥ e.symm p.2) (v, y) :=
    continuousAt_fst.vadd ((e.symm.continuousAt hy).comp continuousAt_snd)
  have he : ∀ᶠ p : V × E in 𝓝 (v, y), p.2 ∈ e.target :=
    continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds hy)
  have hf : ∀ᶠ p : V × E in 𝓝 (v, y), p.1 +ᵥ e.symm p.2 ∈ f.source :=
    hc.preimage_mem_nhds (f.open_source.mem_nhds hvy)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (he.and hf)
  refine ⟨r, hr, ?_⟩
  intro w hw z hz
  exact hball (y := (w, z))
    (by simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hw hz)

/-- Fixed action slices are smooth in every pair of compatible charts on their actual guarded domain (Montgomery, pp.383–386). -/
theorem action_coordinate_contDiffAt
    {V E M : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [AddAction V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (v : V) (y : E) (hy : y ∈ e.target) (hvy : v +ᵥ e.symm y ∈ f.source) :
    ContDiffAt ℝ ∞ (fun z : E ↦ f (v +ᵥ e.symm z)) y := by
  have h := ((contMDiffAt_iff_of_mem_maximalAtlas he hf (e.map_target hy) hvy).mp
    (hsmooth v (e.symm y))).2
  simpa [OpenPartialHomeomorph.extend, Function.comp_def, e.right_inv hy,
    contDiffWithinAt_univ] using h


end HolomorphicAnosov.VectorActionSpatialSupport

