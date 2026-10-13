import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound

namespace HolomorphicAnosov

universe u v

/-- Hatcher's radial projection, directly on a normed characteristic disk. -/
noncomputable def cw_prism_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Metric.closedBall (0 : E) 1 × unitInterval) :
    Metric.closedBall (0 : E) 1 × unitInterval := by
  let x : E := p.1.val
  let u : ℝ := p.2
  let a : ℝ := max ‖x‖ ((2 - u) / 2)
  have hx : ‖x‖ ≤ 1 := by
    simpa only [x, Metric.mem_closedBall, dist_zero_right] using p.1.property
  have hb := cw_prism_radial_scale_bounds x p.2 hx
  have ha0 : (1 / 2 : ℝ) ≤ a := hb.1
  have ha1 : a ≤ 1 := hb.2.1
  have hax : ‖x‖ ≤ a := hb.2.2
  have ha : (2 - u) / 2 ≤ a := le_max_right ..
  have hnorm : ‖a⁻¹ • x‖ ≤ 1 :=
    cw_prism_radial_norm_bound x a (by linarith) hax
  have hu : 0 ≤ 2 + (u - 2) / a ∧ 2 + (u - 2) / a ≤ 1 := by
    have hbounds := cw_prism_radial_height_bounds u a p.2.property.2 ha0 ha1 ha
    exact ⟨hbounds.1, hbounds.2.trans p.2.property.2⟩
  exact (⟨a⁻¹ • x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩,
    ⟨2 + (u - 2) / a, hu⟩)

end HolomorphicAnosov
