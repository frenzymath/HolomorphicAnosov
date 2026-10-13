import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection

namespace HolomorphicAnosov

universe u v

/-- The local prism radial projection is jointly continuous in its disk and time coordinates. -/
theorem continuous_cw_prism_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (cw_prism_radial (E := E)) := by
  let D := Metric.closedBall (0 : E) 1
  let a : D × unitInterval → ℝ :=
    fun p ↦ max ‖p.1.val‖ ((2 - (p.2 : ℝ)) / 2)
  have hx : Continuous (fun p : D × unitInterval ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun p : D × unitInterval ↦ (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have ha : Continuous a := (continuous_norm.comp hx).max
    ((continuous_const.sub hu).div_const 2)
  have ha0 (p : D × unitInterval) : a p ≠ 0 := by
    have hp : ‖p.1.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (show p.1.val ∈ Metric.closedBall (0 : E) 1 from p.1.property)
    have hb := (cw_prism_radial_scale_bounds p.1.val p.2 hp).1
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb)
  have hi : Continuous (fun p : D × unitInterval ↦ (a p)⁻¹) := ha.inv₀ ha0
  have hc1 : Continuous (fun p : D × unitInterval ↦ (a p)⁻¹ • p.1.val) :=
    hi.smul hx
  have hc2 : Continuous (fun p : D × unitInterval ↦
      2 + ((p.2 : ℝ) - 2) / a p) := by
    have hc2a : Continuous (fun p : D × unitInterval ↦
        (2 : ℝ) + ((p.2 : ℝ) - 2) * (a p)⁻¹) :=
      (continuous_const (y := (2 : ℝ))).add
        ((hu.sub (continuous_const (y := (2 : ℝ)))).mul hi)
    simpa only [div_eq_mul_inv] using hc2a
  have hc1' : Continuous (fun p : D × unitInterval ↦ (cw_prism_radial p).1) := by
    convert hc1.subtype_mk (fun p ↦ (cw_prism_radial p).1.property) using 1
    funext p
    apply Subtype.ext
    rfl
  have hc2' : Continuous (fun p : D × unitInterval ↦ (cw_prism_radial p).2) := by
    convert hc2.subtype_mk (fun p ↦ (cw_prism_radial p).2.property) using 1
    funext p
    apply Subtype.ext
    rfl
  exact hc1'.prodMk hc2'

end HolomorphicAnosov
