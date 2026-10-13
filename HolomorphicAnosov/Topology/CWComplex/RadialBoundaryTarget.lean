import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialProjection
import HolomorphicAnosov.Topology.CWComplex.RadialBottom
import HolomorphicAnosov.Topology.CWComplex.RadialSide

namespace HolomorphicAnosov

universe u v

/-- The projected point lies on the bottom or the side of the characteristic prism. -/
theorem cw_prism_radial_in_bottom_or_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Metric.closedBall (0 : E) 1 × unitInterval) :
    (cw_prism_radial p).2 = 0 ∨ ‖(cw_prism_radial p).1.val‖ = 1 := by
  let x : E := p.1.val
  let u : ℝ := p.2
  have hu0 : 0 ≤ u := p.2.property.1
  have hu1 : u ≤ 1 := p.2.property.2
  by_cases h : ‖x‖ ≤ (2 - u) / 2
  · left
    have ha : max ‖x‖ ((2 - u) / 2) = (2 - u) / 2 := max_eq_right h
    have hpos : 0 < (2 - u) / 2 := by linarith
    have hne : 2 - u ≠ 0 := by linarith
    have hval : 2 + (u - 2) / ((2 - u) / 2) = 0 := by
      field_simp [hne]
      ring
    apply Subtype.ext
    simpa [cw_prism_radial, x, u, ha] using hval
  · right
    have h' : (2 - u) / 2 ≤ ‖x‖ := le_of_not_ge h
    have ha : max ‖x‖ ((2 - u) / 2) = ‖x‖ := max_eq_left h'
    have hpos : 0 < ‖x‖ := by linarith
    simpa [cw_prism_radial, x, u, ha, norm_smul, Real.norm_eq_abs,
      abs_of_pos hpos] using (inv_mul_cancel₀ hpos.ne')

end HolomorphicAnosov
