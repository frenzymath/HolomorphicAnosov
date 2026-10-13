import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds

namespace HolomorphicAnosov

universe u v

/-- Dividing by Hatcher's radial scale keeps the disk coordinate in the unit ball. -/
theorem cw_prism_radial_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (a : ℝ) (ha : 0 < a) (hx : ‖x‖ ≤ a) :
    ‖a⁻¹ • x‖ ≤ 1 := by
  have h : a⁻¹ * ‖x‖ ≤ 1 := by
    calc
      a⁻¹ * ‖x‖ ≤ a⁻¹ * a :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ha] using h

end HolomorphicAnosov
