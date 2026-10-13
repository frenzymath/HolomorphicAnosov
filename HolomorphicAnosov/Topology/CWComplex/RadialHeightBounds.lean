import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds

namespace HolomorphicAnosov

universe u v

/-- The radial projection stays below the original prism height and above the bottom. -/
theorem cw_prism_radial_height_bounds
    (u a : ℝ) (hu1 : u ≤ 1)
    (ha0 : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1)
    (ha : (2 - u) / 2 ≤ a) :
    0 ≤ 2 + (u - 2) / a ∧ 2 + (u - 2) / a ≤ u := by
  have hapos : 0 < a := by linarith
  have hsmall : (2 - u) / a ≤ 2 :=
    (div_le_iff₀ hapos).2 (by linarith)
  have hlarge : 2 - u ≤ (2 - u) / a := by
    apply (le_div_iff₀ hapos).2
    nlinarith [mul_nonneg (show 0 ≤ 2 - u by linarith) (sub_nonneg.mpr ha1)]
  have heq : (u - 2) / a = -((2 - u) / a) := by ring
  constructor <;> rw [heq] <;> linarith

end HolomorphicAnosov
