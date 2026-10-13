import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction

namespace HolomorphicAnosov

universe u v

/-- Hatcher's radial denominator is uniformly positive on every normed disk prism,
including the native maximum-norm characteristic disks. Source: Hatcher, Proposition 0.16,
p.15, radial projection from `(0,2)`. -/
theorem cw_prism_radial_scale_bounds
    {E : Type*} [NormedAddCommGroup E] (x : E) (u : unitInterval)
    (hx : ‖x‖ ≤ 1) :
    let a : ℝ := max ‖x‖ ((2 - (u : ℝ)) / 2)
    (1 / 2 : ℝ) ≤ a ∧ a ≤ 1 ∧ ‖x‖ ≤ a := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) ≤ 1 := u.property.2
  dsimp
  constructor
  · exact le_trans (by linarith : (1 / 2 : ℝ) ≤ (2 - (u : ℝ)) / 2)
      (le_max_right ..)
  constructor
  · exact max_le hx (by linarith)
  · exact le_max_left ..

end HolomorphicAnosov
