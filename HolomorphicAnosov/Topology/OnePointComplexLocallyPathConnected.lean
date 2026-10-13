import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local path connectivity of the Riemann sphere

This file proves local path connectivity for the native one-point compactification of `ℂ`.
-/

namespace HolomorphicAnosov.Topology

/-- The native one-point compactification of `ℂ` is locally path connected. (Conway II, Lemma 5.4) -/
instance onePointComplex_locallyPathConnectedSpace : LocallyPathConnectedSpace (OnePoint ℂ) := by
  let : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  exact (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3)
    (by simp [Complex.finrank_real_complex])).symm.locallyPathConnectedSpace

end HolomorphicAnosov.Topology

