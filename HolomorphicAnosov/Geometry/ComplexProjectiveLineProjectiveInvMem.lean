import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceMk

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The normalized representative lies in the corresponding homogeneous-coordinate source. (Demailly, §15.A) -/
theorem projective_inv_mem (j : Fin 2) (z : ComplexModel 1) :
    complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource j := by
  rw [complexProjectiveLineChartInv, projective_source_mk]
  simp [complexProjectiveLineChartVector]

