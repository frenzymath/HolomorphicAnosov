import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveOtherNe

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- On an overlap of distinct charts, the relevant denominator is nonzero. (Demailly, §15.A) -/
theorem projective_overlap_ne (j k : Fin 2) (hjk : j ≠ k) (z : ComplexModel 1)
    (hz : complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource k) : z 0 ≠ 0 := by
  rw [complexProjectiveLineChartInv, projective_source_mk] at hz
  fin_cases j <;> fin_cases k <;> simp_all [complexProjectiveLineChartVector]

