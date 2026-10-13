import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- Nonvanishing of a coordinate is independent of the projective representative. (Demailly, §15.A) -/
theorem projective_source_mk (j : Fin 2) (v : ComplexModel 2) (hv : v ≠ 0) :
    complexProjectiveLineMk v hv ∈ complexProjectiveLineChartSource j ↔ v j ≠ 0 := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (Projectivization.mk ℂ v hv).rep j ≠ 0 ↔ v j ≠ 0
  rw [← ht]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero,
    Units.ne_zero, false_or]

