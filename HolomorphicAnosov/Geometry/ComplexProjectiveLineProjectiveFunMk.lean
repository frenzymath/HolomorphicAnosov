import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- For a nonzero homogeneous representative, the coordinate ratio equals the projective chart value. (Demailly, §15.A) -/
theorem projective_fun_mk (j : Fin 2) (v : ComplexModel 2) (hv : v ≠ 0) :
    complexProjectiveLineChartFun j (complexProjectiveLineMk v hv) =
      fun _ ↦ v (j + 1) / v j := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold complexProjectiveLineChartFun complexProjectiveLineMk
  rw [← ht]
  ext k
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ (Units.ne_zero t)

