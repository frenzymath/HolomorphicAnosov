import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveRightInv
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveFunMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveOtherNe

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The transition between the two normalized charts is the identity or reciprocal map. (Demailly, §15.A) -/
theorem projective_transition (j k : Fin 2) (z : ComplexModel 1) :
    complexProjectiveLineChartFun k (complexProjectiveLineChartInv j z) =
      if j = k then z else (fun _ ↦ (z 0)⁻¹) := by
  by_cases h : j = k
  · subst k
    rw [projective_right_inv, ite_eq_left rfl]
  · rw [ite_eq_right h, complexProjectiveLineChartInv, projective_fun_mk]
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    fin_cases j <;> fin_cases k <;> simp_all [complexProjectiveLineChartVector]

