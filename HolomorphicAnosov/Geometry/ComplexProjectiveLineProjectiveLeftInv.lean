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


/-- Dividing a representative by its pivot preserves its projective class. (Demailly, §15.A) -/
theorem projective_left_inv (j : Fin 2) (p : ComplexProjectiveLine)
    (hp : p ∈ complexProjectiveLineChartSource j) :
    complexProjectiveLineChartInv j (complexProjectiveLineChartFun j p) = p := by
  have hp' : p.rep j ≠ 0 := hp
  change Projectivization.mk ℂ
    (complexProjectiveLineChartVector j (complexProjectiveLineChartFun j p)) _ = p
  calc
    _ = Projectivization.mk ℂ p.rep p.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(p.rep j)⁻¹, ?_⟩
      ext i
      by_cases hi : i = j
      · subst i
        simp [complexProjectiveLineChartVector, Pi.smul_apply, smul_eq_mul, hp']
      · have hi' : i = j + 1 := by fin_cases j <;> fin_cases i <;> simp_all
        rw [hi']
        simp only [Pi.smul_apply, smul_eq_mul, complexProjectiveLineChartVector,
          ite_eq_right (projective_other_ne j), complexProjectiveLineChartFun]
        exact mul_comm _ _
    _ = p := Projectivization.mk_rep p

