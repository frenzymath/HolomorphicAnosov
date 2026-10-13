import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Fixed points of complex projective special linear transformations on the homogeneous projective
line. (Ghys, Thm A, case (i), p. 600) -/

namespace HolomorphicAnosov

open scoped MatrixGroups

/-- Every element of `PSL(2, ℂ)` has a fixed point on the complex projective line. (Ghys, Thm A,
case (i), p. 600) -/
theorem surface_mobius_fixed_point (g : PSL(2, ℂ)) :
    ∃ z : ComplexProjectiveLine, g • z = z := by
  refine QuotientGroup.induction_on g ?_
  intro A
  obtain ⟨eigenvalue, heigenvalue⟩ := Module.End.exists_eigenvalue
    (A.toLin' : Module.End ℂ (ComplexModel 2))
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A.toLin' v = eigenvalue • v := hv.apply_eq_smul
  have hAv0 : A.toLin' v ≠ 0 := by
    intro h
    apply hv0
    apply A.toLin'.injective
    simpa using h
  let p : ComplexProjectiveLine := Projectivization.mk ℂ v hv0
  refine ⟨p, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ (A.toLin' v) v hAv0 hv0).2
  exact ⟨eigenvalue, hAv.symm⟩

end HolomorphicAnosov
