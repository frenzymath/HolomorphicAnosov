import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.LinearAlgebra.Projectivization.Action

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
/-- A projective point outside the finite chart source is infinity.
Source: Ghys §5 p.597 and Demailly V §15.A p.277. -/
theorem developing_eq_infinity_of_not_finite_source (p : ComplexProjectiveLine)
    (hp : p ∉ complexProjectiveLineChartSource 1) : p = complexProjectiveLineInfinity := by
  have hp₁ : p.rep 1 = 0 := not_not.mp hp
  have hp₀ : p.rep 0 ≠ 0 := by
    intro h
    apply p.rep_nonzero
    funext i
    fin_cases i <;> simp [h, hp₁]
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
  refine ⟨Units.mk0 (p.rep 0) hp₀, ?_⟩
  funext i
  fin_cases i <;> simp [complexProjectiveLineChartVector, Units.smul_def, hp₁]

end HolomorphicAnosov.Ghys
