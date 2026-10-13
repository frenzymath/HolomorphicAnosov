import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.LinearAlgebra.Projectivization.Action

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
/-- Finite affine projective coordinates never represent infinity.
Source: Ghys §5 p.597. -/
theorem developing_finite_ne_infinity (z : ℂ) :
    complexProjectiveLineFinite z ≠ complexProjectiveLineInfinity := by
  intro h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
  have h₁ := congrArg (fun v : ComplexModel 2 ↦ v 1) hc
  simp [complexProjectiveLineChartVector] at h₁

end HolomorphicAnosov.Ghys
