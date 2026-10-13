import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


/-- The positively oriented unit circle, regarded as a complex-valued loop. -/
def unitCircleLoop : ComplexLoop :=
  { toFun := fun z => (z : ℂ), continuous_toFun := continuous_subtype_val }

/-- A constant complex-valued circle loop. -/
def constantLoop (c : ℂ) : ComplexLoop :=
  { toFun := fun _ => c, continuous_toFun := continuous_const }

/-- The counterclockwise boundary trace of a continuous closed-disk function. -/
def diskBoundaryLoop (a : ℂ) (r : ℝ) (f : ℂ → ℂ) (hr : 0 < r)
    (hf : ContinuousOn f (Metric.closedBall a r)) : ComplexLoop :=
  { toFun := fun z => f (a + r * (z : ℂ))
    continuous_toFun := by
      apply hf.comp_continuous (continuous_const.add (continuous_const.mul continuous_subtype_val))
      intro z
      change a + (r : ℂ) * (z : ℂ) ∈ Metric.closedBall a r
      rw [Metric.mem_closedBall]
      simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr, Circle.norm_coe (show Circle from z)] }

/-- A free continuous homotopy of circle loops avoiding the marked point. -/
def LoopHomotopyAvoids (γ₀ γ₁ : ComplexLoop) (b : ℂ) : Prop :=
  ∃ H : C(↑unitInterval × Circle, ℂ),
    (∀ z, H (0, z) = γ₀ z) ∧ (∀ z, H (1, z) = γ₁ z) ∧
      ∀ t z, H (t, z) ≠ b

/-- A path of omitted values, in the complement of the original loop image. -/
def OmittedValuePath (γ : ComplexLoop) (b₀ b₁ : ℂ) : Prop :=
  ∃ p : Path b₀ b₁, ∀ t z, p t ≠ γ z

end
end HolomorphicAnosov
