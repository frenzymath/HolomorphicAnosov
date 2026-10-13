import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Equiv

/-!
The universe lift of real coordinate space is linearly homeomorphic to the original space by a norm-preserving map. Its real dimension is unchanged.
-/
noncomputable section
universe u
namespace HolomorphicAnosov.Theorem12LiftedCarrier

/-- The universe lift of the real coordinate space `Fin n → ℝ`. -/
abbrev Carrier (n : ℕ) : Type u := ULift.{u} (Fin n → ℝ)

/-- The norm-preserving real continuous linear equivalence from coordinate space to its universe
lift. -/
def liftEquiv (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] Carrier.{u} n :=
  (ContinuousLinearEquiv.ulift : Carrier.{u} n ≃L[ℝ] (Fin n → ℝ)).symm

/-- `liftEquiv` sends a vector to `ULift.up` of that vector. -/
theorem liftEquiv_apply (n : ℕ) (v : Fin n → ℝ) :
    liftEquiv.{u} n v = ULift.up v := rfl

/-- The inverse of `liftEquiv` sends a lifted vector to its underlying coordinates. -/
theorem liftEquiv_symm_apply (n : ℕ) (v : Carrier.{u} n) :
    (liftEquiv.{u} n).symm v = v.down := rfl

/-- `liftEquiv` preserves the norm. -/
theorem norm_liftEquiv (n : ℕ) (v : Fin n → ℝ) :
    ‖liftEquiv.{u} n v‖ = ‖v‖ := rfl

/-- The lifted coordinate space is finite-dimensional over the reals. -/
theorem carrier_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (Carrier.{u} n) :=
  (liftEquiv.{u} n).toLinearEquiv.finiteDimensional

/-- The lifted coordinate space has real dimension `n`. -/
theorem carrier_finrank (n : ℕ) : Module.finrank ℝ (Carrier.{u} n) = n := by
  rw [← (liftEquiv.{u} n).toLinearEquiv.finrank_eq]
  simp


example (n : ℕ) : NormedAddCommGroup (Carrier.{u} n) := inferInstance
example (n : ℕ) : NormedSpace ℝ (Carrier.{u} n) := inferInstance

end HolomorphicAnosov.Theorem12LiftedCarrier
