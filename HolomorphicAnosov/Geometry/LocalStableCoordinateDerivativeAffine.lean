import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Restricted derivatives under affine changes of a transverse coordinate. (Zhang, §2.2, equations (14)–(15)) -/

open scoped Manifold
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- An affine change of transverse function multiplies its restricted scalar derivative by the linear coefficient. (Zhang, equation (15)) -/
theorem localStableCoordinateDerivative_affine (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t : X → ℂ) (x : X) (a b : ℂ)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t x) :
    localStableCoordinateDerivative S (fun y ↦ a * t y + b) x =
      a • localStableCoordinateDerivative S t x := by
  unfold localStableCoordinateDerivative
  change (mvfderiv (I := complexModel d) (fun y ↦ a * t y + b) x).comp (S x).subtypeL = _
  rw [mvfderiv_fun_add (g := fun y ↦ a * t y) (g' := fun _ ↦ b)
    ((mdifferentiableAt_const (c := a)).mul ht) mdifferentiableAt_const]
  rw [mvfderiv_fun_mul (f := fun _ ↦ a) (g := t) mdifferentiableAt_const ht]
  simp only [mvfderiv_const, smul_zero, add_zero, ContinuousLinearMap.smul_comp]
  rfl
end HolomorphicAnosov

