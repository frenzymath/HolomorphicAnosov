import HolomorphicAnosov.Geometry.InverseDerivative
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle
attribute [local instance] complex_isManifold_real
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]

/-- The canonical inverse of the genuine derivative equivalence agrees with the derivative of the original inverse, including its equal-point endpoint cast (the same inverse-map application in Ghys pp.589–590).-/
theorem derivative_equiv_symm_apply
    (g : Diffeomorph (realModel d) (realModel d) X X ∞) (x : X)
    (v : TangentSpace (realModel d) (g (g.symm x))) :
    (g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)).symm v =
      mfderiv (realModel d) (realModel d) g.symm x
        (tangentSpaceCast (realModel d) (g (g.symm x)) x v) := by
  let Q := g.mfderivToContinuousLinearEquiv (by simp) (g.symm x)
  obtain ⟨w, rfl⟩ := Q.surjective v
  have h := congrArg (fun L ↦ L w) (inverse_derivative_comp g x)
  change mfderiv (realModel d) (realModel d) g.symm x
    (tangentSpaceCast (realModel d) (g (g.symm x)) x (Q w)) = w at h
  change Q.symm (Q w) = _
  rw [Q.symm_apply_apply]
  exact h.symm

end HolomorphicAnosov
