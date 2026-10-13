import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Dynamics.Linear.ComplexHyperbolicity
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import Mathlib.Logic.Function.Conjugate

/-! Biholomorphic conjugacy to hyperbolic complex torus automorphisms. (Zhang, Theorem A, p. 2,
Theorem 1.2, pp. 11–13) -/

namespace HolomorphicAnosov

universe u

/-- A map has a hyperbolic complex torus model if it is biholomorphically conjugate to the quotient
of a lattice-preserving complex-linear equivalence with no eigenvalue on the unit circle.
(Zhang, Theorem A, p. 2, Theorem 1.2, pp. 11–13) -/
def HasHyperbolicComplexTorusModel {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (f : X → X) : Prop :=
  ∃ (L : FullComplexLattice d) (A : LatticeLinearEquiv L)
    (h : Biholomorph d d X (ComplexTorus L)),
    ComplexLinearHyperbolic A.linear.toLinearMap ∧
      Function.Semiconj (fun x ↦ h x) f (fun t ↦ quotientLinearEquiv A t)

end HolomorphicAnosov
