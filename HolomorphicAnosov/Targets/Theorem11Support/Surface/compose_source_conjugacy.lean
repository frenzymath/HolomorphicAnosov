import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

/-!
Composition of a complex torus conjugacy with quotient coordinates gives a real toral conjugacy.
-/

noncomputable section

namespace HolomorphicAnosov.Surface11SupportW06

universe u

/-- The composition of the source biholomorphism and the quotient homeomorphism intertwines `f` with
the integral toral map. (Zhang, Theorem 1.1) -/
theorem compose_source_conjugacy {d n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (f : X → X) (L : FullComplexLattice d) (B : LatticeLinearEquiv L)
    (c : Biholomorph d d X (ComplexTorus L))
    (hc : Function.Semiconj (fun x ↦ c x) f (fun z ↦ quotientLinearEquiv B z))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (q : ComplexTorus L ≃ₜ UnitAddTorus (Fin n))
    (hcov : ∀ z, q (quotientLinearEquiv B z) = integralToralMap A (q z)) :
    ∀ x, (c.toHomeomorph.trans q) (f x) =
      integralToralMap A ((c.toHomeomorph.trans q) x) := by
  intro x
  change q (c (f x)) = integralToralMap A (q (c x))
  have hc' : c (f x) = quotientLinearEquiv B (c x) := hc x
  rw [hc', hcov]

end HolomorphicAnosov.Surface11SupportW06

