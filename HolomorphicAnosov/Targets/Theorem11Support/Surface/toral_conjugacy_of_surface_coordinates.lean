import HolomorphicAnosov.Paper.Zhang.HyperbolicRealToralConjugacy
import HolomorphicAnosov.Targets.Theorem11Support.Surface.compose_source_conjugacy
import HolomorphicAnosov.Targets.Theorem11Support.Surface.quotient_covariance

/-!
Compatible surface coordinates and a hyperbolic integer matrix give a hyperbolic real toral conjugacy.
-/

noncomputable section

namespace HolomorphicAnosov.Surface11SupportW06

universe u

/-- A complex torus conjugacy and compatible real quotient coordinates give a hyperbolic real toral
conjugacy when the coordinate matrix is hyperbolic. (Zhang, Theorem 1.1) -/
theorem toral_conjugacy_of_surface_coordinates {d n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (f : X → X) (L : FullComplexLattice d) (B : LatticeLinearEquiv L)
    (c : Biholomorph d d X (ComplexTorus L))
    (hc : Function.Semiconj (fun x ↦ c x) f (fun z ↦ quotientLinearEquiv B z))
    (P : ComplexModel d ≃L[ℝ] (Fin n → ℝ))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (q : ComplexTorus L ≃ₜ UnitAddTorus (Fin n))
    (hq : ∀ (v : ComplexModel d) (i : Fin n),
      q (QuotientAddGroup.mk v) i = (P v i : AddCircle (1 : ℝ)))
    (hPB : ∀ v : ComplexModel d, ∀ i,
      P (B.linear v) i = ∑ j, (A i j : ℝ) * P v j)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    HyperbolicRealToralConjugacy n X f := by
  refine ⟨A, c.toHomeomorph.trans q, hA, ?_⟩
  exact compose_source_conjugacy f L B c hc A q
    (quotient_covariance L B P A q hq hPB)

end HolomorphicAnosov.Surface11SupportW06

