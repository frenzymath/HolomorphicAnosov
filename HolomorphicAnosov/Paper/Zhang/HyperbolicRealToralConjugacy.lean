import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Homeomorph.Defs
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap

/-! This file states the real toral conjugacy supplied by a hyperbolic integral matrix. (Zhang, Theorem 1.1) -/

namespace HolomorphicAnosov

universe u

/-- A map is topologically conjugate to a hyperbolic integral automorphism of the real `n`-torus when an invertible integer matrix supplies its action on the quotient torus and has no eigenvalues of modulus one. (Zhang, Theorem 1.1) -/
def HyperbolicRealToralConjugacy (n : ℕ) (X : Type u) [TopologicalSpace X]
    (f : X → X) : Prop :=
  ∃ (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (h : X ≃ₜ UnitAddTorus (Fin n)),
    (∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) ∧
    ∀ x : X, h (f x) = integralToralMap A (h x)

end HolomorphicAnosov
