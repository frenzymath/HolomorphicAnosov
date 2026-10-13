import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.ZLattice.Basic

open Set

universe u
namespace HolomorphicAnosov

/-- The inverse of a lattice-preserving linear equivalence preserves the same lattice. -/
theorem covering_conjugacy_inverse_lattice_g15
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) (A : V ≃L[ℝ] V)
    (hΓ : A '' (Γ : Set V) = (Γ : Set V)) :
    A.symm '' (Γ : Set V) = (Γ : Set V) := by
  conv_lhs => rw [← hΓ]
  exact A.toLinearEquiv.toEquiv.symm_image_image _


end HolomorphicAnosov
