import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite bases for finite free modules

Source: the finite free-module reduction used in Hatcher, *Algebraic Topology*,
Theorem 3.15, pp. 214–218: a finite basis is chosen for each free finitely
generated coefficient cohomology module.  The construction uses only the
canonical Mathlib choice of a free-module basis and its finite-index theorem.
DAG node: `algebra.finite_free_basis_g10`.
-/

noncomputable section

universe u

namespace HolomorphicAnosov.AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- A free finitely generated module has a basis indexed by a finite type. -/
theorem finite_basis_of_free_finite
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    ∃ (ι : Type u) (_ : Fintype ι), Nonempty (Module.Basis ι R M) := by
  let b := Module.Free.chooseBasis R M
  exact ⟨Module.Free.ChooseBasisIndex R M, inferInstance, ⟨b⟩⟩


end HolomorphicAnosov.AlgebraicTopology
