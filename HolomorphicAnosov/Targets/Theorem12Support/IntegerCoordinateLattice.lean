import Mathlib.Algebra.Module.ZLattice.Basic

/-!
The integer span of the standard real coordinate basis is a discrete full lattice, characterized by integer coordinates. (Zhang, §3, p.11)
-/

namespace HolomorphicAnosov.IntegerCoordinateLattice

noncomputable section

/-- The integer span of the standard basis of `Fin n → ℝ`. -/
abbrev integerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- A vector lies in the standard integer lattice if and only if every coordinate is an integer. -/
theorem mem_integerLattice (n : ℕ) (v : Fin n → ℝ) :
    v ∈ integerLattice n ↔ ∀ i, ∃ z : ℤ, v i = (z : ℝ) := by
  simpa [integerLattice, eq_comm] using
    (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v

/-- The standard integer lattice has the discrete topology. -/
theorem integerLattice_discrete (n : ℕ) : DiscreteTopology (integerLattice n) :=
  ZSpan.discreteTopology_pi_basisFun

/-- The standard integer lattice spans the entire real coordinate space. -/
theorem integerLattice_span (n : ℕ) :
    Submodule.span ℝ (integerLattice n : Set (Fin n → ℝ)) = ⊤ :=
  ZSpan.span_top (Pi.basisFun ℝ (Fin n))

/-- The standard integer lattice is a full lattice in the real coordinate space. -/
theorem integerLattice_isZLattice (n : ℕ) : IsZLattice ℝ (integerLattice n) :=
  inferInstance


end

end HolomorphicAnosov.IntegerCoordinateLattice
