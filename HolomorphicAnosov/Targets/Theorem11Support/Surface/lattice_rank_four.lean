import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
Full lattices in complex dimension two have integral rank four.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW02

universe u
open Module

/-- A full lattice in complex dimension two has integral rank four. -/
theorem lattice_rank_four (L : FullComplexLattice 2) :
    Module.finrank ℤ L.lattice = 4 := by
  let := L.discrete
  let := L.full
  rw [ZLattice.rank ℝ L.lattice]
  rw [finrank_real_of_complex]
  simp [ComplexModel]

end HolomorphicAnosov.Theorem11SupportW02

