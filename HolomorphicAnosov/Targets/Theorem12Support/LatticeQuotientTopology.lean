import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Covering.Quotient

/-!
The quotient by the standard integer-coordinate lattice is compact, Hausdorff, and second countable, and its projection is a covering map. (Zhang, §3, p.11)
-/

namespace HolomorphicAnosov.IntegerCoordinateQuotient

/-- The integer span of the standard real coordinate basis. -/
abbrev integerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- The additive quotient of real coordinate space by the standard integer lattice, with the
quotient topology. -/
abbrev latticeQuotient (n : ℕ) := (Fin n → ℝ) ⧸ (integerLattice n).toAddSubgroup

/-- The projection onto the lattice quotient is surjective. -/
theorem projection_surjective (n : ℕ) :
    Function.Surjective (QuotientAddGroup.mk : (Fin n → ℝ) → latticeQuotient n) :=
  QuotientAddGroup.mk_surjective

/-- The quotient by the standard integer lattice is compact. -/
theorem latticeQuotient_compact (n : ℕ) : CompactSpace (latticeQuotient n) := by
  constructor
  have hc := IsZLattice.isCompact_range_of_periodic (integerLattice n)
    (QuotientAddGroup.mk : (Fin n → ℝ) → latticeQuotient n)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa using hw)
  simpa only [Set.range_eq_univ.mpr (projection_surjective n)] using hc

/-- The projection onto the quotient by the standard integer lattice is a covering map. -/
theorem projection_covering (n : ℕ) :
    IsCoveringMap (QuotientAddGroup.mk : (Fin n → ℝ) → latticeQuotient n) := by
  have hΓ : IsDiscrete (integerLattice n : Set (Fin n → ℝ)) :=
    isDiscrete_iff_discreteTopology.mpr
      (inferInstanceAs (DiscreteTopology (integerLattice n)))
  exact ((integerLattice n).toAddSubgroup.isAddQuotientCoveringMap_of_comm hΓ).isCoveringMap

/-- The quotient by the standard integer lattice is Hausdorff. -/
theorem latticeQuotient_t2 (n : ℕ) : T2Space (latticeQuotient n) := by
  let : IsClosed ((integerLattice n).toAddSubgroup : Set (Fin n → ℝ)) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

/-- The quotient by the standard integer lattice is second countable. -/
theorem latticeQuotient_secondCountable (n : ℕ) :
    SecondCountableTopology (latticeQuotient n) :=
  inferInstance


end HolomorphicAnosov.IntegerCoordinateQuotient
