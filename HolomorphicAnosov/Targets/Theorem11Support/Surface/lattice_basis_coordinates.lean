import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_rank_four

/-!
A full lattice in complex dimension two admits an integral basis and real coordinates detecting lattice membership.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW02

universe u
open Module

/-- A full lattice in complex dimension two has a four-element integral basis and a real coordinate
equivalence extending its basis coefficients. Lattice membership is equivalent to all
coordinates being integers. -/
theorem lattice_basis_coordinates (L : FullComplexLattice 2) :
    ∃ b : Basis (Fin 4) ℤ L.lattice,
      ∃ P : ComplexModel 2 ≃L[ℝ] (Fin 4 → ℝ),
        (∀ (x : L.lattice) i, P x i = (b.repr x i : ℝ)) ∧
        (∀ v, v ∈ L.lattice ↔ ∀ i, ∃ z : ℤ, P v i = (z : ℝ)) := by
  classical
  let := L.discrete
  let := L.full
  let b := Module.finBasisOfFinrankEq ℤ L.lattice (lattice_rank_four L)
  let c := b.ofZLatticeBasis ℝ L.lattice
  refine ⟨b, c.equivFun.toContinuousLinearEquiv, ?_, ?_⟩
  · intro x i
    exact b.ofZLatticeBasis_repr_apply ℝ L.lattice x i
  · intro v
    rw [← b.ofZLatticeBasis_span ℝ]
    change v ∈ Submodule.span ℤ (Set.range c) ↔ _
    rw [c.mem_span_iff_repr_mem ℤ]
    simp only [Set.mem_range, algebraMap_int_eq]
    constructor
    · intro h i
      obtain ⟨z, hz⟩ := h i
      exact ⟨z, hz.symm⟩
    · intro h i
      obtain ⟨z, hz⟩ := h i
      exact ⟨z, hz.symm⟩

end HolomorphicAnosov.Theorem11SupportW02

