import Mathlib.Algebra.Module.ZLattice.Basic
import HolomorphicAnosov.Targets.Theorem12Support.UniverseLatticeTransport.mapped_integerSpan_full

/-! A real continuous linear equivalence transports the integer span of a finite real basis to a
discrete full lattice. (Zhang, §3, p. 11) -/

namespace HolomorphicAnosov.UniverseLatticeTransport

universe u v w

variable {V : Type u} {W : Type v} {ι : Type w}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [Finite ι]

omit [Finite ι] in
/-- The image of the integer span of `b` under `e` is the integer span of the transported basis. -/
theorem map_integerSpan (b : Module.Basis ι ℝ V) (e : V ≃L[ℝ] W) :
    (Submodule.span ℤ (Set.range b)).map (e.toLinearMap.restrictScalars ℤ) =
      Submodule.span ℤ (Set.range (b.map e.toLinearEquiv)) :=
  ZSpan.map b e.toLinearEquiv

/-- The image of the integer span of a finite real basis under `e` is discrete. -/
theorem mapped_integerSpan_discrete (b : Module.Basis ι ℝ V) (e : V ≃L[ℝ] W) :
    DiscreteTopology ((Submodule.span ℤ (Set.range b)).map
      (e.toLinearMap.restrictScalars ℤ)) := by
  rw [map_integerSpan b e]
  infer_instance

/-- The image of the integer span of a finite real basis under `e` is a full real lattice. -/
theorem mapped_integerSpan_isZLattice (b : Module.Basis ι ℝ V) (e : V ≃L[ℝ] W) :
    letI := mapped_integerSpan_discrete b e
    IsZLattice ℝ ((Submodule.span ℤ (Set.range b)).map
      (e.toLinearMap.restrictScalars ℤ)) := by
  let := mapped_integerSpan_discrete b e
  exact ⟨mapped_integerSpan_full b e⟩


end HolomorphicAnosov.UniverseLatticeTransport
