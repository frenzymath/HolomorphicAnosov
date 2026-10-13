import Mathlib.Algebra.Module.ZLattice.Basic

/-! The image of the integer span of a real basis under a continuous linear equivalence spans the
target over the reals. -/

namespace HolomorphicAnosov.UniverseLatticeTransport

universe u v w

/-- The image of the integer span of a real basis under `e` spans the whole target real vector
space. -/
theorem mapped_integerSpan_full
    {V : Type u} {W : Type v} {ι : Type w}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis ι ℝ V) (e : V ≃L[ℝ] W) :
    Submodule.span ℝ (((Submodule.span ℤ (Set.range b)).map
      (e.toLinearMap.restrictScalars ℤ)) : Set W) = ⊤ := by
  have hm : (Submodule.span ℤ (Set.range b)).map (e.toLinearMap.restrictScalars ℤ) =
      Submodule.span ℤ (Set.range (b.map e.toLinearEquiv)) := ZSpan.map b e.toLinearEquiv
  rw [hm]
  exact ZSpan.span_top (b.map e.toLinearEquiv)

end HolomorphicAnosov.UniverseLatticeTransport

