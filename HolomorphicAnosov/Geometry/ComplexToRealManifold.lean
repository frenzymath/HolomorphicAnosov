import HolomorphicAnosov.Geometry.ComplexModel


/-!
# The real manifold underlying a complex atlas

This file proves that a smooth complex atlas is a smooth real atlas with the same charts and topology. (Demailly, §3.C; Ghys, §2)
-/

open scoped ContDiff

universe u

namespace HolomorphicAnosov

/-- A smooth complex atlas is also a real smooth atlas with the same charts and topology. (Demailly, §3.C; Ghys, §2) -/
theorem complex_isManifold_real (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] :
    IsManifold (realModel d) ∞ X := by
  apply isManifold_of_contDiffOn (realModel d) ∞ X
  intro e e' he he'
  have h := (contDiffGroupoid ∞ (complexModel d)).compatible he he'
  exact ContDiffOn.restrict_scalars ℝ (mem_groupoid_of_pregroupoid.mp h).1

end HolomorphicAnosov
