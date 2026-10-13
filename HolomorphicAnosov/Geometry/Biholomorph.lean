import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.ComplexModel

/-! This file defines the complex-chart interface for biholomorphisms. -/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

abbrev Biholomorph (d e : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y] :=
  Diffeomorph (complexModel d) (complexModel e) X Y ∞

end HolomorphicAnosov
