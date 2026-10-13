import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import Mathlib.Topology.IsLocalHomeomorph
import HolomorphicAnosov.Geometry.ComplexModel

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- The pullback atlas consists of sheet compositions with the downstairs atlas (Lee, Prop. 1.15, p.9). -/
noncomputable abbrev coverPullbackCharts (p : Y → X) (hp : IsLocalHomeomorph p) :
    ChartedSpace (ComplexModel d) Y :=
  AbstractCoverPullback.charts (E := ComplexModel d) p hp


end HolomorphicAnosov
