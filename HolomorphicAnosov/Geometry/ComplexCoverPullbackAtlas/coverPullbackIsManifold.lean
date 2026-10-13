import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackCharts
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackTransition
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- All ordered pairs of charts in the literal lifted atlas are complex smooth (Lee, Prop. 1.15, p.9). -/
theorem coverPullbackIsManifold [IsManifold (complexModel d) ∞ X]
    (p : Y → X) (hp : IsLocalHomeomorph p) :
    letI := coverPullbackCharts (d := d) p hp
    IsManifold (complexModel d) ∞ Y := by
  exact AbstractCoverPullback.isManifold (𝕜 := ℂ) (E := ComplexModel d) p hp


end HolomorphicAnosov
