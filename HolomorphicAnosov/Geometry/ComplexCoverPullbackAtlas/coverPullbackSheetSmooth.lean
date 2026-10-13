import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackCharts
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackIsManifold

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- Every local sheet and its inverse are smooth for the literal pullback atlas (Lee, Prop. 1.15, p.9). -/
theorem coverPullbackSheetSmooth [IsManifold (complexModel d) ∞ X]
    (p : Y → X) (hp : IsLocalHomeomorph p) :
    letI := coverPullbackCharts (d := d) p hp
    ∀ e : OpenPartialHomeomorph Y X, Set.EqOn e p e.source →
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target := by
  exact AbstractCoverPullback.sheetSmooth (𝕜 := ℂ) (E := ComplexModel d) p hp


end HolomorphicAnosov
