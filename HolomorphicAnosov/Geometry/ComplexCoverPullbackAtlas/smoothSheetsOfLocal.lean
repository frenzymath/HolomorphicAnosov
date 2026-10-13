import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- Smooth local covering sheets imply smoothness of the projection and of every other sheet and inverse sheet. (Lee, Prop. 1.15, p. 9). -/
theorem smoothSheetsOfLocal [ChartedSpace (ComplexModel d) Y]
    (p : Y → X)
    (hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) :
    ContMDiff (complexModel d) (complexModel d) ∞ p ∧
      ∀ e : OpenPartialHomeomorph Y X, Set.EqOn e p e.source →
        ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target := by
  exact AbstractCoverPullback.smoothSheetsOfLocal (𝕜 := ℂ) (E := ComplexModel d) p hlocal


end HolomorphicAnosov
