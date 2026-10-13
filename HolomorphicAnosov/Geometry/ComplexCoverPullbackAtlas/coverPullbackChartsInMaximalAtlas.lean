import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackCharts
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.smoothSheetsOfLocal

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

/-- The lifted pullback charts belong to every competing smooth covering structure (Lee, Prop. 1.15, p.9). -/
theorem coverPullbackChartsInMaximalAtlas [IsManifold (complexModel d) ∞ X]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    (p : Y → X) (hp : IsLocalHomeomorph p)
    (hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) :
    (coverPullbackCharts (d := d) p hp).atlas ⊆ IsManifold.maximalAtlas (complexModel d) ∞ Y := by
  intro c hc
  obtain ⟨e, z, he, hz, rfl⟩ := hc
  have hes := (smoothSheetsOfLocal p hlocal).2 e he
  have hzm := IsManifold.subset_maximalAtlas (I := complexModel d) (n := ∞) hz
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas hzm).comp
      (hes.1.mono fun y hy ↦ hy.1) (fun y hy ↦ hy.2)
  · exact hes.2.comp ((contMDiffOn_symm_of_mem_maximalAtlas hzm).mono fun x hx ↦ hx.1)
      (fun x hx ↦ hx.2)


end HolomorphicAnosov
