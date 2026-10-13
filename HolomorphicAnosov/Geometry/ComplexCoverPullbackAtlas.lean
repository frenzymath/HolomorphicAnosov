import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackCharts
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackTransition
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackIsManifold
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackSheetSmooth
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.smoothSheetsOfLocal
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.deckSmoothOfSheets
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackChartsInMaximalAtlas
import Mathlib.Topology.Covering.Basic
import HolomorphicAnosov.Geometry.Biholomorph




/-! Complex structures pulled back by topological coverings are constructed here, together with smooth sheets, deck transformations, and uniqueness of the maximal atlas. (Lee, Prop. 1.15, p. 9; Zhang, pp. 11–12).
-/
namespace HolomorphicAnosov

universe u v

open scoped ContDiff


/-- A surjective topological covering of a complex manifold admits a compatible complex structure whose charts are lifted sheet charts. The resulting projection, sheets, deck transformations, and maximal atlas satisfy the stated smoothness and uniqueness properties. (Lee, Prop. 1.15, p. 9). -/
theorem complex_cover_pullback_atlas
    {d : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (p : Y → X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ A : ChartedSpace (ComplexModel d) Y,
      let : ChartedSpace (ComplexModel d) Y := A
      IsManifold (complexModel d) ∞ Y ∧
      (∀ c : OpenPartialHomeomorph Y (ComplexModel d),
        c ∈ atlas (ComplexModel d) Y ↔
          ∃ (e : OpenPartialHomeomorph Y X) (z : OpenPartialHomeomorph X (ComplexModel d)),
            Set.EqOn e p e.source ∧ z ∈ atlas (ComplexModel d) X ∧ c = e.trans z) ∧
      ContMDiff (complexModel d) (complexModel d) ∞ p ∧
      (∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
        y ∈ e.source ∧ Set.EqOn e p e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) ∧
      (∀ e : OpenPartialHomeomorph Y X, Set.EqOn e p e.source →
        ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) ∧
      (∀ δ : Y ≃ₜ Y, (∀ y, p (δ y) = p y) →
        ∃ b : Biholomorph d d Y Y, b.toHomeomorph = δ) ∧
      (∀ B : ChartedSpace (ComplexModel d) Y,
        (letI : ChartedSpace (ComplexModel d) Y := B
         IsManifold (complexModel d) ∞ Y ∧
           ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
             y ∈ e.source ∧ Set.EqOn e p e.source ∧
               ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
               ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) →
        (letI : ChartedSpace (ComplexModel d) Y := B
         IsManifold.maximalAtlas (complexModel d) ∞ Y) =
          (letI : ChartedSpace (ComplexModel d) Y := A;
           IsManifold.maximalAtlas (complexModel d) ∞ Y)) := by
  have _ := hsurj
  let A := coverPullbackCharts (d := d) p hp.isLocalHomeomorph
  refine ⟨A, coverPullbackIsManifold (d := d) p hp.isLocalHomeomorph, ?_, ?_⟩
  · intro c
    rfl
  · let : ChartedSpace (ComplexModel d) Y := A
    have : IsManifold (complexModel d) ∞ Y :=
      coverPullbackIsManifold (d := d) p hp.isLocalHomeomorph
    have hsheets := coverPullbackSheetSmooth (d := d) p hp.isLocalHomeomorph
    have hlocal : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
        y ∈ e.source ∧ Set.EqOn e p e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target := by
      intro y
      let e := (hp.isLocalHomeomorph.localInverseAt y).symm
      have he : Set.EqOn e p e.source := fun t _ ↦
        congrFun (hp.isLocalHomeomorph.localInverseAt_symm y) t
      exact ⟨e, hp.isLocalHomeomorph.self_mem_localInverseAt_target (x := y), he, hsheets e he⟩
    have hprojection := (smoothSheetsOfLocal p hlocal).1
    refine ⟨hprojection, hlocal, hsheets, ?_, ?_⟩
    · intro δ hδ
      have hforward := deckSmoothOfSheets p hprojection hlocal δ δ.continuous hδ
      have hinverse := deckSmoothOfSheets p hprojection hlocal δ.symm δ.symm.continuous
        (fun y ↦ by simpa only [δ.apply_symm_apply] using (hδ (δ.symm y)).symm)
      let b : Biholomorph d d Y Y :=
        { toEquiv := δ.toEquiv
          contMDiff_toFun := hforward
          contMDiff_invFun := hinverse }
      exact ⟨b, rfl⟩
    · intro B hB
      let : ChartedSpace (ComplexModel d) Y := A
      have hBA : A.atlas ⊆
          (letI : ChartedSpace (ComplexModel d) Y := B
           IsManifold.maximalAtlas (complexModel d) ∞ Y) := by
        let : ChartedSpace (ComplexModel d) Y := B
        have : IsManifold (complexModel d) ∞ Y := hB.1
        exact coverPullbackChartsInMaximalAtlas p hp.isLocalHomeomorph hB.2
      have hsub : (letI : ChartedSpace (ComplexModel d) Y := B
          IsManifold.maximalAtlas (complexModel d) ∞ Y) ⊆
          IsManifold.maximalAtlas (complexModel d) ∞ Y := by
        intro c hc c' hc'
        have hc'B := hBA hc'
        let : ChartedSpace (ComplexModel d) Y := B
        have : IsManifold (complexModel d) ∞ Y := hB.1
        exact ⟨IsManifold.compatible_of_mem_maximalAtlas hc hc'B,
          IsManifold.compatible_of_mem_maximalAtlas hc'B hc⟩
      apply Set.Subset.antisymm hsub
      intro c hc c' hc'
      have hc'A : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ Y := hsub (by
        let : ChartedSpace (ComplexModel d) Y := B
        have : IsManifold (complexModel d) ∞ Y := hB.1
        exact IsManifold.subset_maximalAtlas hc')
      exact ⟨IsManifold.compatible_of_mem_maximalAtlas hc hc'A,
        IsManifold.compatible_of_mem_maximalAtlas hc'A hc⟩


end HolomorphicAnosov
