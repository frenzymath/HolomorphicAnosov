import HolomorphicAnosov.Geometry.Biholomorph

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- The local-sheet calculation of C6, Zhang pp.11 and 13. -/
theorem covering_conjugacy_lift_contMDiff_g15
    {d : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]
    (p : Y → X) (hp : ContMDiff (complexModel d) (complexModel d) ∞ p)
    (hsheets : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (L : Y ≃ₜ Y) (b : Biholomorph d d X X)
    (hsquare : ∀ y, p (L y) = b (p y)) :
    ContMDiff (complexModel d) (complexModel d) ∞ L := by
  apply contMDiff_of_locally_contMDiffOn
  intro y
  obtain ⟨e, hy, he, _, heinv⟩ := hsheets (L y)
  let U := L ⁻¹' e.source
  have hmaps : U ⊆ (b ∘ p) ⁻¹' e.target := by
    intro t ht
    change b (p t) ∈ e.target
    rw [← hsquare t, ← he ht]
    exact e.map_source ht
  have hc := heinv.comp (b.contMDiff.comp hp).contMDiffOn hmaps
  refine ⟨U, L.continuous.isOpen_preimage _ e.open_source, hy, hc.congr ?_⟩
  intro t ht
  change L t = e.symm (b (p t))
  rw [← hsquare t, ← he ht]
  exact (e.left_inv ht).symm


end HolomorphicAnosov
