import HolomorphicAnosov.Topology.BasedHomotopyUniqueness

namespace HolomorphicAnosov

/-- A based relative homotopy gives equal induced fundamental-group maps.
This is the map-level interface used to turn the rooted contraction and its
collapse inverse into a left inverse on π₁.

Source: Hatcher, *Algebraic Topology*, Proposition 0.17, pp.15--16. The
path-level homotopy is the explicit `based_loop_images_homotopic_of_relative`
construction already proved against Mathlib's path quotient.
-/
theorem graph_spanning_tree_loop_fundamental_map_homotopy_g3
    {K Y : Type*} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ : K) (y₀ : Y) (f g : C(K, Y))
    (hf : f k₀ = y₀) (hg : g k₀ = y₀)
    (H : ContinuousMap.HomotopyRel f g {k₀}) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro p
  change FundamentalGroup.mapOfEq f hf (FundamentalGroup.fromPath ⟦p⟧) =
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.fromPath ⟦p⟧)
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  apply Path.Homotopic.Quotient.eq.mpr
  exact based_loop_images_homotopic_of_relative k₀ y₀ f g hf hg H p

end HolomorphicAnosov
