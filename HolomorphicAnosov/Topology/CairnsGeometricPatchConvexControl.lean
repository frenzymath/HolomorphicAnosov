import HolomorphicAnosov.Topology.CairnsGeometricStarChoice
import HolomorphicAnosov.Topology.CairnsRadialPatchConvexControl

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- A geometric closed-star patch stays in every convex set containing the
prescribed image of its original closed arc. The geometric contact identity
supplies the contact condition, the closed sweep supplies radial coordinates,
and front coverage excludes every totalization branch. Source: Cairns §4(A,C). -/
theorem cairns_geometric_patch_convex_control
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (hb : StarGeometry b h)
    (C : Set ℂ) (hC : Convex ℝ C)
    (hvalues : ∀ t ∈ g.closedArc, (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ) ∈ C) :
    MapsTo (b.patchMap h) (closure b.sourceStar) C := by
  obtain ⟨H,hH,hint,hbase,hne,hopen,hball,hfront,hcoverage⟩ :=
    cairns_geometric_star_literal_extension b h hb
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,hrest⟩
  intro z hz
  apply cairns_radial_patch_convex_control b h C hC
  · intro t
    apply hvalues
    rw [← (CairnsCircleGap.parameter_embedding_range g).2.1]
    exact mem_range_self t
  · exact hCsub
  · exact hcoverage
  · intro hc
    exact hCsub (hCurveCl ▸ ⟨hc,hz⟩)
  · right; right
    rw [hBsweep] at hz
    obtain ⟨Q,hQ,t,ht,he⟩ := hz
    exact ⟨(Q,⟨t,ht⟩),hQ,he⟩

end HolomorphicAnosov.Topology.Plane

