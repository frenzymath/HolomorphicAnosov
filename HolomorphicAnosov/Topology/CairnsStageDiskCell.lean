import HolomorphicAnosov.Topology.CairnsLiteralCarrierProperties
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- An open stage whose literal carrier map has a nonempty bounded convex
image is a disk cell and is connected. Restrict the carrier homeomorphism to
the image region, transport the convex closed-disk chart, and read off its
interior/frontier image equalities. Source: Cairns §4(C), stage disk invariant. -/
theorem cairns_stage_disk_cell
    {σ : Circle → ℂ} (s : Stage) (hopen : IsOpen s.region)
    (htopen : IsOpen s.target) (htne : s.target.Nonempty) (htconvex : Convex ℝ s.target)
    (htbounded : Bornology.IsBounded s.target)
    (H : ↥(closure s.region ∪ range σ) ≃ₜ
      ↥(closure s.target ∪ range (fun z : Circle ↦ (z : ℂ))))
    (hH : ∀ x, (H x : ℂ) = s.map x) :
    IsConnected s.region ∧
      ∃ G : closure s.region ≃ₜ Metric.closedBall (0 : ℂ) 1,
        G '' {z : closure s.region | (z : ℂ) ∈ s.region} =
          {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
        G '' {z : closure s.region | (z : ℂ) ∈ frontier s.region} =
          {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1} := by
  have hi := (literal_carrier_homeomorph_properties _ _ s.map H hH).2.2 s.region
    (subset_closure.trans subset_union_left)
  have hconn : IsConnected s.region := by
    let F := homeomorphRestrictSubsets _ _ s.region s.target
      (subset_closure.trans subset_union_left) (subset_closure.trans subset_union_left) H hi
    rw [isConnected_iff_connectedSpace,F.connectedSpace_iff]
    exact isConnected_iff_connectedSpace.mp (htconvex.isConnected htne)
  obtain ⟨G,hGi,hGf⟩ := carrier_homeomorph_closed_disk_chart _ _ s.region s.target hopen
    htopen htne htconvex htbounded subset_union_left subset_union_left H hi
  have himage (P Q : Set ℂ)
      (hPQ : ∀ x : closure s.region, (x : ℂ) ∈ P ↔ (G x : ℂ) ∈ Q) :
      G '' {x : closure s.region | (x : ℂ) ∈ P} =
        {y : Metric.closedBall (0 : ℂ) 1 | (y : ℂ) ∈ Q} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hPQ x).mp hx
    · intro hy
      refine ⟨G.symm y,(hPQ (G.symm y)).mpr ?_,G.apply_symm_apply y⟩
      simpa only [G.apply_symm_apply] using (show (y : ℂ) ∈ Q from hy)
  exact ⟨hconn,G,himage _ _ hGi,himage _ _ hGf⟩

end HolomorphicAnosov.Topology.Plane

