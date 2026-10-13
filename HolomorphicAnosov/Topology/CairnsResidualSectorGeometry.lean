import Mathlib.Analysis.Complex.AbsMax
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- A component cut off by a Cairns chord is a nonempty open connected subset
of the original complementary component. Source: Cairns §3, Lemma 3.1. The
original component is open. Since the chord endpoints lie on the original
curve, deleting the open chord is the same as deleting its compact closed
segment within the component. Its components are therefore open and connected.
This statement uses only the component field of the raw star choice. -/
theorem cairns_star_sector_geometry
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (b : StarChoice σ a g) :
    b.sector.Nonempty ∧ IsOpen b.sector ∧ IsConnected b.sector ∧ b.sector ⊆ a := by
  obtain ⟨x, hx, hxa⟩ := ha
  have hac : a ⊆ (range σ)ᶜ := by
    rw [← hxa]
    exact connectedComponentIn_subset _ _
  have haopen : IsOpen a := by
    rw [← hxa]
    exact (isCompact_range hσ.continuous).isClosed.isOpen_compl.connectedComponentIn
  have hdiff : a \ openSegment ℝ (σ g.first) (σ g.last) =
      a \ segment ℝ (σ g.first) (σ g.last) := by
    ext z
    constructor
    · rintro ⟨hza, hz⟩
      refine ⟨hza, fun hseg ↦ hz ?_⟩
      exact mem_openSegment_of_ne_left_right
        (fun he ↦ hac hza ⟨g.first, he⟩)
        (fun he ↦ hac hza ⟨g.last, he⟩) hseg
    · rintro ⟨hza, hz⟩
      exact ⟨hza, fun hseg ↦ hz (openSegment_subset_segment ℝ _ _ hseg)⟩
  have hcutopen : IsOpen (a \ openSegment ℝ (σ g.first) (σ g.last)) := by
    rw [hdiff]
    apply haopen.sdiff
    have hc : IsCompact (segment ℝ (σ g.first) (σ g.last)) := by
      rw [segment_eq_image]
      exact isCompact_Icc.image (by fun_prop)
    exact hc.isClosed
  obtain ⟨y, hy, hyb⟩ := b.component
  have hne : b.sector.Nonempty := ⟨y, hyb ▸ mem_connectedComponentIn hy⟩
  refine ⟨hne, ?_, ?_, ?_⟩
  · rw [← hyb]
    exact hcutopen.connectedComponentIn
  · rw [← hyb]
    exact ⟨⟨y, mem_connectedComponentIn hy⟩, isPreconnected_connectedComponentIn⟩
  · rw [← hyb]
    exact (connectedComponentIn_subset _ _).trans sdiff_subset

/-- An outside chord sector is an actual component of the complement of the
closed filled stage once its old open chord lies in that stage closure.
Source: Cairns §4(C), selection of the sector containing no point of the old
region. Openness of the sector upgrades disjointness from the region to
its closure. The resulting connected subset belongs to the smaller complement;
component monotonicity gives the reverse containment because deleting the
closed stage also deletes the old chord. -/
theorem cairns_star_sector_component_outside_closure
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (b : StarChoice σ a g) (s : Set ℂ)
    (hout : Disjoint b.sector s)
    (hchord : openSegment ℝ (σ g.first) (σ g.last) ⊆ closure s) :
    ∃ x ∈ a \ closure s, connectedComponentIn (a \ closure s) x = b.sector := by
  obtain ⟨hne, hopen, hconn, hsub⟩ := cairns_star_sector_geometry hσ ha b
  have hdis := hout.closure_right hopen
  have hsmall : b.sector ⊆ a \ closure s := fun z hz ↦
    ⟨hsub hz, fun hzs ↦ Set.disjoint_left.mp hdis hz hzs⟩
  obtain ⟨x, hx, hxb⟩ := b.component
  have hxin : x ∈ b.sector := hxb ▸ mem_connectedComponentIn hx
  refine ⟨x, hsmall hxin, Subset.antisymm ?_ ?_⟩
  · rw [← hxb]
    exact connectedComponentIn_mono _ (fun z hz ↦ ⟨hz.1, fun hc ↦ hz.2 (hchord hc)⟩)
  · exact hconn.isPreconnected.subset_connectedComponentIn hxin hsmall

/-- A residual star sector lies in every closed disk containing its original
closed boundary arc. This is the convex-containment bound used in Cairns §4(C)
and Lemma 4.1. The original arc contains both chord endpoints, hence convexity
puts the chord inside the disk too; the raw frontier bound therefore puts the
whole sector frontier inside. For the remaining elementary bounded-domain step
we use Mathlib's maximum-modulus theorem for the affine holomorphic function
w ↦ w-z, giving the same bound on the entire sector closure. This is an
alternative formal proof of the disk-containment step, not a claim that Cairns
uses complex analysis. Empty or negative-radius disks cause no exception: the
arc containment hypothesis already forces them to contain the endpoints. -/
theorem cairns_star_sector_closure_subset_closedBall
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (b : StarChoice σ a g)
    (z : ℂ) (r : ℝ) (harc : σ '' g.closedArc ⊆ Metric.closedBall z r) :
    closure b.sector ⊆ Metric.closedBall z r := by
  have hf : g.first ∈ g.closedArc := ⟨g.start, ⟨le_rfl, g.start_lt_stop.le⟩, rfl⟩
  have hl : g.last ∈ g.closedArc := ⟨g.stop, ⟨g.start_lt_stop.le, le_rfl⟩, rfl⟩
  have hseg : segment ℝ (σ g.first) (σ g.last) ⊆ Metric.closedBall z r :=
    (convex_closedBall z r).segment_subset (harc ⟨g.first, hf, rfl⟩)
      (harc ⟨g.last, hl, rfl⟩)
  have hfront : frontier b.sector ⊆ Metric.closedBall z r :=
    b.frontier_subset.trans (union_subset hseg harc)
  have hb := haBounded.subset (cairns_star_sector_geometry hσ ha b).2.2.2
  intro w hw
  change dist w z ≤ r
  rw [dist_eq_norm]
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hb
    (differentiable_id.sub_const z).diffContOnCl
    (fun v hv ↦ by simpa only [Metric.mem_closedBall, dist_eq_norm, id_eq] using hfront hv) hw

end HolomorphicAnosov.Topology.Plane

