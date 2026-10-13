import HolomorphicAnosov.Topology.CairnsGeometricRecurrence
import HolomorphicAnosov.Topology.CairnsTargetSectorCover
import HolomorphicAnosov.Topology.CairnsTargetSectorFamily
import HolomorphicAnosov.Topology.CairnsResidualSectorTransport
import HolomorphicAnosov.Topology.CairnsResidualSectorCover
import HolomorphicAnosov.Topology.CairnsResidualSectorShrinking
import HolomorphicAnosov.Topology.CairnsGapMeshAttainment
import HolomorphicAnosov.Topology.CairnsStageDiskCharts
import HolomorphicAnosov.Topology.CairnsTwoStarFrontier
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry
import HolomorphicAnosov.Topology.CairnsResidualStageGaps
import HolomorphicAnosov.Topology.CairnsResidualStageContacts
import HolomorphicAnosov.Topology.CairnsResidualStageMapStability
import HolomorphicAnosov.Topology.CairnsRadialPatchConvexControl
import HolomorphicAnosov.Topology.CairnsResidualStarRecurrenceProperties
import HolomorphicAnosov.Topology.CairnsStarSectorBoundaryContact
import HolomorphicAnosov.Topology.CairnsShrinkingResidualExhaustion
import HolomorphicAnosov.Topology.AccumulatingChordContinuity
import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import HolomorphicAnosov.Topology.Plane.CairnsConvexStarSectorExtension
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsGapMeshEmpty
import HolomorphicAnosov.Topology.CairnsResidualInitialData

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-- The boundary-agreement clause of a scheduled stage homeomorphism follows
from agreement with its literal recurrence map. Source: Cairns §4(B,C), recurrent
Hypothesis (5). Evaluate the homeomorphism through the recurrence map and use
its retained original-boundary values. -/
theorem cairns_schedule_homeomorph_boundary_of_map
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) (j : ℕ)
    (H : ↥(closure (d.stages j).region ∪ range σ) ≃ₜ
      ↥(closure (d.stages j).target ∪ range (fun z : Circle ↦ (z : ℂ))))
    (hH : ∀ x, (H x : ℂ) = (d.stages j).map x)
    (x : ↥(closure (d.stages j).region ∪ range σ))
    (hx : (x : ℂ) ∈ range σ) : (H x : ℂ) = (h ⟨x, hx⟩ : ℂ) := by
  rw [hH]
  exact cairns_residual_stage_map_boundary d j hx

/-- The source-sector component clause of the schedule follows from the actual
step's outside choice once its old chord has been identified in the stage
closure. Source: Cairns §4(C), the outside-sector selection along each old
frontier chord. Apply the open-sector component transfer lemma to each step. -/
theorem cairns_schedule_source_sector_of_chord_closure
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (d : Data σ a p q h) (j : ℕ)
    (i : ResidualComponent ((d.stages j).contacts σ))
    (hchord : openSegment ℝ (σ ((d.steps j).gap i).first)
      (σ ((d.steps j).gap i).last) ⊆ closure (d.stages j).region) :
    ((d.steps j).star i).sector.Nonempty ∧ IsOpen ((d.steps j).star i).sector ∧
      IsConnected ((d.steps j).star i).sector ∧
      ∃ x ∈ a \ closure (d.stages j).region,
        connectedComponentIn (a \ closure (d.stages j).region) x =
          ((d.steps j).star i).sector := by
  obtain ⟨hne, hopen, hconn, _⟩ :=
    cairns_star_sector_geometry hσ ha ((d.steps j).star i)
  exact ⟨hne, hopen, hconn,
    cairns_star_sector_component_outside_closure hσ ha ((d.steps j).star i)
      (d.stages j).region ((d.steps j).outside i) hchord⟩

/-- The uniform convex disk control of all source sectors follows from the
raw step data and boundedness of the original component. Source: Cairns §4(C),
the sector containment used to pass from small boundary arcs to small sectors. -/
theorem cairns_schedule_source_sector_closedBall
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (haBounded : Bornology.IsBounded a) (d : Data σ a p q h) (j : ℕ)
    (i : ResidualComponent ((d.stages j).contacts σ)) (z : ℂ) (r : ℝ)
    (harc : σ '' ((d.steps j).gap i).closedArc ⊆ Metric.closedBall z r) :
    closure ((d.steps j).star i).sector ⊆ Metric.closedBall z r := by
  exact cairns_star_sector_closure_subset_closedBall hσ ha haBounded
    ((d.steps j).star i) z r harc

/-- The actual initial-region frontier is the union of the two chosen fronts,
once opposite-star geometry supplies openness and front avoidance. This is
Cairns §4(B): specialize the two-star seam calculation to the literal initial
data, whose region definition includes exactly both stars and their open base. -/
theorem cairns_schedule_initial_frontier
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h)
    (hfirst : frontier d.initial.firstStar.sourceStar =
      segment ℝ (σ p) (σ q) ∪ d.initial.firstStar.front)
    (hsecond : frontier d.initial.secondStar.sourceStar =
      segment ℝ (σ p) (σ q) ∪ d.initial.secondStar.front)
    (hp : σ p ∈ d.initial.firstStar.front ∪ d.initial.secondStar.front)
    (hq : σ q ∈ d.initial.firstStar.front ∪ d.initial.secondStar.front)
    (hopen : IsOpen (d.stages 0).region)
    (havoid : Disjoint (d.initial.firstStar.front ∪ d.initial.secondStar.front)
      (d.stages 0).region) :
    frontier (d.stages 0).region =
      d.initial.firstStar.front ∪ d.initial.secondStar.front := by
  rw [d.start_eq] at hopen havoid ⊢
  exact (cairns_two_star_frontier _ _ _ _ (σ p) (σ q)
    hfirst hsecond hp hq hopen havoid).2

/-!
Named source-backed simultaneous stage-schedule obligation used by the core provider.

Source: Cairns (1951), §4(B),(C), pp.864–865, recurrent Hypothesis (1)–(5),
equations (4.3),(4.4), Lemma 4.1 and corollary.  The simultaneous recurrence
construction is deferred here as an explicit theorem so its source obligation
can be completed independently of the consumer-facing wrapper.
DAG node: topo.cairns_residual_chord_refinement_schedule_g20.
-/
/-- Cairns's simultaneous recurrent construction and shrinking schedule.
Source: Cairns (1951), §4(B,C), pp.864–865. Start with the two stars on the
opposite sides of the supplied chord. At each stage the boundary is the retained
part of the original curve together with its residual chords. Attach the outside
star for every such chord and extend the map by its radial patch. Patches agree
on old chords by their affine parametrizations. Their disjoint interiors and
shrinking diameters give continuity also at accumulation points of chords.
This proves the cell, frontier, sector partition, and homeomorphism invariants
inductively, while the literal recurrence gives monotonicity and map agreement.
If the union of contacts missed an arc, choose a maximal omitted arc and old
chord endpoints approaching its ends. The next perpendicular-bisector contact
lies strictly inside that arc, a contradiction (Lemma 4.1). Thus contacts are
dense and compactness makes gap lengths tend uniformly to zero; the longest
gap is attained when gaps exist, and empty gap families have mesh zero.
Uniform continuity of both boundary parametrizations and the convex-hull sector
bounds then give uniform source and target diameter decay. Each sector closure
contains its endpoint contacts. Transport of later patches stays in the old
corresponding target sector by disjointness and the recursive construction.

The closedness and four-distinct-contact clause is proved independently by
`cairns_residual_stage_contacts_four` for every literal recurrence datum.
`cairns_residual_stage_gap_labels` supplies the countability clause and proper
angular labels without using the unrestricted-stage residual invariant.

The geometric recurrence theorem establishes these invariants for the actual
initial and successor stages. Target sectors are the convex hull caps of their
labeled arcs; component nesting and closed-hull continuity propagate transport
through all later patches. The proof uses only these actual-stage invariants. -/
theorem cairns_residual_chord_refinement_schedule_source_obligation
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : (range σ) ≃ₜ Circle) (p q : Circle) (hpq : p ≠ q)
    (hChord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (_hCore : p = p)
    (_hSchedule : True) :
    let k := range (fun z : Circle ↦ (z : ℂ))
    let targetBoundary := fun t : Circle ↦ (h ⟨σ t, ⟨t, rfl⟩⟩ : ℂ)
    ∃ d : Data σ a p q h,
      let A := fun j ↦ (d.stages j).region
      let K := fun j ↦ (d.stages j).target
      let T := fun j ↦ (d.stages j).contacts σ
      let I := fun j ↦ ResidualComponent (T j)
      let gap := fun j (i : I j) ↦ (d.steps j).gap i
      let β := fun j (i : I j) ↦ ((d.steps j).star i).sector
      ∃ βt : ∀ j, I j → Set ℂ,
        (∀ j, (A j).Nonempty ∧ IsOpen (A j) ∧ A j ⊆ a ∧
          Nonempty ((A j) ≃ₜ Metric.ball (0 : ℂ) 1) ∧
          (K j).Nonempty ∧ IsOpen (K j) ∧ K j ⊆ Metric.ball (0 : ℂ) 1) ∧
        Monotone A ∧ Monotone K ∧ Monotone T ∧
        (∀ j, IsClosed (T j) ∧
          ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ T j ∧ t₂ ∈ T j ∧ t₃ ∈ T j ∧ t₄ ∈ T j ∧
            t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄) ∧
        Dense (⋃ j, T j) ∧ closure (⋃ j, σ '' T j) = range σ ∧
        (∀ j, Set.Countable {U : Set Circle |
          ∃ x ∈ (T j)ᶜ, connectedComponentIn (T j)ᶜ x = U}) ∧
        (∀ j, Nonempty (Circle ≃ₜ frontier (A j)) ∧
          frontier (A j) = σ '' T j ∪
            ⋃ i : I j, openSegment ℝ (σ (gap j i).first) (σ (gap j i).last) ∧
          frontier (K j) = targetBoundary '' T j ∪
            ⋃ i : I j, openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last)) ∧
        (∀ j, ∃ H : ↥(closure (A j) ∪ range σ) ≃ₜ ↥(closure (K j) ∪ k),
          (∀ x, (H x : ℂ) = (d.stages j).map x) ∧
          (∀ (x : ↥(closure (A j) ∪ range σ)) (hx : (x : ℂ) ∈ range σ),
            (H x : ℂ) = (h ⟨x, hx⟩ : ℂ))) ∧
        (∀ j z, z ∈ closure (A j) ∪ range σ →
          (d.stages (j + 1)).map z = (d.stages j).map z) ∧
        (∀ j (i : I j) (t : CairnsStar.I),
          (d.stages j).map ((1 - (t : ℝ)) • σ (gap j i).first +
            (t : ℝ) • σ (gap j i).last) =
          (1 - (t : ℝ)) • targetBoundary (gap j i).first +
            (t : ℝ) • targetBoundary (gap j i).last) ∧
        (∀ j, T (j + 1) = T j ∪
          ⋃ i : I j, σ ⁻¹' (((d.steps j).star i).front ∩ range σ)) ∧
        (∀ j, K (j + 1) = K j ∪
          ⋃ i : I j, (((d.steps j).star i).targetStar h ∪
            openSegment ℝ (targetBoundary (gap j i).first)
              (targetBoundary (gap j i).last))) ∧
        (∀ j, a \ closure (A j) = ⋃ i : I j, β j i) ∧
        (∀ j, Metric.ball (0 : ℂ) 1 \ closure (K j) = ⋃ i : I j, βt j i) ∧
        (∀ j, Pairwise (fun i i' : I j ↦ Disjoint (β j i) (β j i')) ∧
          Pairwise (fun i i' : I j ↦ Disjoint (βt j i) (βt j i'))) ∧
        (∀ j (i : I j),
          (β j i).Nonempty ∧ IsOpen (β j i) ∧ IsConnected (β j i) ∧
          (∃ x ∈ a \ closure (A j),
            connectedComponentIn (a \ closure (A j)) x = β j i) ∧
          frontier (β j i) ⊆ segment ℝ (σ (gap j i).first) (σ (gap j i).last) ∪
            σ '' (gap j i).closedArc ∧
          (∀ z r, σ '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (β j i) ⊆ Metric.closedBall z r) ∧
          (βt j i).Nonempty ∧ IsOpen (βt j i) ∧ IsConnected (βt j i) ∧
          (∃ x ∈ Metric.ball (0 : ℂ) 1 \ closure (K j),
            connectedComponentIn (Metric.ball (0 : ℂ) 1 \ closure (K j)) x = βt j i) ∧
          frontier (βt j i) ⊆
            segment ℝ (targetBoundary (gap j i).first) (targetBoundary (gap j i).last) ∪
              targetBoundary '' (gap j i).closedArc ∧
          (∀ z r, targetBoundary '' (gap j i).closedArc ⊆ Metric.closedBall z r →
            closure (βt j i) ⊆ Metric.closedBall z r) ∧
          targetBoundary '' (gap j i).closedArc ⊆ closure (βt j i) ∧
          (∀ n : ℕ, j ≤ n →
            MapsTo (d.stages n).map (A n ∩ β j i) (closure (βt j i)))) ∧
        (∀ j, (¬ ∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          CairnsCircleGap.mesh (T j) = 0) ∧
        (∀ j, (∃ g : CairnsCircleGap, g.IsGapOf (T j)) →
          ∃ g : CairnsCircleGap, g.IsGapOf (T j) ∧
            g.normalizedLength = CairnsCircleGap.mesh (T j)) ∧
        Filter.Tendsto (fun j ↦ CairnsCircleGap.mesh (T j)) Filter.atTop (nhds 0) ∧
        (∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ i : I j,
          Metric.diam (closure (β j i)) < ε ∧ Metric.diam (closure (βt j i)) < ε) ∧
        (∀ j (i : I j), (closure (β j i) ∩ range σ).Nonempty ∧
          (closure (βt j i) ∩ k).Nonempty)
        ∧ (∀ _j : ℕ, True) := by
  classical
  obtain ⟨d,hgeom,hstar⟩ := cairns_geometric_recurrence σ hσ a ha haBounded haComponent h p q hpq hChord
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  choose b hb hpair using fun j ↦ cairns_target_sector_family hσ haBounded h (hgeom j) (d.steps j)
  let βt : ∀ j, ResidualComponent ((d.stages j).contacts σ) → Set ℂ := fun j i ↦ (b j i).sector
  have hseam (j : ℕ) (i : ResidualComponent ((d.stages j).contacts σ)) :
      openSegment ℝ (σ ((d.steps j).gap i).first) (σ ((d.steps j).gap i).last) ⊆
        closure (d.stages j).region :=
    ((hgeom j).chord _ ((d.steps j).gap_isGap i)).trans
      (inter_subset_right.trans frontier_subset_closure)
  have hpatch := fun j ↦ cairns_successor_literal_patches hσ haComponent (d.steps j) h (hstar j)
    (hgeom j).curve (hseam j) (fun i ↦ (hgeom j).affine _ ((d.steps j).gap_isGap i))
  have hTclosed (j : ℕ) : IsClosed ((d.stages j).contacts σ) := isClosed_closure.preimage hσ.continuous
  obtain ⟨hA,hK,hT,hmap⟩ := cairns_residual_star_recurrence_properties d
  have hcontrol : ∀ j i z r, τ '' ((d.steps j).gap i).closedArc ⊆ Metric.closedBall z r →
      closure (βt j i) ⊆ Metric.closedBall z r := fun j i ↦ (hb j i).2.2.2.2.2.1
  have hthull : ∀ j i, closure (βt j i) = convexHull ℝ (τ '' ((d.steps j).gap i).closedArc) :=
    fun j i ↦ (hb j i).2.2.2.2.2.2.1
  refine ⟨d,βt,?_,hA,hK,hT,?_,cairns_residual_stage_contacts_dense hσ d,
    cairns_residual_image_contacts_closure hσ d,?_,?_,?_,hmap,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(hgeom j).nonempty,(hgeom j).isOpen,(hgeom j).subset,
      (cairns_stage_disk_charts (hgeom j)).1,(hgeom j).target_nonempty,
      (hgeom j).target_open,(hgeom j).target_ball⟩
  · intro j
    exact ⟨hTclosed j,(hgeom j).four⟩
  · intro j
    exact cairns_residual_components_countable _ (hTclosed j)
  · intro j
    refine ⟨(cairns_stage_disk_charts (hgeom j)).2,
      (hgeom j).source_frontier (d.steps j).gap (d.steps j).gap_isGap (d.steps j).gap_arc,?_⟩
    obtain ⟨H,hH⟩ := (hgeom j).carrier
    obtain ⟨hc,hbij,hi⟩ := literal_carrier_homeomorph_properties _ _ (d.stages j).map H hH
    exact cairns_stage_target_frontier _ h (haBounded.subset (hgeom j).subset).isCompact_closure
      (hc.mono subset_union_left) (hbij.injOn.mono subset_union_left)
      (hgeom j).isOpen (hgeom j).target_open (hgeom j).curve (d.steps j).gap
      ((hgeom j).source_frontier (d.steps j).gap (d.steps j).gap_isGap (d.steps j).gap_arc)
      (fun i ↦ (hgeom j).affine _ ((d.steps j).gap_isGap i))
  · intro j
    obtain ⟨H,hH⟩ := (hgeom j).carrier
    exact ⟨H,hH,fun x hx ↦ (hH x).trans ((hgeom j).curve x hx)⟩
  · intro j i
    exact (hgeom j).affine _ ((d.steps j).gap_isGap i)
  · intro j
    dsimp only []
    rw [d.next_eq j]
    have hc := cairns_successor_closed_stars_compact hσ haComponent haBounded (d.steps j)
      (haBounded.subset (hgeom j).subset) (fun i ↦ (hstar j i).2.2.1)
    apply cairns_successor_contacts (d.steps j)
      (cairns_successor_region_closure (d.steps j) hc.isClosed (hseam j))
    intro i
    exact (hstar j i).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro j
    dsimp only []
    rw [d.next_eq j]
    exact cairns_successor_target_image (d.steps j) h (hstar j) (hpatch j) (hseam j)
      (fun i ↦ (hgeom j).affine _ ((d.steps j).gap_isGap i))
  · intro j
    exact cairns_residual_sectors_cover hσ haComponent haBounded (d.steps j) h (hgeom j)
      (by rw [← d.next_eq j]; exact (hgeom (j+1)).isOpen) (fun i ↦ (hstar j i).2.2.1)
  · intro j
    exact cairns_target_sectors_cover hσ haBounded h (hgeom j) (d.steps j) (b j) (fun i ↦ (hb j i).1)
  · intro j
    exact ⟨cairns_successor_sectors_pairwise_disjoint hσ haComponent (d.steps j)
      (fun i ↦ (hstar j i).2.2.1) (hseam j),hpair j⟩
  · intro j i
    obtain ⟨hne,ho,hconn,hcomp⟩ := cairns_schedule_source_sector_of_chord_closure
      hσ haComponent d j i (hseam j i)
    rcases hb j i with ⟨hout,htne,hto,htconn,htcomp,htcontrol,htcl,htconvex⟩
    refine ⟨hne,ho,hconn,hcomp,((d.steps j).star i).frontier_subset,
      cairns_schedule_source_sector_closedBall hσ haComponent haBounded d j i,
      htne,hto,htconn,htcomp,(b j i).frontier_subset,htcontrol,?_,?_⟩
    · rw [htcl]
      exact subset_convexHull ℝ _
    · intro n hjn
      rw [htcl]
      exact cairns_residual_sector_transport hσ haComponent d hgeom hstar j i n hjn
  · intro j hg
    exact cairns_gap_mesh_eq_zero_of_no_gap hg
  · intro j hg
    exact CairnsCircleGap.mesh_attained_of_closed _ (hTclosed j) hg
  · exact CairnsCircleGap.mesh_tendsto_zero_of_dense _ hT (cairns_residual_stage_contacts_dense hσ d)
  · intro ε hε
    obtain ⟨J₁,h₁⟩ := cairns_residual_source_sectors_shrink hσ haComponent haBounded d ε hε
    obtain ⟨J₂,h₂⟩ := cairns_residual_target_sectors_shrink hσ d βt hcontrol ε hε
    exact ⟨max J₁ J₂,fun j hj i ↦ ⟨h₁ j (le_trans (le_max_left _ _) hj) i,
      h₂ j (le_trans (le_max_right _ _) hj) i⟩⟩
  · intro j i
    refine ⟨cairns_star_sector_boundary_contact ((d.steps j).star i),?_⟩
    refine ⟨τ ((d.steps j).gap i).first,?_,?_⟩
    · rw [hthull]
      exact subset_convexHull ℝ _ (mem_image_of_mem τ
        ⟨((d.steps j).gap i).start,⟨le_rfl,((d.steps j).gap i).start_lt_stop.le⟩,rfl⟩)
    · exact ⟨h ⟨σ ((d.steps j).gap i).first,mem_range_self _⟩,rfl⟩
  · exact fun _ ↦ trivial

end HolomorphicAnosov.Topology.Plane
