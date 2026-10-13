import HolomorphicAnosov.Topology.CairnsEquidistantContactLimit
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates
import HolomorphicAnosov.Topology.CairnsResidualStageContacts

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement
open scoped _root_.Topology

/-- Every chosen first contact lies strictly inside its actual old gap and
is equidistant from the gap's two source endpoints. -/
theorem cairns_star_contact_in_gap_equidistant
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) :
    g.parameter b.contactParameter ∈ g.openArc ∧
      dist b.contact (σ g.first) = dist b.contact (σ g.last) := by
  constructor
  · refine ⟨g.start + (g.stop - g.start) * (b.contactParameter : ℝ),⟨?_,?_⟩,rfl⟩
    · nlinarith [g.start_lt_stop,b.contact_pos]
    · nlinarith [g.start_lt_stop,b.contact_lt_one]
  · change dist (σ (g.parameter b.contactParameter)) _ = dist (σ (g.parameter b.contactParameter)) _
    rw [← b.first_contact]
    simpa only [smul_smul] using
      HolomorphicAnosov.complex_perpendicular_bisector_equidistant
        (σ g.first) (σ g.last) (b.radius * b.sign)

/-- Every selected star's first contact is retained at the next literal stage,
because its included radial seam has that contact in its closure. -/
theorem cairns_successor_retains_first_contact
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (d : Data σ a p q h) (n : ℕ)
    (i : ResidualComponent ((d.stages n).contacts σ)) :
    ((d.steps n).gap i).parameter ((d.steps n).star i).contactParameter ∈
      (d.stages (n + 1)).contacts σ := by
  change ((d.steps n).star i).contact ∈ closure (d.stages (n + 1)).region
  apply closure_mono _ (cairns_star_contact_mem_closure_sourceStar ((d.steps n).star i))
  rw [d.next_eq]
  intro z hz
  exact Or.inr (mem_iUnion.mpr ⟨i,Or.inl hz⟩)

/-- On any initial proper parameter arc with retained endpoints, the literal
Cairns recurrence has dense contacts. Source: Cairns Lemma 4.1, p.865. Pull
back the increasing closed contact sets along the embedded interval parameter.
Every subinterval with retained endpoints and no retained interior point is
an actual residual gap. The step's first contact gives the equidistant point
required by the interval density theorem and is retained at the next stage. -/
theorem cairns_contacts_dense_on_initial_arc
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (d : Data σ a p q h)
    (g : CairnsCircleGap)
    (hf : g.first ∈ (d.stages 0).contacts σ)
    (hl : g.last ∈ (d.stages 0).contacts σ) :
    g.closedArc ⊆ closure (⋃ n, (d.stages n).contacts σ) := by
  classical
  let T := fun n ↦ (d.stages n).contacts σ
  let U := fun n ↦ g.parameter ⁻¹' T n
  have hmono : Monotone T := (cairns_residual_star_recurrence_properties d).2.2.1
  obtain ⟨hparam,hrange,h0,h1⟩ := CairnsCircleGap.parameter_embedding_range g
  have hdense : Dense (⋃ n, U n) := by
    apply HolomorphicAnosov.dense_of_equidistant_gap_refinement
      (σ ∘ g.parameter) (hσ.continuous.comp hparam.continuous)
      (hσ.injective.comp hparam.injective) U
    · intro n
      exact (isClosed_closure.preimage hσ.continuous).preimage hparam.continuous
    · intro n m hnm t ht
      exact hmono hnm ht
    · intro n
      change g.parameter 0 ∈ T n
      rw [h0]
      exact hmono (Nat.zero_le n) hf
    · intro n
      change g.parameter 1 ∈ T n
      rw [h1]
      exact hmono (Nat.zero_le n) hl
    · intro n l u hl hu hlu hgap
      let v := g.subgap l u hlu
      have hv : v.IsGapOf (T n) := by
        apply v.isGapOf_of_endpoints (T n) hl hu
        rw [CairnsCircleGap.subgap_openArc]
        rintro z ⟨t,⟨hlt,htu⟩,rfl⟩
        exact hgap t hlt htu
      let i : ResidualComponent (T n) := ⟨v.openArc,hv.2.2⟩
      let b := (d.steps n).star i
      let v' := (d.steps n).gap i
      have harc : v'.openArc = v.openArc := (d.steps n).gap_arc i
      have hep : ({v'.first,v'.last} : Set Circle) = {v.first,v.last} := by
        have hh := congrArg frontier harc
        simpa only [CairnsCircleGap.openArc,
          cairns_exp_interval_frontier _ _ v'.start_lt_stop v'.shorter_than_turn.le,
          cairns_exp_interval_frontier _ _ v.start_lt_stop v.shorter_than_turn.le,
          CairnsCircleGap.first,CairnsCircleGap.last] using hh
      obtain ⟨hwgap,hweq⟩ := cairns_star_contact_in_gap_equidistant b
      rw [harc,CairnsCircleGap.subgap_openArc] at hwgap
      obtain ⟨w,⟨hlw,hwu⟩,hw⟩ := hwgap
      refine ⟨w,?_,hlw,hwu,?_⟩
      · change g.parameter w ∈ T (n + 1)
        rw [hw]
        exact cairns_successor_retains_first_contact d n i
      · change dist (σ (g.parameter w)) (σ (g.parameter l)) =
          dist (σ (g.parameter w)) (σ (g.parameter u))
        rw [hw]
        change dist b.contact (σ v.first) = dist b.contact (σ v.last)
        rcases pair_eq_pair_iff.mp hep with hh | hh
        · rw [← hh.1,← hh.2]
          exact hweq
        · rw [← hh.2,← hh.1]
          exact hweq.symm
  rw [← hrange]
  rintro z ⟨t,rfl⟩
  apply closure_mono _
    ((image_closure_subset_closure_image hparam.continuous) ⟨t,hdense t,rfl⟩)
  rintro z ⟨t,ht,rfl⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨n,hn⟩

/-- The literal recurrence retains a dense set of original boundary contacts.
Source: Cairns (1951), Lemma 4.1, p.865. Apply the interval refinement argument
to each of the two original opposite proper arcs; their closed parameter
ranges cover the circle and their endpoints are retained from the initial chord. -/
theorem cairns_residual_stage_contacts_dense
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (d : Data σ a p q h) :
    Dense (⋃ n, (d.stages n).contacts σ) := by
  let i := d.initial
  have hchord : openSegment ℝ (σ p) (σ q) ⊆ (d.stages 0).region := by
    rw [d.start_eq]
    exact subset_union_right
  have hp : p ∈ (d.stages 0).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
  have hq : q ∈ (d.stages 0).contacts σ :=
    closure_mono hchord (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))
  have hsfirst : i.secondGap.first = i.firstGap.last := by
    simp only [CairnsCircleGap.first,CairnsCircleGap.last,i.second_start]
  have hslast : i.secondGap.last = i.firstGap.first := by
    simp only [CairnsCircleGap.first,CairnsCircleGap.last,i.second_stop]
    exact Circle.periodic_exp _
  have hf := cairns_contacts_dense_on_initial_arc hσ d i.firstGap
    (by simpa [i.first_eq] using hp) (by simpa [i.last_eq] using hq)
  have hs := cairns_contacts_dense_on_initial_arc hσ d i.secondGap
    (by simpa [hsfirst,i.last_eq] using hq) (by simpa [hslast,i.first_eq] using hp)
  have hcover := (CairnsCircleGap.opposite_parameter_cover_inter i.firstGap i.secondGap
    i.second_start i.second_stop hsfirst hslast).1
  rw [(CairnsCircleGap.parameter_embedding_range i.firstGap).2.1,
    (CairnsCircleGap.parameter_embedding_range i.secondGap).2.1] at hcover
  intro t
  have ht : t ∈ i.firstGap.closedArc ∪ i.secondGap.closedArc := hcover ▸ mem_univ t
  exact ht.elim (fun hh ↦ hf hh) (fun hh ↦ hs hh)

/-- The retained image contacts are dense in the original embedded curve.
The curve is compact, hence closed, and continuity transports density of the
parameter contacts to their image. -/
theorem cairns_residual_image_contacts_closure
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : range σ ≃ₜ Circle}
    (hσ : Topology.IsEmbedding σ) (d : Data σ a p q h) :
    closure (⋃ n, σ '' (d.stages n).contacts σ) = range σ := by
  have hd := cairns_residual_stage_contacts_dense hσ d
  apply Subset.antisymm
  · apply closure_minimal
    · exact iUnion_subset (fun n ↦ image_subset_range _ _)
    · exact (isCompact_range hσ.continuous).isClosed
  · rintro z ⟨t,rfl⟩
    rw [← image_iUnion]
    exact (image_closure_subset_closure_image hσ.continuous) ⟨t,hd t,rfl⟩

end HolomorphicAnosov.Topology.Plane

