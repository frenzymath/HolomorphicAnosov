import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry
import HolomorphicAnosov.Topology.CairnsInitialStarChoice
import HolomorphicAnosov.Topology.CairnsResidualStageGaps
import HolomorphicAnosov.Topology.CairnsGeometricStarChoice

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- Only the two endpoints of a residual closed arc are retained contacts.
Interior parameters belong to the complementary component by definition. -/
theorem cairns_gap_contact_endpoints (g : CairnsCircleGap) (S : Set Circle)
    (hg : g.IsGapOf S) : g.closedArc ∩ S ⊆ {g.first,g.last} := by
  rintro z ⟨⟨t,ht,rfl⟩,hzS⟩
  rcases lt_or_eq_of_le ht.1 with hlt | he
  · rcases lt_or_eq_of_le ht.2 with hgt | he
    · obtain ⟨x,hx,hcomp⟩ := hg.2.2
      have hn : Circle.exp t ∉ S := by
        apply connectedComponentIn_subset Sᶜ x
        rw [hcomp]
        exact ⟨t,⟨hlt,hgt⟩,rfl⟩
      exact (hn hzS).elim
    · exact Or.inr (congrArg Circle.exp he)
  · exact Or.inl (congrArg Circle.exp he.symm)

/-- Three distinct retained contacts guarantee one outside any residual
closed arc. This selects the old-region witness for Cairns's outside sector. -/
theorem cairns_gap_exists_contact_outside (g : CairnsCircleGap) (S : Set Circle)
    (hg : g.IsGapOf S)
    (hthree : ∃ p q r : Circle, p ∈ S ∧ q ∈ S ∧ r ∈ S ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r) :
    ∃ r ∈ S, r ∉ g.closedArc := by
  classical
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := hthree
  by_contra! hh
  have hp' := cairns_gap_contact_endpoints g S hg ⟨hh p hp,hp⟩
  have hq' := cairns_gap_contact_endpoints g S hg ⟨hh q hq,hq⟩
  have hr' := cairns_gap_contact_endpoints g S hg ⟨hh r hr,hr⟩
  rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
  · exact hpq (hp'.trans hq'.symm)
  · exact hr'.elim (fun hr' ↦ hpr (hp'.trans hr'.symm))
      (fun hr' ↦ hqr (hq'.trans hr'.symm))
  · exact hr'.elim (fun hr' ↦ hqr (hq'.trans hr'.symm))
      (fun hr' ↦ hpr (hp'.trans hr'.symm))
  · exact hpq (hp'.trans hq'.symm)

/-- An old connected region lies outside the gap's labeled sector when an
old retained contact lies outside its closed arc. Source: Cairns §4(C), the
outside-sector choice. The region avoids its frontier chord, hence if it met
the sector, connectedness would put it entirely in that chord component.
Its closure would then contain the retained contact in the sector closure.
Since the contact is on the original curve it is a frontier point, but the
sector frontier consists only of the gap arc and base chord, contradiction. -/
theorem cairns_sector_disjoint_of_retained_contact
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (b : StarChoice σ a g) (s : Set ℂ) (hs : IsPreconnected s)
    (hsa : s ⊆ a)
    (hChord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a)
    (havoid : Disjoint s (openSegment ℝ (σ g.first) (σ g.last)))
    (r : Circle) (hrcl : σ r ∈ closure s)
    (hrarc : r ∉ g.closedArc) : Disjoint b.sector s := by
  obtain ⟨x,hx,hxa⟩ := ha
  have hac : a ⊆ (range σ)ᶜ := by
    rw [← hxa]
    exact connectedComponentIn_subset _ _
  have hcut : s ⊆ a \ openSegment ℝ (σ g.first) (σ g.last) :=
    fun z hz ↦ ⟨hsa hz,fun hh ↦ havoid.le_bot ⟨hz,hh⟩⟩
  apply Set.disjoint_left.mpr
  intro z hzb hzs
  obtain ⟨y,hy,hyb⟩ := b.component
  have hcomp : connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) z = b.sector := by
    rw [← hyb] at hzb ⊢
    exact (connectedComponentIn_eq hzb).symm
  have hsub : s ⊆ b.sector := by
    rw [← hcomp]
    exact hs.subset_connectedComponentIn hzs hcut
  have hrb : σ r ∈ closure b.sector := closure_mono hsub hrcl
  have hrnot : σ r ∉ b.sector := fun hh ↦
    hac ((cairns_star_sector_geometry hσ ⟨x,hx,hxa⟩ b).2.2.2 hh) ⟨r,rfl⟩
  have hrf : σ r ∈ frontier b.sector := ⟨hrb,fun hh ↦ hrnot (interior_subset hh)⟩
  rcases b.frontier_subset hrf with hrch | hrimage
  · have hrfirst : r ≠ g.first := by
      intro he
      apply hrarc
      rw [he]
      exact ⟨g.start,⟨le_rfl,g.start_lt_stop.le⟩,rfl⟩
    have hrlast : r ≠ g.last := by
      intro he
      apply hrarc
      rw [he]
      exact ⟨g.stop,⟨g.start_lt_stop.le,le_rfl⟩,rfl⟩
    have hropen : σ r ∈ openSegment ℝ (σ g.first) (σ g.last) :=
      mem_openSegment_of_ne_left_right (fun he ↦ hrfirst (hσ.injective he.symm))
        (fun he ↦ hrlast (hσ.injective he.symm)) hrch
    exact hac (hChord hropen) ⟨r,rfl⟩
  · obtain ⟨t,ht,he⟩ := hrimage
    exact hrarc (hσ.injective he ▸ ht)

/-- Choose an actual geometric outside star for a frontier gap of a connected
stage. Source: Cairns §4(C), p.864. Chord separation supplies the component
labeled by this gap's original arc; the convex-star provider supplies its
first-contact star. A retained contact outside the arc forces that entire
sector to miss the old connected region. -/
theorem cairns_choose_outside_geometric_star
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (habounded : Bornology.IsBounded a)
    (hacomp : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (s : Set ℂ) (hsopen : IsOpen s)
    (hsconn : IsPreconnected s) (hsa : s ⊆ a)
    (hthree : ∃ p q r : Circle,
      σ p ∈ closure s ∧ σ q ∈ closure s ∧ σ r ∈ closure s ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r)
    (g : CairnsCircleGap) (hg : g.IsGapOf (σ ⁻¹' closure s))
    (hchord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a)
    (hfront : openSegment ℝ (σ g.first) (σ g.last) ⊆ frontier s) :
    ∃ b : StarChoice σ a g, StarGeometry b h ∧ Disjoint b.sector s := by
  let g' : CairnsCircleGap := {
    start := g.stop
    stop := g.start + 2 * Real.pi
    start_lt_stop := by linarith [g.shorter_than_turn]
    shorter_than_turn := by linarith [g.start_lt_stop] }
  have hpq : g.first ≠ g.last := by
    intro he
    have hh := Circle.exp_injOn_Icc g.shorter_than_turn
      (show g.start ∈ Icc g.start g.stop from ⟨le_rfl,g.start_lt_stop.le⟩)
      (show g.stop ∈ Icc g.start g.stop from ⟨g.start_lt_stop.le,le_rfl⟩) he
    exact g.start_lt_stop.ne hh
  obtain ⟨β₁,β₂,hβ₁ne,hβ₂ne,hβ₁conn,hβ₂conn,hβ₁open,hβ₂open,hdisj,
    hunion,hcomp,hfront₁,hfront₂⟩ := cairns_opposite_gap_sector_frontier_data
      σ hσ a ha habounded hacomp g.first g.last hpq hchord g g' rfl rfl rfl
      (Circle.periodic_exp g.start) rfl rfl
  obtain ⟨x,hx⟩ := hβ₁ne
  have hxcut : x ∈ a \ openSegment ℝ (σ g.first) (σ g.last) := hunion ▸ Or.inl hx
  have hβcomp : ∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
      connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = β₁ := by
    rcases hcomp x hxcut with hh | hh
    · exact ⟨x,hxcut,hh⟩
    · have hx₂ : x ∈ β₂ := hh ▸ mem_connectedComponentIn hxcut
      exact (hdisj.le_bot ⟨hx,hx₂⟩).elim
  obtain ⟨b,hb,hgeom⟩ := cairns_geometric_star_choice σ hσ a ha habounded hacomp
    g hchord β₁ hβcomp hfront₁ h
  obtain ⟨r,hr,hrarc⟩ := cairns_gap_exists_contact_outside g (σ ⁻¹' closure s) hg hthree
  refine ⟨b,hgeom,cairns_sector_disjoint_of_retained_contact hσ hacomp b s hsconn hsa
    hchord ?_ r hr hrarc⟩
  exact (disjoint_frontier_iff_isOpen.mpr hsopen).symm.mono_right hfront

/-- Build the literal next-step choices from a connected open stage whose
frontier contains the residual gap chords. Source: Cairns §4(C), equation
(4.3). The four contacts label every complementary component by a proper gap;
choose its proved geometric outside star independently and package precisely
the gap, star and outside fields required by `StepData`. -/
theorem cairns_stepData_of_stage_frontier
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (habounded : Bornology.IsBounded a)
    (hacomp : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (s : Stage)
    (hsopen : IsOpen s.region) (hsconn : IsPreconnected s.region) (hsa : s.region ⊆ a)
    (hfour : ∃ t₁ t₂ t₃ t₄ : Circle,
      t₁ ∈ s.contacts σ ∧ t₂ ∈ s.contacts σ ∧ t₃ ∈ s.contacts σ ∧ t₄ ∈ s.contacts σ ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄)
    (hchord : ∀ g : CairnsCircleGap, g.IsGapOf (s.contacts σ) →
      openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∩ frontier s.region) :
    ∃ step : StepData σ a s, ∀ i, StarGeometry (step.star i) h := by
  classical
  have hclosed : IsClosed (s.contacts σ) := isClosed_closure.preimage hσ.continuous
  choose gap hgap harc using cairns_gap_of_residual_component _ hclosed hfour
  have hthree : ∃ p q r : Circle,
      σ p ∈ closure s.region ∧ σ q ∈ closure s.region ∧ σ r ∈ closure s.region ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r := by
    obtain ⟨p,q,r,t,hp,hq,hr,ht,hpq,hpr,hpt,hqr,hqt,hrt⟩ := hfour
    exact ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩
  have hex (i : ResidualComponent (s.contacts σ)) :
      ∃ b : StarChoice σ a (gap i), StarGeometry b h ∧ Disjoint b.sector s.region :=
    cairns_choose_outside_geometric_star σ hσ a ha habounded hacomp h s.region hsopen hsconn hsa
      hthree (gap i) (hgap i) ((hchord _ (hgap i)).trans inter_subset_left)
      ((hchord _ (hgap i)).trans inter_subset_right)
  choose star hgeom hout using hex
  exact ⟨{gap := gap,gap_isGap := hgap,gap_arc := harc,star := star,outside := hout},hgeom⟩

end HolomorphicAnosov.Topology.Plane

