import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsGapParameter
import HolomorphicAnosov.Topology.CairnsLiteralPatchIdentification

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

namespace CairnsRefinement
/-- The source, front, and radial-extension conclusions of Cairns's single-star
provider, expressed in the literal `StarChoice` coordinates. This proof record
adds no data to a choice and asserts no existence by definition. -/
def StarGeometry {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) : Prop :=
  let α := g.parameter
  let β := b.sector
  let c := range σ
  let μ := σ '' range g.parameter
  let D₁ := σ g.first
  let D₂ := σ g.last
  let M := b.center
  let P := b.contact
  let E₁ : ℂ := h ⟨D₁,⟨g.first,rfl⟩⟩
  let E₂ : ℂ := h ⟨D₂,⟨g.last,rfl⟩⟩
  let N := b.targetCenter h
  let k := range (fun z : Circle ↦ (z : ℂ))
  let L := b.front
  let B := b.sourceStar
  let C := L ∩ c
  B.Nonempty ∧ IsOpen B ∧ B ⊆ β ∧
      frontier B = segment ℝ D₁ D₂ ∪ L ∧ IsCompact L ∧
      closure B = sweep M L ∧ B = openStar D₁ D₂ P M L ∧
      (∀ z ∈ closure B, z ≠ M →
        ∃! w : L × I, z = (1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : ℂ)) ∧
      IsClosed C ∧ C ⊆ μ ∧ D₁ ∈ C ∧ D₂ ∈ C ∧ P ∈ C ∧
      c ∩ closure B = C ∧
      ∃ (qs : I ≃ₜ L), (qs ⟨0, by simp⟩ : ℂ) = D₁ ∧
        (qs ⟨1, by simp⟩ : ℂ) = D₂ ∧
        (∀ u v s t : I, σ (g.parameter u) ∈ C → σ (g.parameter v) ∈ C →
          (qs s : ℂ) = σ (g.parameter u) → (qs t : ℂ) = σ (g.parameter v) → (u ≤ v ↔ s ≤ t)) ∧
        gapPairs (fun t : I ↦ σ (g.parameter t)) C = gapPairs (fun t ↦ (qs t : ℂ)) C ∧
        (∀ l r : I, l < r → (qs l : ℂ) ∈ C → (qs r : ℂ) ∈ C →
          (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ C) →
          (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r} =
            openSegment ℝ (qs l : ℂ) (qs r : ℂ) ∧
          openSegment ℝ (qs l : ℂ) (qs r : ℂ) ⊆ a ∧
          Disjoint (openSegment ℝ (qs l : ℂ) (qs r : ℂ)) c) ∧
        (∀ x ∈ μ \ C, ∃ l r : I, l < r ∧ σ (g.parameter l) ∈ C ∧ σ (g.parameter r) ∈ C ∧
          (∀ t : I, l < t → t < r → σ (g.parameter t) ∉ C) ∧
          connectedComponentIn (μ \ C) x =
            (fun t : I ↦ σ (g.parameter t)) '' {t : I | l < t ∧ t < r}) ∧
        (∀ x ∈ L \ C, ∃ l r : I, l < r ∧ (qs l : ℂ) ∈ C ∧ (qs r : ℂ) ∈ C ∧
          (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ C) ∧
          connectedComponentIn (L \ C) x =
            (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r}) ∧
        Set.Countable {G : Set ℂ | ∃ x ∈ L \ C, connectedComponentIn (L \ C) x = G} ∧
        ∃ ds : L ≃ₜ directions D₁ D₂ P,
          (∀ Q : L, ((ds Q : Circle) : ℂ) = ((Q : ℂ) - M) / (‖(Q : ℂ) - M‖ : ℂ)) ∧
          Continuous (fun v : directions D₁ D₂ P ↦ ‖(ds.symm v : ℂ) - M‖) ∧
          (∀ v : directions D₁ D₂ P, 0 < ‖(ds.symm v : ℂ) - M‖) ∧
          ∃ (ν : Set ℂ) (H₀ : ↥(c ∪ segment ℝ D₁ D₂ ∪ L) ≃ₜ
            ↥(k ∪ segment ℝ E₁ E₂ ∪ ν)),
            H₀ '' {x | (x : ℂ) ∈ L} = {y | (y : ℂ) ∈ ν} ∧
            (∀ (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)) (hx : (x : ℂ) ∈ c),
              (H₀ x : ℂ) = (h ⟨(x : ℂ), hx⟩ : ℂ)) ∧
            (∀ (x₁ x₂ : c) (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
              ((x₁ : ℂ), (x₂ : ℂ)) ∈ gapPairs (fun t ↦ (qs t : ℂ)) C →
              (x : ℂ) = (1 - (t : ℝ)) • (x₁ : ℂ) + (t : ℝ) • (x₂ : ℂ) →
              (H₀ x : ℂ) = (1 - (t : ℝ)) • (h x₁ : ℂ) + (t : ℝ) • (h x₂ : ℂ)) ∧
            (∀ (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
              (x : ℂ) = (1 - (t : ℝ)) • D₁ + (t : ℝ) • D₂ →
              (H₀ x : ℂ) = (1 - (t : ℝ)) • E₁ + (t : ℝ) • E₂) ∧
            let Eₚ : ℂ := h ⟨σ (g.parameter b.contactParameter), ⟨α b.contactParameter, rfl⟩⟩
            let Cν := Subtype.val '' h '' {x : c | (x : ℂ) ∈ C}
            let γ := openStar E₁ E₂ Eₚ N ν
            IsCompact ν ∧ ν ∩ k = Cν ∧
            γ.Nonempty ∧ IsOpen γ ∧ frontier γ = segment ℝ E₁ E₂ ∪ ν ∧
            closure γ = sweep N ν ∧
            γ ⊆ Metric.ball (0 : ℂ) 1 ∩
              {z | 0 < ((star (E₂ - E₁) * (Eₚ - E₁)).im) *
                ((star (E₂ - E₁) * (z - E₁)).im)} ∧
            (∀ z ∈ closure γ, z ≠ N →
              ∃! w : ν × I, z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)) ∧
            ∃ qt : I ≃ₜ ν,
              (qt ⟨0, by simp⟩ : ℂ) = E₁ ∧ (qt ⟨1, by simp⟩ : ℂ) = E₂ ∧
              (∀ (t : I) (x : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
                (x : ℂ) = (qs t : ℂ) → (H₀ x : ℂ) = (qt t : ℂ)) ∧
              gapPairs (fun t : I ↦ (h ⟨σ (g.parameter t), ⟨α t, rfl⟩⟩ : ℂ)) Cν =
                gapPairs (fun t ↦ (qt t : ℂ)) Cν ∧
              (∀ l r : I, l < r → (qt l : ℂ) ∈ Cν → (qt r : ℂ) ∈ Cν →
                (∀ t : I, l < t → t < r → (qt t : ℂ) ∉ Cν) →
                (fun t : I ↦ (qt t : ℂ)) '' {t : I | l < t ∧ t < r} =
                  openSegment ℝ (qt l : ℂ) (qt r : ℂ) ∧
                openSegment ℝ (qt l : ℂ) (qt r : ℂ) ⊆ Metric.ball (0 : ℂ) 1 ∧
                Disjoint (openSegment ℝ (qt l : ℂ) (qt r : ℂ)) k) ∧
              ∃ dt : ν ≃ₜ directions E₁ E₂ Eₚ,
                (∀ Q : ν, ((dt Q : Circle) : ℂ) =
                  ((Q : ℂ) - N) / (‖(Q : ℂ) - N‖ : ℂ)) ∧
                Continuous (fun v : directions E₁ E₂ Eₚ ↦ ‖(dt.symm v : ℂ) - N‖) ∧
                (∀ v : directions E₁ E₂ Eₚ, 0 < ‖(dt.symm v : ℂ) - N‖) ∧
                ∃ H : ↥(c ∪ closure B) ≃ₜ ↥(k ∪ closure γ),
                  (∀ (x : ↥(c ∪ closure B)) (hx : (x : ℂ) ∈ c),
                    (H x : ℂ) = (h ⟨(x : ℂ), hx⟩ : ℂ)) ∧
                  (∀ (Q : L) (t : I) (x : ↥(c ∪ closure B))
                    (y : ↥(c ∪ segment ℝ D₁ D₂ ∪ L)),
                    (y : ℂ) = (Q : ℂ) →
                    (x : ℂ) = (1 - (t : ℝ)) • M + (t : ℝ) • (Q : ℂ) →
                    (H x : ℂ) = (1 - (t : ℝ)) • N + (t : ℝ) • (H₀ y : ℂ))
end CairnsRefinement

/-- Choose a star with the full geometric conclusions of the source provider.
Source: Cairns (1951), §3(D,E) and §4(A), pp.862–864. Parametrize the chosen
proper gap and the reversed opposite gap, apply the convex-star theorem, and
retain its actual first-contact witnesses. Rewriting its formulas by that
first-contact identity gives the literal recurrence's front and source star. -/
theorem cairns_geometric_star_choice
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ) (ha : a.Nonempty) (haBounded : Bornology.IsBounded a)
    (haComponent : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (g : CairnsCircleGap)
    (hChord : openSegment ℝ (σ g.first) (σ g.last) ⊆ a)
    (β : Set ℂ)
    (hβ : ∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
      connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = β)
    (hfront : frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc)
    (h : range σ ≃ₜ Circle) :
    ∃ b : StarChoice σ a g, b.sector = β ∧ StarGeometry b h := by
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
  obtain ⟨hα,hα',hα0,hα1,hα'0,hα'1,hcover,hmeet⟩ :=
    CairnsCircleGap.opposite_parameter_chord_arc_data g g' rfl rfl rfl (Circle.periodic_exp g.start)
  obtain ⟨ε,τ,sP,hε,hτ,hs0,hs1,hP,hray,hgeom⟩ :=
    cairns_convex_star_sector_extension σ hσ g.first g.last hpq
      g.parameter (fun t ↦ g'.parameter (unitInterval.symm t))
      hα hα' hα0 hα1 hα'0 hα'1 hcover hmeet a β ha haBounded haComponent
      hChord hβ (by simpa only [(CairnsCircleGap.parameter_embedding_range g).2.1] using hfront) h
  let b : StarChoice σ a g := {
    sector := β
    component := hβ
    frontier_subset := hfront
    sign := ε
    sign_eq := hε
    radius := τ
    radius_pos := hτ
    contactParameter := sP
    contact_pos := hs0
    contact_lt_one := hs1
    first_contact := hP
    ray_inside := hray }
  refine ⟨b,rfl,?_⟩
  generalize hPdef : (σ g.first + σ g.last) / 2 +
    τ • (ε • (Complex.I * (σ g.last - σ g.first))) = P at hgeom
  have hPeq : P = σ (g.parameter sP) := hPdef.symm.trans hP
  clear hPdef
  subst P
  exact hgeom

/-- The geometric provider's extension is the exact radial patch used by
the recurrence. Source: Cairns §4(A), (4.1)–(4.2). Its skeleton map agrees
with the literal affine front map by the front-gap coverage theorem. The
radial formulas agree at the center and along every sweep coordinate, and
both maps prescribe the original boundary values. -/
theorem cairns_geometric_star_literal_extension
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (hb : StarGeometry b h) :
    ∃ H : ↥(range σ ∪ closure b.sourceStar) ≃ₜ
        ↥(range (fun z : Circle ↦ (z : ℂ)) ∪ closure (b.targetStar h)),
      (∀ x, (H x : ℂ) = b.patchMap h x) ∧
      (∀ x : ↥(range σ ∪ closure b.sourceStar), ((x : ℂ) ∈ b.sourceStar ↔ (H x : ℂ) ∈ b.targetStar h)) ∧
      (∀ t : I, b.patchMap h ((1 - (t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
        (1 - (t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ)) ∧
      (b.targetStar h).Nonempty ∧ IsOpen (b.targetStar h) ∧
      b.targetStar h ⊆ Metric.ball (0 : ℂ) 1 ∧
      frontier (b.targetStar h) =
        segment ℝ (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ)
          (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) ∪ b.targetFront h ∧
      (∀ z ∈ b.front, z ∉ range σ → ∃ w, b.FrontCoordinate z w) := by
  classical
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,
    hcompμ,hcompL,hcount,ds,hds,hdcont,hdpos,ν,H₀,hH₀front,hH₀curve,
    hH₀chord,hH₀base,hνc,hνcurve,hγne,hγopen,hγfront,hγsweep,hγsub,hγunique,
    qt,hqt0,hqt1,hqtH,hpairtarget,hchordtarget,dt,hdt,hdtcont,hdtpos,H,hHcurve,hHrad⟩
  let S₀ := range σ ∪ segment ℝ (σ g.first) (σ g.last) ∪ b.front
  let S := range σ ∪ closure b.sourceStar
  let F₀ : ℂ → ℂ := fun z ↦ if hz : z ∈ S₀ then (H₀ ⟨z,hz⟩ : ℂ) else 0
  let F : ℂ → ℂ := fun z ↦ if hz : z ∈ S then (H ⟨z,hz⟩ : ℂ) else 0
  have hF₀ (z : ℂ) (hz : z ∈ b.front) :
      F₀ z = (H₀ ⟨z,Or.inr hz⟩ : ℂ) := dite_eq_left (Or.inr hz)
  have hcoverage := cairns_front_coordinate_coverage b qs hpairs
    (fun l r hlr hl hr hg ↦ (hchords l r hlr hl hr hg).1) hcompL
  have hfrontEq : ∀ z ∈ b.front, b.frontMap h z = F₀ z := by
    apply cairns_frontMap_eq_of_affine b h F₀ hcoverage
    · intro z hz hzc
      rw [hF₀ z hz]
      exact hH₀curve _ hzc
    · intro z hz w hw
      rw [hF₀ z hz]
      apply hH₀chord
        ⟨σ (g.parameter w.1),⟨g.parameter w.1,rfl⟩⟩
        ⟨σ (g.parameter w.2.1),⟨g.parameter w.2.1,rfl⟩⟩ w.2.2
      · rw [← hpairs]
        exact hw.1
      · exact hw.2
  have hH₀front' : Subtype.val '' H₀ '' {x | (x : ℂ) ∈ b.front} = ν := hH₀front
  have hfrontImage : b.targetFront h = ν := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : (H₀ ⟨x,Or.inr hx⟩ : ℂ) ∈ ν := by
        exact hH₀front'.subset ⟨H₀ ⟨x,Or.inr hx⟩,⟨⟨x,Or.inr hx⟩,hx,rfl⟩,rfl⟩
      rw [hfrontEq x hx,hF₀ x hx]
      exact hy
    · intro hz
      rw [← hH₀front'] at hz
      obtain ⟨y,⟨x,hx,hxy⟩,hyz⟩ := hz
      refine ⟨x.val,hx,?_⟩
      rw [hfrontEq _ hx,hF₀ _ hx]
      exact (congrArg Subtype.val hxy).trans hyz
  have hpatch : ∀ z ∈ S, b.patchMap h z = F z := by
    apply cairns_patchMap_eq_of_radial b h S F F₀ hfrontEq
    · intro z hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · right; right
        rw [hBsweep] at hz
        obtain ⟨Q,hQ,t,ht,he⟩ := hz
        exact ⟨(Q,⟨t,ht⟩),hQ,he⟩
    · intro z hz hzc
      rw [show F z = (H ⟨z,hz⟩ : ℂ) from dite_eq_left hz]
      exact hHcurve _ hzc
    · intro hc
      rw [show F b.center = (H ⟨b.center,hc⟩ : ℂ) from dite_eq_left hc]
      have hh := hHrad ⟨σ g.first,hD₁.1⟩ 0 ⟨b.center,hc⟩
        ⟨σ g.first,Or.inr hD₁.1⟩ rfl (by simp)
      simpa using hh
    · intro z hz w hw
      rw [show F z = (H ⟨z,hz⟩ : ℂ) from dite_eq_left hz,hF₀ _ hw.1]
      exact hHrad ⟨w.1,hw.1⟩ w.2 ⟨z,hz⟩ ⟨w.1,Or.inr hw.1⟩ rfl hw.2
  have hbase : ∀ t : I,
      b.patchMap h ((1 - (t : ℝ)) • σ g.first + (t : ℝ) • σ g.last) =
        (1 - (t : ℝ)) • (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) := by
    apply cairns_midpoint_radial_base_affine
    · intro t
      have hx : (1 - (t : ℝ)) • b.center + (t : ℝ) • σ g.first ∈ S := by
        right
        rw [hBsweep]
        exact ⟨σ g.first,hD₁.1,t,t.property,rfl⟩
      change b.patchMap h ((1 - (t : ℝ)) • b.center + (t : ℝ) • _) = _
      rw [hpatch _ hx]
      change (if hz : _ ∈ S then (H ⟨_,hz⟩ : ℂ) else 0) = _
      rw [dite_eq_left hx]
      have hh := hHrad ⟨σ g.first,hD₁.1⟩ t ⟨_,hx⟩
        ⟨σ g.first,Or.inr hD₁.1⟩ rfl rfl
      rw [hH₀curve _ hD₁.2] at hh
      exact hh
    · intro t
      have hx : (1 - (t : ℝ)) • b.center + (t : ℝ) • σ g.last ∈ S := by
        right
        rw [hBsweep]
        exact ⟨σ g.last,hD₂.1,t,t.property,rfl⟩
      change b.patchMap h ((1 - (t : ℝ)) • b.center + (t : ℝ) • _) = _
      rw [hpatch _ hx]
      change (if hz : _ ∈ S then (H ⟨_,hz⟩ : ℂ) else 0) = _
      rw [dite_eq_left hx]
      have hh := hHrad ⟨σ g.last,hD₂.1⟩ t ⟨_,hx⟩
        ⟨σ g.last,Or.inr hD₂.1⟩ rfl rfl
      rw [hH₀curve _ hD₂.2] at hh
      exact hh
  let γ := CairnsStar.openStar (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ)
    (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ)
    (h ⟨b.contact,⟨g.parameter b.contactParameter,rfl⟩⟩ : ℂ) (b.targetCenter h) ν
  have hγ : γ = b.targetStar h := by
    simp only [StarChoice.targetStar,hfrontImage,γ]
  have hS₀sub : S₀ ⊆ S := by
    intro z hz
    rcases hz with (hzc | hzb) | hzf
    · exact Or.inl hzc
    · right
      exact frontier_subset_closure (hBfront ▸ Or.inl hzb)
    · right
      exact frontier_subset_closure (hBfront ▸ Or.inr hzf)
  have hFH₀ (z : ℂ) (hz : z ∈ S₀) : F z = (H₀ ⟨z,hz⟩ : ℂ) := by
    rw [show F z = (H ⟨z,hS₀sub hz⟩ : ℂ) from dite_eq_left (hS₀sub hz)]
    rcases hz with (hzc | hzb) | hzf
    · rw [hHcurve _ hzc,hH₀curve _ hzc]
    · rw [segment_eq_image] at hzb
      obtain ⟨t,ht,rfl⟩ := hzb
      have hx := hS₀sub (Or.inl (Or.inr
        (show (1 - t) • σ g.first + t • σ g.last ∈ segment ℝ (σ g.first) (σ g.last) from
          ⟨1-t,t,sub_nonneg.mpr ht.2,ht.1,sub_add_cancel _ _,rfl⟩)))
      have hh := hbase ⟨t,ht⟩
      rw [hpatch _ hx] at hh
      rw [show F ((1 - t) • σ g.first + t • σ g.last) = (H ⟨_,hx⟩ : ℂ) from dite_eq_left hx] at hh
      exact hh.trans (hH₀base ⟨t,ht⟩ _ rfl).symm
    · have hh := hHrad ⟨z,hzf⟩ 1 ⟨z,hS₀sub (Or.inr hzf)⟩ ⟨z,Or.inr hzf⟩ rfl (by simp)
      simpa using hh
  have hsource : ∀ x : S, x.val ∈ b.sourceStar ↔ x.val ∉ S₀ := by
    intro x
    constructor
    · intro hx hzero
      rcases hzero with (hc | hbase') | hf'
      · have hmeet : x.val ∈ b.front ∩ range σ := hCurveCl ▸ ⟨hc,subset_closure hx⟩
        have hh : x.val ∈ frontier b.sourceStar := hBfront ▸ Or.inr hmeet.1
        exact (disjoint_frontier_iff_isOpen.mpr hBopen).le_bot ⟨hh,hx⟩
      · exact (disjoint_frontier_iff_isOpen.mpr hBopen).le_bot ⟨hBfront ▸ Or.inl hbase',hx⟩
      · exact (disjoint_frontier_iff_isOpen.mpr hBopen).le_bot ⟨hBfront ▸ Or.inr hf',hx⟩
    · intro hx
      have hcl : x.val ∈ closure b.sourceStar := x.property.resolve_left (fun hc ↦ hx (Or.inl (Or.inl hc)))
      by_contra hb'
      have hh : x.val ∈ frontier b.sourceStar := by rw [hBopen.frontier_eq];exact ⟨hcl,hb'⟩
      rw [hBfront] at hh
      exact hx (hh.elim (fun hb ↦ Or.inl (Or.inr hb)) Or.inr)
  let T₀ := range (fun z : Circle ↦ (z : ℂ)) ∪
    segment ℝ (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ) (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) ∪ ν
  change IsOpen γ at hγopen
  change frontier γ = segment ℝ (h ⟨σ g.first,⟨g.first,rfl⟩⟩ : ℂ)
    (h ⟨σ g.last,⟨g.last,rfl⟩⟩ : ℂ) ∪ ν at hγfront
  have htarget : ∀ y : ↥(range (fun z : Circle ↦ (z : ℂ)) ∪ closure γ),
      y.val ∈ γ ↔ y.val ∉ T₀ := by
    intro y
    constructor
    · intro hy hzero
      rcases hzero with (hc | hbase') | hf'
      · obtain ⟨t,ht⟩ := hc
        have hh := (hγsub hy).1
        rw [← ht] at hh
        have hh' : ‖(t : ℂ)‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hh
        exact (ne_of_lt hh') (Circle.norm_coe t)
      · exact (disjoint_frontier_iff_isOpen.mpr hγopen).le_bot ⟨hγfront ▸ Or.inl hbase',hy⟩
      · exact (disjoint_frontier_iff_isOpen.mpr hγopen).le_bot ⟨hγfront ▸ Or.inr hf',hy⟩
    · intro hy
      have hcl : y.val ∈ closure γ := y.property.resolve_left (fun hc ↦ hy (Or.inl (Or.inl hc)))
      by_contra hy'
      have hh : y.val ∈ frontier γ := by rw [hγopen.frontier_eq];exact ⟨hcl,hy'⟩
      rw [hγfront] at hh
      exact hy (hh.elim (fun hb ↦ Or.inl (Or.inr hb)) Or.inr)
  have hskeleton (x : S) : x.val ∈ S₀ ↔ (H x : ℂ) ∈ T₀ := by
    constructor
    · intro hx
      have hh : (H x : ℂ) = (H₀ ⟨x,hx⟩ : ℂ) :=
        (show F x = (H x : ℂ) from dite_eq_left x.property).symm.trans (hFH₀ x hx)
      rw [hh]
      exact (H₀ ⟨x,hx⟩).property
    · intro hx
      obtain ⟨z,hz⟩ := H₀.surjective ⟨H x,hx⟩
      have hh : H ⟨z,hS₀sub z.property⟩ = H x := by
        apply Subtype.ext
        exact (show F z = (H ⟨z,hS₀sub z.property⟩ : ℂ) from
          dite_eq_left (hS₀sub z.property)).symm.trans ((hFH₀ z z.property).trans (congrArg Subtype.val hz))
      have he := congrArg Subtype.val (H.injective hh)
      exact he ▸ z.property
  have hinterior (x : S) : x.val ∈ b.sourceStar ↔ (H x : ℂ) ∈ b.targetStar h := by
    rw [← hγ,hsource x,htarget (H x)]
    exact not_congr (hskeleton x)
  refine ⟨H.trans (Homeomorph.setCongr (show
      range (fun z : Circle ↦ (z : ℂ)) ∪ closure γ =
      range (fun z : Circle ↦ (z : ℂ)) ∪ closure (b.targetStar h) from by rw [hγ])),?_,hinterior,hbase,
      ?_,?_,?_,?_,hcoverage⟩
  · intro x
    change (H x : ℂ) = b.patchMap h x
    exact (show F x = (H x : ℂ) from dite_eq_left x.property).symm.trans (hpatch x x.property).symm
  · rw [← hγ]
    exact hγne
  · exact hγ ▸ hγopen
  · rw [← hγ]
    exact fun z hz ↦ (hγsub hz).1
  · rw [← hγ,hfrontImage]
    exact hγfront

end HolomorphicAnosov.Topology.Plane

