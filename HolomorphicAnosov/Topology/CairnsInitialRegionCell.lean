import HolomorphicAnosov.Topology.CairnsStarDiskCell
import HolomorphicAnosov.Topology.CairnsStarBaseFrontier
import HolomorphicAnosov.Topology.CairnsOppositeCellIntersection
import HolomorphicAnosov.Topology.CairnsTwoDiskCells
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The union of the two geometric initial stars and their common open chord
is a disk cell whose frontier is exactly the two outer fronts. Opposite sector
frontier bounds show that the two closed cells meet precisely on the base.
Their disk charts glue along that base by the finite two-cell theorem. The
fronts meet the base only at its endpoints, so removing the open seam leaves
exactly the two fronts. This is the initial geometric invariant in Cairns §4(B). -/
theorem cairns_initial_region_cell
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (hchord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hop₁ : IsOpen d.firstStar.sector) (hop₂ : IsOpen d.secondStar.sector)
    (hdisj : Disjoint d.firstStar.sector d.secondStar.sector) :
    let A := (d.stage h).region
    A.Nonempty ∧ IsOpen A ∧ A ⊆ a ∧
      Nonempty (A ≃ₜ Metric.ball (0 : ℂ) 1) ∧
      Nonempty (Circle ≃ₜ frontier A) ∧
      frontier A = d.firstStar.front ∪ d.secondStar.front ∧
      closure A = closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar ∧
      closure d.firstStar.sourceStar ∩ closure d.secondStar.sourceStar =
        segment ℝ (σ p) (σ q) := by
  intro A
  let U := d.firstStar.sourceStar
  let V := d.secondStar.sourceStar
  let B := segment ℝ (σ p) (σ q)
  let L := d.firstStar.front
  let M := d.secondStar.front
  have hg2first : d.secondGap.first = q := by
    change Circle.exp d.secondGap.start = q
    rw [d.second_start]
    exact d.last_eq
  have hg2last : d.secondGap.last = p := by
    change Circle.exp d.secondGap.stop = p
    rw [d.second_stop,Circle.periodic_exp]
    exact d.first_eq
  have hUne : U.Nonempty := h₁.1
  have hVne : V.Nonempty := h₂.1
  have hUfront : frontier U = B ∪ L := by
    simpa only [d.first_eq,d.last_eq] using h₁.2.2.2.1
  have hVfront : frontier V = B ∪ M := by
    simpa only [hg2first,hg2last,segment_symm] using h₂.2.2.2.1
  have hBU : B ⊆ frontier U := fun z hz ↦ hUfront ▸ Or.inl hz
  have hBV : B ⊆ frontier V := fun z hz ↦ hVfront ▸ Or.inl hz
  have hLM : (σ '' d.firstGap.closedArc) ∩ (σ '' d.secondGap.closedArc) ⊆ B := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := hz.1
    obtain ⟨t,ht,he⟩ := hz.2
    have hts : t = s := hσ.injective he
    subst t
    have hm := (CairnsCircleGap.opposite_parameter_cover_inter d.firstGap d.secondGap
      d.second_start d.second_stop (hg2first.trans d.last_eq.symm)
      (hg2last.trans d.first_eq.symm)).2
    rw [(CairnsCircleGap.parameter_embedding_range d.firstGap).2.1,
      (CairnsCircleGap.parameter_embedding_range d.secondGap).2.1] at hm
    have hs' : s ∈ {d.firstGap.first,d.firstGap.last} := hm ▸ (show
      s ∈ d.firstGap.closedArc ∩ d.secondGap.closedArc from ⟨hs,ht⟩)
    rcases hs' with rfl | rfl
    · simpa only [d.first_eq] using (left_mem_segment ℝ (σ p) (σ q))
    · simpa only [d.last_eq] using (right_mem_segment ℝ (σ p) (σ q))
  have hUV : closure U ∩ closure V = B := by
    apply opposite_cells_closure_intersection U V d.firstStar.sector d.secondStar.sector B
      (σ '' d.firstGap.closedArc) (σ '' d.secondGap.closedArc) hop₁ hop₂ hdisj
      h₁.2.2.1 h₂.2.2.1
    · simpa only [d.first_eq,d.last_eq] using d.firstStar.frontier_subset
    · simpa only [hg2first,hg2last,segment_symm] using d.secondStar.frontier_subset
    · exact hLM
    · exact hBU.trans frontier_subset_closure
    · exact hBV.trans frontier_subset_closure
  have hfrontUV : frontier U ∩ frontier V = B := by
    apply Subset.antisymm
    · intro z hz
      exact hUV ▸ (show z ∈ closure U ∩ closure V from
        ⟨frontier_subset_closure hz.1,frontier_subset_closure hz.2⟩)
    · exact fun z hz ↦ ⟨hBU hz,hBV hz⟩
  have hcontact₁ := cairns_star_contact_notMem_base hσ d.firstStar ha
    (by simpa only [d.first_eq,d.last_eq] using hchord)
  have hcontact₂ := cairns_star_contact_notMem_base hσ d.secondStar ha
    (by simpa only [hg2first,hg2last,openSegment_symm] using hchord)
  have hproperU : B ≠ frontier U := by
    intro he
    apply hcontact₁
    have hPfront : d.firstStar.contact ∈ frontier U := hUfront ▸
      Or.inr h₁.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    have hh : d.firstStar.contact ∈ B := he.symm ▸ hPfront
    simpa only [d.first_eq,d.last_eq] using hh
  have hproperV : B ≠ frontier V := by
    intro he
    apply hcontact₂
    have hPfront : d.secondStar.contact ∈ frontier V := hVfront ▸
      Or.inr h₂.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    have hh : d.secondStar.contact ∈ B := he.symm ▸ hPfront
    simpa only [hg2first,hg2last,segment_symm] using hh
  obtain ⟨hUdisk,hUcircle,⟨GU,hGUi,hGUf⟩,hUext⟩ := cairns_geometric_star_disk_cell hσ d.firstStar h h₁
  obtain ⟨hVdisk,hVcircle,⟨GV,hGVi,hGVf⟩,hVext⟩ := cairns_geometric_star_disk_cell hσ d.secondStar h h₂
  have hcellAmbient (W : Set ℂ) (G : closure W ≃ₜ Metric.closedBall (0 : ℂ) 1)
      (hi : G '' {z : closure W | (z : ℂ) ∈ W} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1})
      (hf : G '' {z : closure W | (z : ℂ) ∈ frontier W} =
        {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1}) :
      ∃ H : closure W ≃ₜ Metric.closedBall (0 : ℂ) 1,
        H '' {z | (z : ℂ) ∈ W} = {w | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1} ∧
        H '' {z | (z : ℂ) ∈ frontier W} = {w | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1} := by
    refine ⟨G,?_,?_⟩
    · have hh := congrArg (Set.image (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ)) hi
      change Subtype.val '' G '' {z : closure W | (z : ℂ) ∈ W} = Metric.ball (0 : ℂ) 1
      rw [hh]
      exact Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using
        (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall 0 1))
    · have hh := congrArg (Set.image (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ)) hf
      change Subtype.val '' G '' {z : closure W | (z : ℂ) ∈ frontier W} = Metric.sphere (0 : ℂ) 1
      rw [hh]
      exact Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using
        (Metric.sphere_subset_closedBall : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall 0 1))
  have hpq : σ p ≠ σ q := by
    intro he
    have hh := (CairnsCircleGap.parameter_embedding_range d.firstGap).1.injective
      (show d.firstGap.parameter 0 = d.firstGap.parameter 1 from by
        rw [(CairnsCircleGap.parameter_embedding_range d.firstGap).2.2.1,
          (CairnsCircleGap.parameter_embedding_range d.firstGap).2.2.2,d.first_eq,d.last_eq]
        exact hσ.injective he)
    exact zero_ne_one hh
  have harc : ∃ b : unitInterval → ℂ,
      Topology.IsEmbedding b ∧ range b = B ∧ b 0 = σ p ∧ b 1 = σ q := by
    let b : unitInterval → ℂ := fun t ↦ AffineMap.lineMap (σ p) (σ q) (t : ℝ)
    have hbc : Continuous b := by fun_prop
    have hbi : Function.Injective b := by
      intro s t he
      apply Subtype.ext
      exact AffineMap.lineMap_injective ℝ hpq he
    refine ⟨b,hbc.isClosedEmbedding hbi |>.isEmbedding,?_,by simp [b],by simp [b]⟩
    change range b = segment ℝ (σ p) (σ q)
    rw [segment_eq_image_lineMap]
    exact Set.range_comp _ _ |>.trans (by rw [Subtype.range_coe])
  obtain ⟨hAopen,hAcl,hAfront,G,hGi,hGf⟩ := cairns_two_disk_cells U V B (σ p) (σ q)
    (hcellAmbient U GU hGUi hGUf) (hcellAmbient V GV hGVi hGVf) hUext hVext
    hpq harc ⟨hBU,hproperU⟩ ⟨hBV,hproperV⟩ hfrontUV hUV
  have hseam : B \ {σ p,σ q} = openSegment ℝ (σ p) (σ q) := by
    ext z
    constructor
    · intro hz
      exact mem_openSegment_of_ne_left_right (fun he ↦ hz.2 (Or.inl he.symm))
        (fun he ↦ hz.2 (Or.inr he.symm)) hz.1
    · intro hz
      refine ⟨openSegment_subset_segment ℝ _ _ hz,?_⟩
      rintro (rfl | rfl)
      · exact hpq (left_mem_openSegment_iff.mp hz)
      · exact hpq (right_mem_openSegment_iff.mp hz)
  have hAdef : A = U ∪ V ∪ (B \ {σ p,σ q}) := by rw [hseam];rfl
  have hAf : frontier A = (frontier U ∪ frontier V) \ (B \ {σ p,σ q}) := by
    rw [hAdef]; exact hAfront
  have hLbase := cairns_geometric_star_front_base_intersection hσ d.firstStar h h₁
  have hMbase := cairns_geometric_star_front_base_intersection hσ d.secondStar h h₂
  have hLf : L ∩ B = {σ p,σ q} := by simpa only [d.first_eq,d.last_eq] using hLbase
  have hMf : M ∩ B = {σ p,σ q} := by
    simpa only [hg2first,hg2last,segment_symm,pair_comm] using hMbase
  have hfront : frontier A = L ∪ M := by
    rw [hAf,hUfront,hVfront]
    ext z
    constructor
    · rintro ⟨hz,hznot⟩
      have hBend (hzB : z ∈ B) : z ∈ L := by
        have he : z ∈ ({σ p,σ q} : Set ℂ) := by
          by_contra hn
          exact hznot ⟨hzB,hn⟩
        have hh : z ∈ L ∩ B := hLf.symm ▸ he
        exact hh.1
      rcases hz with (hzB | hzL) | (hzB | hzM)
      · exact Or.inl (hBend hzB)
      · exact Or.inl hzL
      · exact Or.inl (hBend hzB)
      · exact Or.inr hzM
    · intro hz
      refine ⟨hz.elim (fun hz ↦ Or.inl (Or.inr hz)) (fun hz ↦ Or.inr (Or.inr hz)),?_⟩
      rintro ⟨hzB,hznot⟩
      exact hznot (hz.elim (fun hz ↦ hLf ▸ ⟨hz,hzB⟩) (fun hz ↦ hMf ▸ ⟨hz,hzB⟩))
  have hAsub : A ⊆ a := by
    have hUa := h₁.2.2.1.trans (cairns_star_sector_geometry hσ ha d.firstStar).2.2.2
    have hVa := h₂.2.2.1.trans (cairns_star_sector_geometry hσ ha d.secondStar).2.2.2
    exact union_subset (union_subset hUa hVa) hchord
  have hAR : A ⊆ closure U ∪ closure V := by
    intro z hz
    exact (show closure A = closure U ∪ closure V from hAdef.symm ▸ hAcl) ▸ subset_closure hz
  have hGint (x : ↥(closure U ∪ closure V)) : (x : ℂ) ∈ A ↔ (G x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [hAdef]
    change x ∈ {x : ↥(closure U ∪ closure V) | (x : ℂ) ∈ U ∪ V ∪ (B \ {σ p,σ q})} ↔
      G x ∈ {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.ball (0 : ℂ) 1}
    rw [← hGi]
    exact G.injective.mem_set_image.symm
  have hGF (x : ↥(closure U ∪ closure V)) : (x : ℂ) ∈ frontier A ↔ (G x : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [hAf]
    change x ∈ {x : ↥(closure U ∪ closure V) | (x : ℂ) ∈
      (frontier U ∪ frontier V) \ (B \ {σ p,σ q})} ↔
      G x ∈ {w : Metric.closedBall (0 : ℂ) 1 | (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1}
    rw [← hGf]
    exact G.injective.mem_set_image.symm
  refine ⟨hUne.mono (fun z hz ↦ Or.inl (Or.inl hz)),hAdef.symm ▸ hAopen,hAsub,
    ⟨homeomorphRestrictSubsets _ _ _ _ hAR Metric.ball_subset_closedBall G hGint⟩,
    ⟨(homeomorphRestrictSubsets _ _ _ _ ?_ Metric.sphere_subset_closedBall G hGF).symm⟩,
    hfront,hAdef.symm ▸ hAcl,hUV⟩
  exact frontier_subset_closure.trans (by rw [hAdef,hAcl])

end HolomorphicAnosov.Topology.Plane
