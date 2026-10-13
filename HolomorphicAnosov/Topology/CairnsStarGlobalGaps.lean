import HolomorphicAnosov.Topology.CairnsStarTargetConvexity

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- A local front-gap pair is a genuine global contact gap whenever global
contacts on the star's original closed arc are exactly its front contacts.
The resulting chord lies on the star front and inside the original region.
The source and front gap-pair correspondence transfers the chord formula. -/
theorem cairns_star_pair_global_gap
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h)
    (T : Set Circle)
    (hlocal : ∀ t ∈ g.closedArc, t ∈ T ↔ σ t ∈ b.front ∩ range σ)
    (u v : I) (hp : (σ (g.parameter u),σ (g.parameter v)) ∈
      gapPairs (fun t ↦ σ (g.parameter t)) (b.front ∩ range σ)) :
    ∃ gg : CairnsCircleGap, gg.IsGapOf T ∧
      gg.first = g.parameter u ∧ gg.last = g.parameter v ∧
      openSegment ℝ (σ gg.first) (σ gg.last) ⊆ b.front ∩ a := by
  obtain ⟨l,r,hlr,hl,hr,hmissing,he⟩ := hp
  have hu : u = l := (CairnsCircleGap.parameter_embedding_range g).1.injective
    (hσ.injective (congrArg Prod.fst he))
  have hv : v = r := (CairnsCircleGap.parameter_embedding_range g).1.injective
    (hσ.injective (congrArg Prod.snd he))
  subst u; subst v
  let gg := g.subgap l r hlr
  have hparam (t : I) : g.parameter t ∈ g.closedArc :=
    (CairnsCircleGap.parameter_embedding_range g).2.1 ▸ mem_range_self t
  have hgg : gg.IsGapOf T := by
    apply CairnsCircleGap.isGapOf_of_endpoints _ _
      ((hlocal _ (hparam l)).mpr hl) ((hlocal _ (hparam r)).mpr hr)
    rw [CairnsCircleGap.subgap_openArc]
    rintro _ ⟨t,⟨hlt,htr⟩,rfl⟩ htT
    exact hmissing t hlt htr ((hlocal _ (hparam t)).mp htT)
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,hrest⟩
  have hpairFront : (σ (g.parameter l),σ (g.parameter r)) ∈
      gapPairs (fun t ↦ (qs t : ℂ)) (b.front ∩ range σ) := by
    rw [← hpairs]
    exact ⟨l,r,hlr,hl,hr,hmissing,rfl⟩
  obtain ⟨l',r',hlr',hl',hr',hmissing',he'⟩ := hpairFront
  have hel := congrArg Prod.fst he'
  have her := congrArg Prod.snd he'
  dsimp only at hel her
  obtain ⟨hchord,hchorda,hchordc⟩ := hchords l' r' hlr' hl' hr' hmissing'
  refine ⟨gg,hgg,rfl,rfl,?_⟩
  change openSegment ℝ (σ (g.parameter l)) (σ (g.parameter r)) ⊆ _
  rw [hel,her]
  intro z hz
  refine ⟨?_,hchorda hz⟩
  rw [← hchord] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  exact (qs t).property

/-- Every noncontact point of a star front is on a global complementary chord,
under the same local-contact compatibility. The existing front-component
coverage provides its affine coordinate and the preceding pair theorem
provides the actual global gap. -/
theorem cairns_star_front_global_gap_coverage
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h)
    (T : Set Circle)
    (hlocal : ∀ t ∈ g.closedArc, t ∈ T ↔ σ t ∈ b.front ∩ range σ) :
    ∀ z ∈ b.front, z ∉ range σ → ∃ gg : CairnsCircleGap,
      gg.IsGapOf T ∧ z ∈ openSegment ℝ (σ gg.first) (σ gg.last) ∧
        openSegment ℝ (σ gg.first) (σ gg.last) ⊆ b.front ∩ a := by
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,
    hcompμ,hcompL,hrest⟩
  intro z hz hzc
  have hz' : z ∈ b.front \ (b.front ∩ range σ) := ⟨hz,fun hh ↦ hzc hh.2⟩
  obtain ⟨l,r,hlr,hl,hr,hmissing,hcomp⟩ := hcompL z hz'
  have hpair : ((qs l : ℂ),(qs r : ℂ)) ∈ gapPairs (fun t ↦ σ (g.parameter t))
      (b.front ∩ range σ) := by
    rw [hpairs]
    exact ⟨l,r,hlr,hl,hr,hmissing,rfl⟩
  obtain ⟨u,v,huv,hu,hv,hmissinguv,he⟩ := hpair
  have hch := (hchords l r hlr hl hr hmissing).1
  have hzch : z ∈ openSegment ℝ (qs l : ℂ) (qs r : ℂ) := by
    rw [← hch,← hcomp]
    exact mem_connectedComponentIn hz'
  have hbu : StarGeometry b h := ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,hcompμ,hcompL,hrest⟩
  obtain ⟨gg,hgg,hgf,hgl,hsub⟩ := cairns_star_pair_global_gap hσ b h hbu T hlocal u v
    ⟨u,v,huv,hu,hv,hmissinguv,rfl⟩
  refine ⟨gg,hgg,?_,hsub⟩
  have hel := congrArg Prod.fst he
  have her := congrArg Prod.snd he
  dsimp only at hel her
  rw [hgf,hgl,← hel,← her]
  exact hzch

/-- The literal radial patch is affine on every front-gap chord. The existing
skeleton extension prescribes that affine value for the same endpoint pair;
its radial extension agrees with it on the front by the t=1 formula. -/
theorem cairns_star_patch_front_gap_affine
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (_hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h)
    (u v : I) (hp : (σ (g.parameter u),σ (g.parameter v)) ∈
      gapPairs (fun t ↦ σ (g.parameter t)) (b.front ∩ range σ)) :
    ∀ t : I, b.patchMap h ((1-(t : ℝ)) • σ (g.parameter u) + (t : ℝ) • σ (g.parameter v)) =
      (1-(t : ℝ)) • (h ⟨σ (g.parameter u),⟨g.parameter u,rfl⟩⟩ : ℂ) +
        (t : ℝ) • (h ⟨σ (g.parameter v),⟨g.parameter v,rfl⟩⟩ : ℂ) := by
  classical
  have hb' := hb
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,
    hcompμ,hcompL,hcount,ds,hds,hdcont,hdpos,ν,H₀,hH₀front,hH₀curve,
    hH₀chord,hH₀base,hνc,hνcurve,hγne,hγopen,hγfront,hγsweep,hγsub,hγunique,
    qt,hqt0,hqt1,hqtH,hpairtarget,hchordtarget,dt,hdt,hdtcont,hdtpos,H,hHcurve,hHrad⟩
  have hpfront : (σ (g.parameter u),σ (g.parameter v)) ∈
      gapPairs (fun t ↦ (qs t : ℂ)) (b.front ∩ range σ) := hpairs ▸ hp
  obtain ⟨l,r,hlr,hl,hr,hmissing,he⟩ := hpfront
  have hel : σ (g.parameter u) = (qs l : ℂ) := congrArg Prod.fst he
  have her : σ (g.parameter v) = (qs r : ℂ) := congrArg Prod.snd he
  have hseg : segment ℝ (σ (g.parameter u)) (σ (g.parameter v)) ⊆ b.front := by
    have hu : σ (g.parameter u) ∈ b.front := hel.symm ▸ hl.1
    have hv : σ (g.parameter v) ∈ b.front := her.symm ▸ hr.1
    apply (openSegment_subset_iff_segment_subset hu hv).mp
    rw [hel,her,← (hchords l r hlr hl hr hmissing).1]
    rintro _ ⟨t,ht,rfl⟩;exact (qs t).property
  intro t
  let z := (1-(t : ℝ)) • σ (g.parameter u) + (t : ℝ) • σ (g.parameter v)
  have hz : z ∈ b.front := hseg ⟨1-t,t,sub_nonneg.mpr t.property.2,t.property.1,
    sub_add_cancel _ _,rfl⟩
  let S₀ := range σ ∪ segment ℝ (σ g.first) (σ g.last) ∪ b.front
  let F₀ : ℂ → ℂ := fun z ↦ if hz : z ∈ S₀ then (H₀ ⟨z,hz⟩ : ℂ) else 0
  have hcov := cairns_front_coordinate_coverage b qs hpairs
    (fun l r hlr hl hr hg ↦ (hchords l r hlr hl hr hg).1) hcompL
  have hfrontEq : ∀ z ∈ b.front, b.frontMap h z = F₀ z := by
    apply cairns_frontMap_eq_of_affine b h F₀ hcov
    · intro z hz hzc
      rw [show F₀ z = (H₀ ⟨z,Or.inr hz⟩ : ℂ) from dite_eq_left (Or.inr hz)]
      exact hH₀curve _ hzc
    · intro z hz w hw
      rw [show F₀ z = (H₀ ⟨z,Or.inr hz⟩ : ℂ) from dite_eq_left (Or.inr hz)]
      exact hH₀chord ⟨σ (g.parameter w.1),⟨g.parameter w.1,rfl⟩⟩
        ⟨σ (g.parameter w.2.1),⟨g.parameter w.2.1,rfl⟩⟩ w.2.2 _ (hpairs ▸ hw.1) hw.2
  have hradEq : b.patchMap h z = b.frontMap h z := by
    unfold StarChoice.patchMap
    split_ifs with hc hm hw
    · simp only [StarChoice.frontMap,dite_eq_left hc]
    · have hh := hds ⟨z,hz⟩
      have hn := Circle.norm_coe (ds ⟨z,hz⟩)
      have hhzero : ((ds ⟨z,hz⟩ : Circle) : ℂ) = 0 := by
        simpa only [show z - b.center = 0 from sub_eq_zero.mpr hm,
          norm_zero,Complex.ofReal_zero,div_zero] using hh
      rw [hhzero,norm_zero] at hn
      exact (zero_ne_one hn).elim
    · have hcoord := Classical.choose_spec hw
      have hnonzero : z ≠ b.center := hm
      have hu := hBunique z (frontier_subset_closure (hBfront ▸ Or.inr hz)) hnonzero
      have hchosen : ((⟨(Classical.choose hw).1,hcoord.1⟩ : b.front),(Classical.choose hw).2) =
          ((⟨z,hz⟩ : b.front),(1 : I)) := hu.unique hcoord.2 (by simp)
      have htone : (Classical.choose hw).2 = (1 : I) := congrArg Prod.snd hchosen
      have hpoint : (Classical.choose hw).1 = z := congrArg (fun w : b.front × I ↦ (w.1 : ℂ)) hchosen
      simp only [htone,hpoint]
      simp
    · exact (hw ⟨(z,1),hz,by simp⟩).elim
  rw [hradEq,hfrontEq z hz]
  rw [show F₀ z = (H₀ ⟨z,Or.inr hz⟩ : ℂ) from dite_eq_left (Or.inr hz)]
  exact hH₀chord ⟨σ (g.parameter u),⟨g.parameter u,rfl⟩⟩
    ⟨σ (g.parameter v),⟨g.parameter v,rfl⟩⟩ t _ (hpairs ▸ hp) rfl

/-- A missing original-circle contact on the star arc lies in a local front
gap, and hence in an actual global gap with its chord on the front. Use the
provider's component parametrization of the original arc minus its contacts;
its component contains the point itself, so the interval parameters strictly
surround its parameter. -/
theorem cairns_star_missing_contact_global_gap
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (hσ : Topology.IsEmbedding σ) (b : StarChoice σ a g)
    (h : range σ ≃ₜ Circle) (hb : StarGeometry b h)
    (T : Set Circle)
    (hlocal : ∀ t ∈ g.closedArc, t ∈ T ↔ σ t ∈ b.front ∩ range σ)
    (t : Circle) (ht : t ∈ g.closedArc) (htT : t ∉ T) :
    ∃ gg : CairnsCircleGap, gg.IsGapOf T ∧ t ∈ gg.openArc ∧
      openSegment ℝ (σ gg.first) (σ gg.last) ⊆ b.front ∩ a ∧
      (∀ t : I, b.patchMap h ((1-(t : ℝ)) • σ gg.first + (t : ℝ) • σ gg.last) =
        (1-(t : ℝ)) • (h ⟨σ gg.first,⟨gg.first,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ gg.last,⟨gg.last,rfl⟩⟩ : ℂ)) := by
  have hb' := hb
  rcases hb with ⟨hBne,hBopen,hBsub,hBfront,hLc,hBsweep,hBstar,hBunique,
    hCclosed,hCsub,hD₁,hD₂,hPC,hCurveCl,qs,hqs0,hqs1,horder,hpairs,hchords,
    hcompμ,hrest⟩
  have htC : σ t ∉ b.front ∩ range σ := fun hh ↦ htT ((hlocal t ht).mpr hh)
  have htμ : σ t ∈ σ '' range g.parameter :=
    ⟨t,(CairnsCircleGap.parameter_embedding_range g).2.1.symm ▸ ht,rfl⟩
  obtain ⟨l,r,hlr,hl,hr,hmissing,hcomp⟩ := hcompμ (σ t) ⟨htμ,htC⟩
  have htcomp := mem_connectedComponentIn (show σ t ∈ (σ '' range g.parameter) \ (b.front ∩ range σ) from
    ⟨htμ,htC⟩)
  rw [hcomp] at htcomp
  obtain ⟨s,⟨hls,hsr⟩,he⟩ := htcomp
  have hgt : g.parameter s = t := hσ.injective he
  obtain ⟨gg,hgg,hgf,hgl,hch⟩ := cairns_star_pair_global_gap hσ b h hb' T hlocal l r
    ⟨l,r,hlr,hl,hr,hmissing,rfl⟩
  let v := g.subgap l r hlr
  have hv : v.IsGapOf T := by
    apply CairnsCircleGap.isGapOf_of_endpoints v T
      ((hlocal _ ((CairnsCircleGap.parameter_embedding_range g).2.1 ▸ mem_range_self l)).mpr hl)
      ((hlocal _ ((CairnsCircleGap.parameter_embedding_range g).2.1 ▸ mem_range_self r)).mpr hr)
    rw [CairnsCircleGap.subgap_openArc]
    rintro _ ⟨u,⟨hlu,hur⟩,rfl⟩ hu
    exact hmissing u hlu hur ((hlocal _
      ((CairnsCircleGap.parameter_embedding_range g).2.1 ▸ mem_range_self u)).mp hu)
  refine ⟨v,hv,?_,?_,?_⟩
  · rw [CairnsCircleGap.subgap_openArc]
    exact ⟨s,⟨hls,hsr⟩,hgt⟩
  · change openSegment ℝ (σ (g.parameter l)) (σ (g.parameter r)) ⊆ _
    simpa only [hgf,hgl] using hch

  · exact cairns_star_patch_front_gap_affine hσ b h hb' l r
      ⟨l,r,hlr,hl,hr,hmissing,rfl⟩

/-- Complementary gaps that share a point have the same open arc and the same
unordered endpoint pair. This removes dependence on angular representatives
when matching the literal recurrence labels to front-gap coordinates. -/
theorem cairns_gaps_equal_of_common_point (T : Set Circle)
    (g v : CairnsCircleGap) (hg : g.IsGapOf T) (hv : v.IsGapOf T)
    (t : Circle) (htg : t ∈ g.openArc) (htv : t ∈ v.openArc) :
    g.openArc = v.openArc ∧ ({g.first,g.last} : Set Circle) = {v.first,v.last} := by
  obtain ⟨_,_,x,hx,hgx⟩ := hg
  obtain ⟨_,_,y,hy,hvy⟩ := hv
  have heq : g.openArc = v.openArc := by
    have ht1 : t ∈ connectedComponentIn Tᶜ x := hgx.symm ▸ htg
    have ht2 : t ∈ connectedComponentIn Tᶜ y := hvy.symm ▸ htv
    exact hgx.symm.trans ((connectedComponentIn_eq ht1).trans
      ((connectedComponentIn_eq ht2).symm.trans hvy))
  refine ⟨heq,?_⟩
  have hh := congrArg frontier heq
  simpa only [CairnsCircleGap.openArc,
    cairns_exp_interval_frontier _ _ g.start_lt_stop g.shorter_than_turn.le,
    cairns_exp_interval_frontier _ _ v.start_lt_stop v.shorter_than_turn.le,
    CairnsCircleGap.first,CairnsCircleGap.last] using hh

end HolomorphicAnosov.Topology.Plane
