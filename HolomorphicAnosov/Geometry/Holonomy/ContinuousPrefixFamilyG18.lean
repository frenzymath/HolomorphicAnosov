import HolomorphicAnosov.Geometry.FinitePlaqueHolonomy

/-! Continuous representatives of finite stable prefix holonomy. (Ghys, Proposition 3.1) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u v

/-- Any full-source family of transports in a fixed product box is jointly continuous when its receiving stable coordinate is continuous.    The actual source plaque inverse supplies a single fixed transverse-coordinate map. -/
theorem fixed_source_plaque_transport_continuous_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (a₀ : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk t)
    (x : M) (hx : ((F.box b).chart (a₀,w₀)).val = x)
    {R : Type*} [TopologicalSpace R] (v : R → FoliationCoordinateDisk s) (hv : Continuous v)
    (y : R → M) (h : ∀ r, LocalPlaqueTransport F x (y r))
    (hh : ∀ r, (h r).box = b ∧ (h r).first = a₀ ∧ (h r).second = v r ∧
      (h r).transverse = w₀ ∧ (h r).map.source = {z | ∃ w : FoliationCoordinateDisk t,
        ((F.box b).chart (a₀,w)).val = z.val}) :
    ContinuousOn (fun p : R × F.ULeaf x ↦ ((h p.1).map p.2).val)
      (univ ×ˢ {z | ∃ w : FoliationCoordinateDisk t,
        ((F.box b).chart (a₀,w)).val = z.val}) := by
  let W : Set (F.ULeaf x) := {z | ∃ w : FoliationCoordinateDisk t,
    ((F.box b).chart (a₀,w)).val = z.val}
  have hlabel : F.unstableLabel b a₀ = Quotient.mk F.unstablePartition x :=
    (F.unstable_label b a₀ w₀).symm.trans (congrArg (Quotient.mk F.unstablePartition) hx)
  let j : FoliationCoordinateDisk t → F.ULeaf x := fun w ↦
    ⟨((F.box b).chart (a₀,w)).val,(F.unstable_label b a₀ w).trans hlabel⟩
  have hj : IsOpenEmbedding j := unstable_plaque_open_at_class_g10 F b a₀ _ hlabel
  let : Nonempty (FoliationCoordinateDisk t) := ⟨w₀⟩
  let e := hj.toOpenPartialHomeomorph j
  have hW : W = e.target := by
    rw [show e.target = Set.range j by simp [e]]
    ext z
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨w,rfl⟩
  have hcoord (z : F.ULeaf x) (hz : z ∈ W) :
      ((F.box b).chart (a₀,e.symm z)).val = z.val := by
    exact congrArg Subtype.val (e.right_inv (hW ▸ hz))
  have hecont : ContinuousOn (fun p : R × F.ULeaf x ↦
      e.symm p.2) (univ ×ˢ W) :=
    e.symm.continuousOn.comp continuous_snd.continuousOn (fun p hp ↦ by
      change p.2 ∈ e.target
      exact hW ▸ hp.2)
  have hcont := continuous_subtype_val.comp_continuousOn
    ((F.box b).chart.continuous.comp_continuousOn ((hv.comp continuous_fst).continuousOn.prodMk hecont))
  apply hcont.congr
  intro p hp
  have heq := (h p.1).coordinate_map p.2 (e.symm p.2)
    ((hh p.1).2.2.2.2.symm ▸ hp.2)
  rw [(hh p.1).1,(hh p.1).2.1,(hh p.1).2.2.1] at heq
  exact heq (hcoord p.2 hp.2)

/-- The full-source transports in one product box have jointly continuous ambient evaluation.    Their source is the same original unstable plaque. -/
theorem one_box_plaque_transport_continuous_family_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (a₀ : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk t) :
    let x := fun a : FoliationCoordinateDisk s ↦ ((F.box b).chart (a,w₀)).val
    let W : Set (F.ULeaf (x a₀)) := {z | ∃ w : FoliationCoordinateDisk t,
      ((F.box b).chart (a₀,w)).val = z.val}
    ∃ h : ∀ a, LocalPlaqueTransport F (x a₀) (x a),
      (∀ a, (h a).box = b ∧ (h a).first = a₀ ∧ (h a).second = a ∧
        (h a).transverse = w₀ ∧ (h a).map.source = W) ∧
      ContinuousOn (fun p : FoliationCoordinateDisk s × F.ULeaf (x a₀) ↦
        ((h p.1).map p.2).val) (univ ×ˢ W) := by
  classical
  intro x W
  choose h hb hf hs ht hsource using fun a ↦
    local_plaque_transport_of_box F b a₀ a w₀ (x a₀) (x a) rfl rfl
  refine ⟨h,fun a ↦ ⟨hb a,hf a,hs a,ht a,hsource a⟩,?_⟩
  exact fixed_source_plaque_transport_continuous_g1 F b a₀ w₀ (x a₀) rfl
    id continuous_id x h (fun a ↦ ⟨hb a,hf a,hs a,ht a,hsource a⟩)

/-- A continuous curve in a stable coordinate disk gives actual prefix representatives on the whole fixed unstable plaque, with continuous ambient evaluation and the exact product-box formula. -/
theorem one_box_stable_curve_continuous_prefixes_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (w₀ : FoliationCoordinateDisk t)
    (p : C(unitInterval,FoliationCoordinateDisk s)) :
    letI := F.stableTopology (F.stableLabel b w₀)
    let j : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition
      (F.stableLabel b w₀) := fun a ↦ ⟨((F.box b).chart (a,w₀)).val,F.stable_label b a w₀⟩
    ∃ γ : Path (j (p 0)) (j (p 1)), (∀ r, γ r = j (p r)) ∧
      ∃ (h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r)
        (W : Set (F.ULeaf (γ 0).val)),
        IsOpen W ∧ F.uPoint (γ 0).val ∈ W ∧
        W = {z | ∃ w : FoliationCoordinateDisk t, ((F.box b).chart (p 0,w)).val = z.val} ∧
        (∀ r, (h r).map.source = W) ∧
        ContinuousOn (fun a : unitInterval × F.ULeaf (γ 0).val ↦
          ((h a.1).map a.2).val) (univ ×ˢ W) ∧
        ∀ (r : unitInterval) (z : F.ULeaf (γ 0).val) (w : FoliationCoordinateDisk t),
          z ∈ W → ((F.box b).chart (p 0,w)).val = z.val →
            ((h r).map z).val = ((F.box b).chart (p r,w)).val := by
  classical
  let := F.stableTopology (F.stableLabel b w₀)
  intro j
  let γ : Path (j (p 0)) (j (p 1)) := {
    toFun := fun r ↦ j (p r)
    continuous_toFun := (F.stable_plaque b w₀).continuous.comp p.continuous
    source' := rfl
    target' := rfl }
  obtain ⟨e,he,hcont⟩ := one_box_plaque_transport_continuous_family_g1 F b (p 0) w₀
  let h (r : unitInterval) : PathHolonomyRepresentative F γ 0 r := {
    toPointedLeafHomeomorph := (e (p r)).toPointedLeafHomeomorph
    chain := PlaqueChainAlong.single (F := F) (γ := γ) 0 r bot_le (e (p r)) (by
      intro v hv0 hvr
      refine ⟨p v,?_⟩
      rw [(he (p r)).1,(he (p r)).2.2.2.1]
      rfl) }
  let W : Set (F.ULeaf (γ 0).val) := {z | ∃ w : FoliationCoordinateDisk t,
    ((F.box b).chart (p 0,w)).val = z.val}
  have hs (r : unitInterval) : (h r).map.source = W := (he (p r)).2.2.2.2
  refine ⟨γ,fun _ ↦ rfl,h,W,?_,?_,rfl,hs,?_,?_⟩
  · rw [← hs 0]
    exact (h 0).map.open_source
  · rw [← hs 0]
    exact (h 0).source_point
  · exact hcont.comp (p.continuous.comp continuous_fst |>.prodMk continuous_snd).continuousOn
      (fun a ha ↦ ⟨mem_univ _,ha.2⟩)
  · intro r z w hz hw
    have hc := (e (p r)).coordinate_map z w ((hs r).symm ▸ hz)
    rw [(he (p r)).1,(he (p r)).2.1,(he (p r)).2.2.1] at hc
    exact hc hw

/-- On a closed path segment contained in one stable plaque, the full-source plaque representatives form a continuous family on one fixed initial plaque.    At the initial time their restriction to that plaque is exactly the identity. -/
theorem stable_segment_continuous_plaque_family_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b) (k : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hsegment : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box k).chart (z,w)).val = (γ r).val) :
    ∃ (W : Set (F.ULeaf (γ a).val))
      (e : ∀ r : Set.Icc a b, LocalPlaqueTransport F (γ a).val (γ r.val).val),
      IsOpen W ∧ F.uPoint (γ a).val ∈ W ∧
      (∀ r, (e r).map.source = W ∧ (e r).box = k ∧ (e r).transverse = w) ∧
      ContinuousOn (fun p : Set.Icc a b × F.ULeaf (γ a).val ↦
        ((e p.1).map p.2).val) (univ ×ˢ W) ∧
      ∀ z ∈ W, (e ⟨a,le_rfl,hab⟩).map z = z := by
  classical
  obtain ⟨z₀,hz₀⟩ := hsegment a le_rfl hab
  have hy (r : Set.Icc a b) : (γ r.val).val ∈ (F.box k).image := by
    obtain ⟨z,hz⟩ := hsegment r.val r.property.1 r.property.2
    exact hz ▸ ((F.box k).chart (z,w)).property
  let γb : Set.Icc a b → (F.box k).image := fun r ↦ ⟨(γ r.val).val,hy r⟩
  have hγb : Continuous γb :=
    ((F.stable_inclusion q).comp (γ.continuous.comp continuous_subtype_val)).subtype_mk _
  let z : Set.Icc a b → FoliationCoordinateDisk s := fun r ↦ ((F.box k).chart.symm (γb r)).1
  have hzcont : Continuous z := ((F.box k).chart.symm.continuous.comp hγb).fst
  have hz (r : Set.Icc a b) : ((F.box k).chart (z r,w)).val = (γ r.val).val := by
    obtain ⟨v,hv⟩ := hsegment r.val r.property.1 r.property.2
    have he : (F.box k).chart (v,w) = γb r := Subtype.ext hv
    have hc := congrArg (fun y ↦ ((F.box k).chart.symm y).1) he
    simp only [Homeomorph.symm_apply_apply] at hc
    change v = z r at hc
    rwa [← hc]
  choose e hb hf hs ht hsource using fun r : Set.Icc a b ↦
    local_plaque_transport_of_box F k z₀ (z r) w (γ a).val (γ r.val).val hz₀ (hz r)
  let W : Set (F.ULeaf (γ a).val) := {v | ∃ u : FoliationCoordinateDisk t,
    ((F.box k).chart (z₀,u)).val = v.val}
  have hsrc (r : Set.Icc a b) : (e r).map.source = W := hsource r
  refine ⟨W,e,?_,?_,fun r ↦ ⟨hsrc r,hb r,ht r⟩,?_,?_⟩
  · rw [← hsrc ⟨a,le_rfl,hab⟩]
    exact (e ⟨a,le_rfl,hab⟩).map.open_source
  · rw [← hsrc ⟨a,le_rfl,hab⟩]
    exact (e ⟨a,le_rfl,hab⟩).source_point
  · exact fixed_source_plaque_transport_continuous_g1 F k z₀ w (γ a).val hz₀
      z hzcont (fun r ↦ (γ r.val).val) e
      (fun r ↦ ⟨hb r,hf r,hs r,ht r,hsource r⟩)
  · intro v hv
    obtain ⟨u,hu⟩ := hv
    have heq := (e ⟨a,le_rfl,hab⟩).coordinate_map v u ((hsrc _).symm ▸ ⟨u,hu⟩)
    rw [hb,hf,hs] at heq
    have hzinit : z ⟨a,le_rfl,hab⟩ = z₀ := by
      have he : (F.box k).chart (z ⟨a,le_rfl,hab⟩,w) = (F.box k).chart (z₀,w) :=
        Subtype.ext ((hz ⟨a,le_rfl,hab⟩).trans hz₀.symm)
      exact congrArg Prod.fst ((F.box k).chart.injective he)
    apply Subtype.ext
    rw [heq hu,hzinit]
    exact hu

/-- Extend a continuous prefix family across one stable plaque segment.    The source is shrunk by the endpoint transport; exact identity at the join makes the two continuous ambient evaluations agree there. -/
theorem extend_continuous_prefix_family_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b) (k : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hsegment : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box k).chart (z,w)).val = (γ r).val)
    (h₀ : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r)
    (W₀ : Set (F.ULeaf (γ 0).val)) (hW₀ : IsOpen W₀) (hxW₀ : F.uPoint (γ 0).val ∈ W₀)
    (hsource₀ : ∀ r ≤ a, W₀ ⊆ (h₀ r).map.source)
    (hcont₀ : ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
      ((h₀ p.1).map p.2).val) (Iic a ×ˢ W₀)) :
    ∃ (h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r)
      (W : Set (F.ULeaf (γ 0).val)),
      IsOpen W ∧ F.uPoint (γ 0).val ∈ W ∧
      (∀ r ≤ b, W ⊆ (h r).map.source) ∧
      ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
        ((h p.1).map p.2).val) (Iic b ×ˢ W) := by
  classical
  obtain ⟨V,e,hV,hxV,he,hecont,heid⟩ :=
    stable_segment_continuous_plaque_family_g1 F γ a b hab k w hsegment
  let ea := e ⟨a,le_rfl,hab⟩
  let W := W₀ ∩ ((h₀ a).map.trans ea.map).source
  have hW : IsOpen W := hW₀.inter ((h₀ a).map.trans ea.map).open_source
  have hWs (z : F.ULeaf (γ 0).val) (hz : z ∈ W) :
      z ∈ W₀ ∧ z ∈ (h₀ a).map.source ∧ (h₀ a).map z ∈ V := by
    exact ⟨hz.1,hz.2.1,(he _).1 ▸ hz.2.2⟩
  have hxW : F.uPoint (γ 0).val ∈ W := by
    refine ⟨hxW₀,(h₀ a).source_point,?_⟩
    change (h₀ a).map (F.uPoint (γ 0).val) ∈ (e ⟨a,le_rfl,hab⟩).map.source
    rw [(h₀ a).map_point,(he _).1]
    exact hxV
  let er (r : Icc a b) : PathHolonomyRepresentative F γ a r.val := {
    toPointedLeafHomeomorph := (e r).toPointedLeafHomeomorph
    chain := PlaqueChainAlong.single a r.val r.prop.1 (e r) (by
      intro z haz hzr
      obtain ⟨v,hv⟩ := hsegment z haz (hzr.trans r.prop.2)
      exact ⟨v,by rw [(he r).2.1,(he r).2.2]; exact hv⟩) }
  choose hr hhr using fun r : Icc a b ↦
    compose_path_representatives F γ 0 a r.val bot_le r.prop.1 (h₀ a) (er r)
  let h (r : unitInterval) : PathHolonomyRepresentative F γ 0 r :=
    if hra : r ≤ a then h₀ r else if hrb : r ≤ b then hr ⟨r,le_of_not_ge hra,hrb⟩ else h₀ r
  let R (p : unitInterval × F.ULeaf (γ 0).val) : M :=
    ((e (projIcc a b hab p.1)).map ((h₀ a).map p.2)).val
  have hR : ContinuousOn R (univ ×ˢ W) := by
    apply hecont.comp
      (((continuous_projIcc (h := hab)).comp continuous_fst).continuousOn.prodMk
        ((h₀ a).map.continuousOn.comp continuous_snd.continuousOn
          (fun p hp ↦ (hWs p.2 hp.2).2.1)))
    exact fun p hp ↦ ⟨mem_univ _,(hWs p.2 hp.2).2.2⟩
  refine ⟨h,W,hW,hxW,?_,?_⟩
  · intro r hrb z hz
    dsimp [h]
    split_ifs with hra
    · exact hsource₀ r hra (hWs z hz).1
    · rw [hhr]
      exact ⟨(hWs z hz).2.1,(he _).1.symm ▸ (hWs z hz).2.2⟩
  · have hglue : ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
        if p.1 ≤ a then ((h₀ p.1).map p.2).val else R p) (Iic b ×ˢ W) := by
      apply ContinuousOn.if
      · intro p hp
        have hpa : p.1 = a := frontier_le_subset_eq continuous_fst continuous_const hp.2
        dsimp [R]
        rw [hpa,projIcc_of_mem hab ⟨le_rfl,hab⟩,heid _ (hWs p.2 hp.1.2).2.2]
      · apply hcont₀.mono
        intro p hp
        have hclosed : IsClosed {p : unitInterval × F.ULeaf (γ 0).val | p.1 ≤ a} :=
          isClosed_le continuous_fst continuous_const
        exact ⟨show p ∈ {p | p.1 ≤ a} from hclosed.closure_eq ▸ hp.2,(hWs p.2 hp.1.2).1⟩
      · exact hR.mono (fun p hp ↦ ⟨mem_univ _,hp.1.2⟩)
    apply hglue.congr
    intro p hp
    dsimp [h]
    split_ifs with hpa hpb
    · rfl
    · rw [hhr]
      dsimp [R,er]
      rw [projIcc_of_mem hab ⟨le_of_not_ge hpa,hp.1⟩]
    · exact (hpb hp.1).elim


/-- Every stable path admits genuine prefix representatives on one open initial unstable neighborhood, with jointly continuous ambient evaluation. -/
theorem path_continuous_prefix_family_g1
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    ∃ (h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r)
      (W : Set (F.ULeaf (γ 0).val)),
      IsOpen W ∧ F.uPoint (γ 0).val ∈ W ∧
      (∀ r, W ⊆ (h r).map.source) ∧
      ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
        ((h p.1).map p.2).val) (univ ×ˢ W) := by
  classical
  let J := {bw : F.boxIndex × FoliationCoordinateDisk t // F.stableLabel bw.1 bw.2 = q}
  let j : J → FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun bw z ↦ ⟨((F.box bw.val.1).chart (z,bw.val.2)).val,
      (F.stable_label bw.val.1 z bw.val.2).trans bw.prop⟩
  have hj : ∀ bw : J, IsOpenEmbedding (j bw) := fun bw ↦
    stable_plaque_open_at_class_g10 F bw.val.1 bw.val.2 q bw.prop
  have hcover : ∀ r : unitInterval, ∃ bw : J, γ r ∈ Set.range (j bw) := by
    intro r
    obtain ⟨b,hb⟩ := F.cover (γ r).val
    let zw := (F.box b).chart.symm ⟨(γ r).val,hb⟩
    have hv : ((F.box b).chart zw).val = (γ r).val :=
      congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(γ r).val,hb⟩)
    have hq : F.stableLabel b zw.2 = q :=
      (F.stable_label b zw.1 zw.2).symm.trans
        ((congrArg (Quotient.mk F.stablePartition) hv).trans (γ r).prop)
    exact ⟨⟨(b,zw.2),hq⟩,zw.1,Subtype.ext hv⟩
  obtain ⟨n,hn,ts,ht0,htn,htmono,assigned,hsub⟩ :=
    exists_openCover_pathSubdivision γ (fun bw : J ↦ Set.range (j bw))
      (fun bw ↦ (hj bw).isOpen_range) hcover
  let a : ℕ → unitInterval := fun k ↦ ts ⟨min k n,by omega⟩
  have ha : Monotone a := by
    intro k l hkl
    apply htmono
    change min k n ≤ min l n
    omega
  have ha0 : a 0 = 0 := by
    have hh : (⟨min 0 n,by omega⟩ : Fin (n+1)) = 0 := Fin.ext (Nat.zero_min n)
    exact (congrArg ts hh).trans ht0
  have han : a n = 1 := by
    have hh : (⟨min n n,by omega⟩ : Fin (n+1)) = Fin.last n := Fin.ext (min_self n)
    exact (congrArg ts hh).trans htn
  have hsegments (k : ℕ) (hk : k < n) :
      ∃ (b : F.boxIndex) (w : FoliationCoordinateDisk t),
        ∀ r : unitInterval, a k ≤ r → r ≤ a (k+1) →
          ∃ z : FoliationCoordinateDisk s, ((F.box b).chart (z,w)).val = (γ r).val := by
    let kk : Fin n := ⟨k,hk⟩
    have hleft : a k = ts kk.castSucc := by
      apply congrArg ts
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hk)
    have hright : a (k+1) = ts kk.succ := by
      apply congrArg ts
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hk)
    refine ⟨(assigned kk).val.1,(assigned kk).val.2,?_⟩
    rw [hleft,hright]
    intro r hl hr
    have hh : γ r ∈ Set.range (γ.subpath (ts kk.castSucc) (ts kk.succ)) := by
      rw [γ.range_subpath_of_le _ _ (htmono (Fin.castSucc_le_succ kk))]
      exact ⟨r,⟨hl,hr⟩,rfl⟩
    obtain ⟨z,hz⟩ := hsub kk hh
    exact ⟨z,congrArg Subtype.val hz⟩
  have hfinite (k : ℕ) (hk : k ≤ n) :
      ∃ (h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r)
        (W : Set (F.ULeaf (γ 0).val)), IsOpen W ∧ F.uPoint (γ 0).val ∈ W ∧
        (∀ r ≤ a k, W ⊆ (h r).map.source) ∧
        ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
          ((h p.1).map p.2).val) (Iic (a k) ×ˢ W) := by
    induction k with
    | zero =>
      let h (r : unitInterval) :=
        (path_holonomy_subinterval_representative_exists F γ 0 r bot_le).some
      refine ⟨h,(h 0).map.source,(h 0).map.open_source,(h 0).source_point,?_,?_⟩
      · intro r hr
        have hr0 : r = 0 := le_antisymm (ha0 ▸ hr) bot_le
        subst r
        exact Subset.rfl
      · have hc : ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
            ((h 0).map p.2).val) (Iic (a 0) ×ˢ (h 0).map.source) :=
          (F.unstable_inclusion _).comp_continuousOn
            ((h 0).map.continuousOn.comp continuous_snd.continuousOn (fun p hp ↦ hp.2))
        apply hc.congr
        intro p hp
        have hle : p.1 ≤ a 0 := hp.1
        rw [ha0] at hle
        have hr0 : p.1 = 0 := le_antisymm hle bot_le
        dsimp only
        rw [hr0]
    | succ k ih =>
      obtain ⟨h,W,hW,hxW,hsrc,hcont⟩ := ih (by omega)
      obtain ⟨b,w,hseg⟩ := hsegments k (by omega)
      exact extend_continuous_prefix_family_g1 F γ (a k) (a (k+1))
        (ha (Nat.le_succ k)) b w hseg h W hW hxW hsrc hcont
  obtain ⟨h,W,hW,hxW,hsource,hcont⟩ := hfinite n le_rfl
  refine ⟨h,W,hW,hxW,fun r ↦ hsource r (han ▸ le_top),?_⟩
  apply hcont.mono
  intro p hp
  exact ⟨show p.1 ≤ a n by rw [han]; exact le_top,hp.2⟩


end HolomorphicAnosov.Ghys
