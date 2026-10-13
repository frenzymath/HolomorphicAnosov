import HolomorphicAnosov.Analysis.Complex.ConnectedCurveHolomorphicIdentity
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v w

variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u, v} s t M)

/-- A foliation box has a covering lift through any prescribed point over the box. (Hatcher, Prop.
1.33, pp.61–62) -/
theorem covering_foliation_box_lift
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (i : F.boxIndex) (q : FoliationCoordinateDisk s × FoliationCoordinateDisk t)
    (e : E) (he : p e = ((F.box i).chart q).val) :
    ∃ L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E),
      L q = e ∧ ∀ z, p (L z) = ((F.box i).chart z).val := by
  let : ContractibleSpace (FoliationCoordinateDisk s) :=
    (convex_ball (0 : Fin s → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : ContractibleSpace (FoliationCoordinateDisk t) :=
    (convex_ball (0 : Fin t → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : LocallyPathConnectedSpace (FoliationCoordinateDisk s) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (FoliationCoordinateDisk t) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  let f : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, M) :=
    ⟨fun z ↦ ((F.box i).chart z).val,
      continuous_subtype_val.comp (F.box i).chart.continuous⟩
  obtain ⟨L, hL, _⟩ := hp.existsUnique_continuousMap_lifts f q e he
  exact ⟨L, hL.1, fun z ↦ congrFun hL.2 z⟩

omit [T2Space M] [SecondCountableTopology M] in
/-- Continuous lifts with equal marked values and equal projection germs have equal germs at the
marked point. (Hatcher, Prop. 1.34) -/
theorem covering_lifts_eventuallyEq
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {X : Type*} [TopologicalSpace X] {x : X} {f g : X → E}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hx : f x = g x)
    (heq : (p ∘ f) =ᶠ[𝓝 x] (p ∘ g)) : f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hxU, hinj⟩ := hp.isLocalHomeomorph.isLocallyInjective (g x)
  have hUf := hf.eventually (hU.mem_nhds (hx.symm ▸ hxU))
  have hUg := hg.eventually (hU.mem_nhds hxU)
  filter_upwards [hUf, hUg, heq] with z hz₁ hz₂ hz
  exact hinj hz₁ hz₂ hz


/-- A pointed lift of a foliation box agrees with a lifted path throughout any path staying over
that box and starting at the marked point. (Hatcher, Prop. 1.34, pp.62–63) -/
theorem covering_box_lift_path
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (i : F.boxIndex)
    (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E))
    (hL : ∀ z, p (L z) = ((F.box i).chart z).val)
    {x y : E} (β : Path x y) (hβ : ∀ r, p (β r) ∈ (F.box i).image)
    (hpoint : L ((F.box i).chart.symm ⟨p x, by simpa using hβ 0⟩) = x) :
    ∀ r, L ((F.box i).chart.symm ⟨p (β r), hβ r⟩) = β r := by
  let c : unitInterval → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
    fun r ↦ (F.box i).chart.symm ⟨p (β r), hβ r⟩
  have hc : Continuous c := (F.box i).chart.symm.continuous.comp
    ((hp.continuous.comp β.continuous).subtype_mk _)
  have heq : (fun r ↦ L (c r)) = β := hp.eq_of_comp_eq (L.continuous.comp hc)
    β.continuous (by
      funext r
      change p (L (c r)) = p (β r)
      rw [hL]
      exact congrArg Subtype.val ((F.box i).chart.apply_symm_apply _))
    0 (by simpa [c] using hpoint)
  exact congrFun heq


/-- Local plaque transport preserves the developing germ on pointed unstable lifts when the
developing map has equal values on the corresponding horizontal slices of the lifted box. -/
theorem covering_local_plaque_developing_germ
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} (D : E → Z) {x y : M} (e : LocalPlaqueTransport F x y)
    (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E))
    (hL : ∀ z, p (L z) = ((F.box e.box).chart z).val)
    (hD : ∀ w, D (L (e.first, w)) = D (L (e.second, w)))
    (f : F.ULeaf x → E) (g : F.ULeaf y → E)
    (hf : ContinuousAt f (F.uPoint x)) (hg : ContinuousAt g (F.uPoint y))
    (hfproj : ∀ z, p (f z) = z.val) (hgproj : ∀ z, p (g z) = z.val)
    (hfpoint : f (F.uPoint x) = L (e.first, e.transverse))
    (hgpoint : g (F.uPoint y) = L (e.second, e.transverse)) :
    (fun z ↦ D (f z)) =ᶠ[𝓝 (F.uPoint x)] (fun z ↦ D (g (e.map z))) := by
  have hlabel : F.unstableLabel e.box e.first = Quotient.mk F.unstablePartition x := by
    exact (F.unstable_label _ _ _).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e.first_point)
  let j : FoliationCoordinateDisk t → F.ULeaf x := fun w ↦
    ⟨((F.box e.box).chart (e.first, w)).val,
      (F.unstable_label _ _ _).trans hlabel⟩
  have hj : IsOpenEmbedding j := by
    have aux (q : Quotient F.unstablePartition) (hq : F.unstableLabel e.box e.first = q) :
        letI := F.unstableTopology q
        IsOpenEmbedding (fun w : FoliationCoordinateDisk t ↦
          (⟨((F.box e.box).chart (e.first, w)).val,
            (F.unstable_label _ _ _).trans hq⟩ : IntrinsicFoliationLeaf F.unstablePartition q)) := by
      subst q
      exact F.unstable_plaque _ _
    exact aux _ hlabel
  have hjpoint : j e.transverse = F.uPoint x := Subtype.ext e.first_point
  have hjcont : ContinuousAt j e.transverse := hj.continuous.continuousAt
  have hmapcont : ContinuousAt e.map (F.uPoint x) :=
    e.map.continuousOn.continuousAt (e.map.open_source.mem_nhds e.source_point)
  have hsource : ∀ᶠ w in 𝓝 e.transverse, j w ∈ e.map.source :=
    (hjcont.eventually (by rw [hjpoint]; exact e.map.open_source.mem_nhds e.source_point))
  have heqf : (fun w ↦ f (j w)) =ᶠ[𝓝 e.transverse] (fun w ↦ L (e.first, w)) := by
    apply covering_lifts_eventuallyEq p hp
    · exact (hjpoint ▸ hf).comp hjcont
    · exact (L.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
    · rw [hjpoint, hfpoint]
    · exact Filter.Eventually.of_forall (fun w ↦ by
        change p (f (j w)) = p (L (e.first, w))
        rw [hfproj, hL])
  have heqg : (fun w ↦ g (e.map (j w))) =ᶠ[𝓝 e.transverse]
      (fun w ↦ L (e.second, w)) := by
    apply covering_lifts_eventuallyEq p hp
    · have hg' : ContinuousAt g (e.map (j e.transverse)) := by
        simpa only [hjpoint, e.map_point] using hg
      have hm' : ContinuousAt e.map (j e.transverse) := hjpoint ▸ hmapcont
      exact (hg'.comp hm').comp hjcont
    · exact (L.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
    · rw [hjpoint, e.map_point, hgpoint]
    · filter_upwards [hsource] with w hw
      change p (g (e.map (j w))) = p (L (e.second, w))
      rw [hgproj, hL]
      exact e.coordinate_map (j w) w hw rfl
  rw [← hjpoint, ← hj.map_nhds_eq]
  change ∀ᶠ w in 𝓝 e.transverse, D (f (j w)) = D (g (e.map (j w)))
  filter_upwards [heqf, heqg] with w hwf hwg
  rw [hwf, hwg]
  exact hD w


/-- A plaque-chain representative preserves the developing germ on pointed unstable lifts when the
developing map is constant on horizontal slices of lifted boxes. -/
theorem covering_plaque_chain_developing_germ
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} (D : E → Z)
    (hD : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {e₀ e₁ : E} (β : Path e₀ e₁) (hβ : ∀ r, p (β r) = (γ r).val)
    (lift : ∀ r : unitInterval, F.ULeaf (γ r).val → E)
    (hlift : ∀ r, Continuous (lift r))
    (hproj : ∀ r z, p (lift r z) = z.val)
    (hpoint : ∀ r, lift r (F.uPoint (γ r).val) = β r)
    {a b : unitInterval}
    {h : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (chain : PlaqueChainAlong F γ a b h) :
    F.uPoint (γ a).val ∈ h.source ∧
    h (F.uPoint (γ a).val) = F.uPoint (γ b).val ∧
    (fun z ↦ D (lift a z)) =ᶠ[𝓝 (F.uPoint (γ a).val)] (fun z ↦ D (lift b (h z))) := by
  induction chain with
  | single a b hab e hsegment =>
    obtain ⟨L, hLpoint, hL⟩ := covering_foliation_box_lift F p hp e.box
      (e.first, e.transverse) (β a) ((hβ a).trans e.first_point.symm)
    have habox : (F.box e.box).chart.symm
        ⟨p (β a), by simpa only [← hLpoint] using (hL (e.first, e.transverse)).symm ▸ ((F.box e.box).chart (e.first, e.transverse)).property⟩ =
        (e.first, e.transverse) := by
      apply (F.box e.box).chart.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext ((hβ a).trans e.first_point.symm)
    have hbbox : (F.box e.box).chart.symm
        ⟨p (β b), by exact ((hβ b).trans e.second_point.symm) ▸ ((F.box e.box).chart (e.second, e.transverse)).property⟩ =
        (e.second, e.transverse) := by
      apply (F.box e.box).chart.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext ((hβ b).trans e.second_point.symm)
    have hβbox : ∀ r, p (β.subpath a b r) ∈ (F.box e.box).image := by
      intro r
      obtain ⟨v, hv, hvβ⟩ := (β.range_subpath_of_le a b hab) ▸
        (show β.subpath a b r ∈ Set.range (β.subpath a b) from ⟨r, rfl⟩)
      obtain ⟨z, hz⟩ := hsegment v hv.1 hv.2
      rw [← hvβ, hβ v, ← hz]
      exact ((F.box e.box).chart _).property
    have hLpath := covering_box_lift_path F p hp e.box L hL (β.subpath a b) hβbox
      (by rw [habox]; exact hLpoint)
    have hLend : L (e.second, e.transverse) = β b := by
      have hh := hLpath 1
      simpa only [Path.target, hbbox] using hh
    refine ⟨e.source_point, e.map_point, ?_⟩
    exact covering_local_plaque_developing_germ F p hp D e L hL
      (hD e.box L hL e.first e.second) (lift a) (lift b)
      (hlift a).continuousAt (hlift b).continuousAt (hproj a) (hproj b)
      ((hpoint a).trans hLpoint.symm) ((hpoint b).trans hLend.symm)
  | @compose a b c h h' hab hbc left right ih ih' =>
    refine ⟨⟨ih.1, ?_⟩, ?_, ?_⟩
    · change h (F.uPoint (γ a).val) ∈ h'.source
      rw [ih.2.1]
      exact ih'.1
    · change h' (h (F.uPoint (γ a).val)) = F.uPoint (γ c).val
      rw [ih.2.1, ih'.2.1]
    · have ht : Tendsto h (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
        rw [← ih.2.1]
        exact h.continuousOn.continuousAt (h.open_source.mem_nhds ih.1)
      exact ih.2.2.trans (ih'.2.2.comp_tendsto ht)


/-- Global stable holonomy preserves the developing germ on pointed unstable lifts when the
developing map is constant on horizontal slices of lifted boxes. (Ghys, p.598; Hatcher, Prop.
1.34, pp.62–63) -/
theorem covering_global_holonomy_developing_germ
    (C : IntrinsicComplexUnstableLeaves F) (G : GlobalSHolonomyData F C)
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} (D : E → Z)
    (hD : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {e₀ e₁ : E} (β : Path e₀ e₁) (hβ : ∀ r, p (β r) = (γ r).val)
    (lift : ∀ r : unitInterval, F.ULeaf (γ r).val → E)
    (hlift : ∀ r, Continuous (lift r))
    (hproj : ∀ r z, p (lift r z) = z.val)
    (hpoint : ∀ r, lift r (F.uPoint (γ r).val) = β r) :
    (fun z ↦ D (lift 0 (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z)))
      =ᶠ[𝓝 (F.uPoint x.val)]
    (fun z ↦ D (lift 1 (castIntrinsicULeaf F (congrArg Subtype.val γ.target).symm
      (G.transport γ z)))) := by
  have hcastCont {a b : M} (h : a = b) : Continuous (castIntrinsicULeaf F h) := by
    cases h
    exact continuous_id
  have hcastPoint {a b : M} (h : a = b) :
      castIntrinsicULeaf F h (F.uPoint a) = F.uPoint b := by
    cases h
    rfl
  have hcastCancel {a b : M} (h : a = b) (z : F.ULeaf a) :
      castIntrinsicULeaf F h.symm (castIntrinsicULeaf F h z) = z := by
    cases h
    rfl
  have ht : Tendsto (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm)
      (𝓝 (F.uPoint x.val)) (𝓝 (F.uPoint (γ 0).val)) := by
    have ht := (hcastCont (congrArg Subtype.val γ.source).symm).continuousAt (x := F.uPoint x.val)
    change Tendsto _ _ (𝓝 (castIntrinsicULeaf F _ (F.uPoint x.val))) at ht
    simpa only [hcastPoint] using ht
  have he := (covering_plaque_chain_developing_germ F p hp D hD γ β hβ
    lift hlift hproj hpoint ((G.localContinuation γ).representative 0 1 (by simp)).chain).2.2
  filter_upwards [he.comp_tendsto ht, Germ.coe_eq.mp (G.extends_local γ)] with z hz hG
  rw [hG, hcastCancel]
  exact hz

/-- If the developing map is constant on each pointed stable-leaf lift, it is constant on every
horizontal slice of a lifted foliation box. -/
theorem covering_developing_const_on_box
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} (D : E → Z)
    (hSlifts : ∀ x : E,
      ∃ lift : IntrinsicFoliationLeaf F.stablePartition
          (Quotient.mk F.stablePartition (p x)) → E,
        Continuous lift ∧ lift ⟨p x, rfl⟩ = x ∧
        (∀ z, p (lift z) = z.val) ∧ (∀ z, D (lift z) = D x)) :
    ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)) := by
  intro i L hL z z' w
  obtain ⟨l, hl, hlpoint, hlproj, hlD⟩ := hSlifts (L (z, w))
  have hlabel : F.stableLabel i w = Quotient.mk F.stablePartition (p (L (z, w))) :=
    (F.stable_label i z w).symm.trans (congrArg (Quotient.mk _) (hL (z, w)).symm)
  let j : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition
      (Quotient.mk F.stablePartition (p (L (z, w)))) := fun v ↦
    ⟨((F.box i).chart (v, w)).val, (F.stable_label i v w).trans hlabel⟩
  have hj : Continuous j := by
    have aux (q : Quotient F.stablePartition) (hq : F.stableLabel i w = q) :
        letI := F.stableTopology q
        Continuous (fun v : FoliationCoordinateDisk s ↦
          (⟨((F.box i).chart (v, w)).val,
            (F.stable_label i v w).trans hq⟩ : IntrinsicFoliationLeaf F.stablePartition q)) := by
      subst q
      exact (F.stable_plaque i w).continuous
    exact aux _ hlabel
  let : PreconnectedSpace (FoliationCoordinateDisk s) :=
    Subtype.preconnectedSpace (convex_ball (0 : Fin s → ℝ) 1).isPreconnected
  have heq : (fun v ↦ L (v, w)) = l ∘ j := hp.eq_of_comp_eq
    (L.continuous.comp (continuous_id.prodMk continuous_const)) (hl.comp hj)
    (by funext v; exact (hL (v, w)).trans (hlproj (j v)).symm) z (by
      have hjz : j z = ⟨p (L (z, w)), rfl⟩ := Subtype.ext (hL (z, w)).symm
      simpa only [Function.comp_apply, hjz] using hlpoint.symm)
  exact (hlD (j z')).symm.trans (congrArg D (congrFun heq z').symm)

/-- Holomorphic developing maps on endpoint unstable leaves have the same omitted point when their
germs are intertwined by global stable holonomy. (Ghys, p.598) -/
theorem covering_global_holonomy_poles_eq
    (C : IntrinsicComplexUnstableLeaves F) (G : GlobalSHolonomyData F C)
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [ChartedSpace (ComplexModel 1) Z] [IsManifold (complexModel 1) ∞ Z]
    (D : E → Z)
    (hD : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)))
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {e₀ e₁ : E} (β : Path e₀ e₁) (hβ : ∀ r, p (β r) = (γ r).val)
    (lift : ∀ r : unitInterval, F.ULeaf (γ r).val → E)
    (hlift : ∀ r, Continuous (lift r))
    (hproj : ∀ r z, p (lift r z) = z.val)
    (hpoint : ∀ r, lift r (F.uPoint (γ r).val) = β r)
    (hhol : ∀ r, letI := C.charts (Quotient.mk F.unstablePartition (γ r).val)
      ContMDiff (complexModel 1) (complexModel 1) ∞ (D ∘ lift r))
    (pole : unitInterval → Z)
    (hrange : ∀ r, Set.range (D ∘ lift r) = {pole r}ᶜ) : pole 0 = pole 1 := by
  let := C.charts (Quotient.mk F.unstablePartition x.val)
  let := C.charts (Quotient.mk F.unstablePartition y.val)
  let := C.charts (Quotient.mk F.unstablePartition (γ 0).val)
  let := C.charts (Quotient.mk F.unstablePartition (γ 1).val)
  let := C.complex_manifold (Quotient.mk F.unstablePartition x.val)
  let := F.unstable_connected (Quotient.mk F.unstablePartition x.val)
  have hcastHol {a b : M} (h : a = b) :
      letI := C.charts (Quotient.mk F.unstablePartition a)
      letI := C.charts (Quotient.mk F.unstablePartition b)
      ContMDiff (complexModel 1) (complexModel 1) ∞ (castIntrinsicULeaf F h) := by
    cases h
    let := C.charts (Quotient.mk F.unstablePartition a)
    exact contMDiff_id
  have hcastSurj {a b : M} (h : a = b) : Function.Surjective (castIntrinsicULeaf F h) := by
    cases h
    exact Function.surjective_id
  let f₀ := (D ∘ lift 0) ∘ castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm
  let f₁ := (D ∘ lift 1) ∘ castIntrinsicULeaf F (congrArg Subtype.val γ.target).symm
  have hf₀ : ContMDiff (complexModel 1) (complexModel 1) ∞ f₀ :=
    (hhol 0).comp (hcastHol _)
  have hf₁ : ContMDiff (complexModel 1) (complexModel 1) ∞ f₁ :=
    (hhol 1).comp (hcastHol _)
  have hgerm : f₀ =ᶠ[𝓝 (F.uPoint x.val)] f₁ ∘ G.transport γ :=
    covering_global_holonomy_developing_germ F C G p hp D hD γ β hβ
      lift hlift hproj hpoint
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hgerm
  have heq := Ghys.connected_curve_holomorphic_eq_of_open_germ f₀ (f₁ ∘ G.transport γ)
    hf₀ (hf₁.comp (G.transport γ).contMDiff) U hUopen ⟨_, hxU⟩ hUsub
  have hrf₀ : Set.range f₀ = {pole 0}ᶜ := by
    dsimp only [f₀]
    rw [Set.range_comp, Set.range_eq_univ.mpr (hcastSurj _), Set.image_univ]
    exact hrange 0
  have hrf₁ : Set.range f₁ = {pole 1}ᶜ := by
    dsimp only [f₁]
    rw [Set.range_comp, Set.range_eq_univ.mpr (hcastSurj _), Set.image_univ]
    exact hrange 1
  have hrt : Set.range (G.transport γ : F.ULeaf x.val → F.ULeaf y.val) = Set.univ :=
    Set.range_eq_univ.mpr (G.transport γ).surjective
  have hr : Set.range f₀ = Set.range f₁ := by
    rw [heq, Set.range_comp, hrt, Set.image_univ]
  rw [hrf₀, hrf₁] at hr
  exact Set.singleton_injective (compl_injective hr)

/-- On a connected cover, the omitted points of the holomorphic developing maps on unstable leaves
coincide, provided they are constant along lifted unstable leaves and the developing map is
constant on horizontal slices. (Ghys, p.598) -/
theorem covering_global_holonomy_common_pole
    (C : IntrinsicComplexUnstableLeaves F) (G : GlobalSHolonomyData F C)
    {E : Type w} [TopologicalSpace E] [PreconnectedSpace E]
    (p : E → M) (hp : IsCoveringMap p)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [ChartedSpace (ComplexModel 1) Z] [IsManifold (complexModel 1) ∞ Z]
    (D : E → Z) (R : E → E → Prop) (pole : E → Z)
    (hDbox : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)))
    (UL : ∀ x : E, F.ULeaf (p x) → E)
    (hULcont : ∀ x, Continuous (UL x))
    (hULproj : ∀ x z, p (UL x z) = z.val)
    (hULpoint : ∀ x, UL x (F.uPoint (p x)) = x)
    (hULrange : ∀ x, Set.range (UL x) = {y | Relation.EqvGen R x y})
    (hULdev : ∀ x, letI := C.charts (Quotient.mk F.unstablePartition (p x))
      ContMDiff (complexModel 1) (complexModel 1) ∞ (D ∘ UL x))
    (hULdevrange : ∀ x, Set.range (D ∘ UL x) = {pole x}ᶜ)
    (hpole_unstable : ∀ x y, Relation.EqvGen R x y → pole x = pole y)
    (e0 : E) : ∀ x : E, pole x = pole e0 := by
  have hpole_path {q : Quotient F.stablePartition}
      {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
      {x' y' : E} (β : Path x' y') (hβ : ∀ r, p (β r) = (γ r).val) :
      pole x' = pole y' := by
    have hcastCont {a b : M} (h : a = b) : Continuous (castIntrinsicULeaf F h) := by
      cases h
      exact continuous_id
    have hcastPoint {a b : M} (h : a = b) :
        castIntrinsicULeaf F h (F.uPoint a) = F.uPoint b := by cases h; rfl
    have hcastVal {a b : M} (h : a = b) (z : F.ULeaf a) :
        (castIntrinsicULeaf F h z).val = z.val := by cases h; rfl
    have hcastHol {a b : M} (h : a = b) :
        letI := C.charts (Quotient.mk F.unstablePartition a)
        letI := C.charts (Quotient.mk F.unstablePartition b)
        ContMDiff (complexModel 1) (complexModel 1) ∞ (castIntrinsicULeaf F h) := by
      cases h
      let := C.charts (Quotient.mk F.unstablePartition a)
      exact contMDiff_id
    have hcastSurj {a b : M} (h : a = b) : Function.Surjective (castIntrinsicULeaf F h) := by
      cases h
      exact Function.surjective_id
    let lr : ∀ r : unitInterval, F.ULeaf (γ r).val → E :=
      fun r ↦ UL (β r) ∘ castIntrinsicULeaf F (hβ r).symm
    have hc : ∀ r, Continuous (lr r) := by
      intro r
      let := C.charts (Quotient.mk F.unstablePartition (p (β r)))
      exact (hULcont (β r)).comp (hcastCont _)
    have hpr : ∀ r z, p (lr r z) = z.val := by
      intro r z
      exact (hULproj _ _).trans (hcastVal _ _)
    have hpt : ∀ r, lr r (F.uPoint (γ r).val) = β r := by
      intro r
      dsimp only [lr, Function.comp_apply]
      rw [hcastPoint, hULpoint]
    have hh : ∀ r, letI := C.charts (Quotient.mk F.unstablePartition (γ r).val)
        ContMDiff (complexModel 1) (complexModel 1) ∞ (D ∘ lr r) := by
      intro r
      let := C.charts (Quotient.mk F.unstablePartition (γ r).val)
      let := C.charts (Quotient.mk F.unstablePartition (p (β r)))
      exact (hULdev (β r)).comp (hcastHol _)
    have hr : ∀ r, Set.range (D ∘ lr r) = {pole (β r)}ᶜ := by
      intro r
      change Set.range ((D ∘ UL (β r)) ∘ castIntrinsicULeaf F (hβ r).symm) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr (hcastSurj _), Set.image_univ]
      exact hULdevrange (β r)
    have he := covering_global_holonomy_poles_eq F C G p hp D hDbox
      γ β hβ lr hc hpr hpt hh (pole ∘ β) hr
    simpa only [Function.comp_apply, Path.source, Path.target] using he
  have hpoleSbox : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, pole (L (z, w)) = pole (L (z', w)) := by
    intro i L hL z z' w
    let : ContractibleSpace (FoliationCoordinateDisk s) :=
      (convex_ball (0 : Fin s → ℝ) 1).contractibleSpace ⟨0, by simp⟩
    let j : FoliationCoordinateDisk s →
        IntrinsicFoliationLeaf F.stablePartition (F.stableLabel i w) :=
      fun v ↦ ⟨((F.box i).chart (v, w)).val, F.stable_label i v w⟩
    have hj : Continuous j := (F.stable_plaque i w).continuous
    let η := PathConnectedSpace.somePath z z'
    exact hpole_path (η.map hj)
      (η.map (L.continuous.comp (continuous_id.prodMk continuous_const)))
      (fun r ↦ hL (η r, w))
  have hpoleUbox : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z w w', pole (L (z, w)) = pole (L (z, w')) := by
    intro i L hL z w w'
    let x := L (z, w)
    have hlabel : F.unstableLabel i z = Quotient.mk F.unstablePartition (p x) :=
      (F.unstable_label i z w).symm.trans (congrArg (Quotient.mk _) (hL (z, w)).symm)
    let j : FoliationCoordinateDisk t → F.ULeaf (p x) := fun v ↦
      ⟨((F.box i).chart (z, v)).val, (F.unstable_label i z v).trans hlabel⟩
    have hj : Continuous j := by
      have aux (q : Quotient F.unstablePartition) (hq : F.unstableLabel i z = q) :
          letI := F.unstableTopology q
          Continuous (fun v : FoliationCoordinateDisk t ↦
            (⟨((F.box i).chart (z, v)).val,
              (F.unstable_label i z v).trans hq⟩ : IntrinsicFoliationLeaf F.unstablePartition q)) := by
        subst q
        let := F.unstableTopology (F.unstableLabel i z)
        exact (F.unstable_plaque i z).continuous
      exact aux _ hlabel
    let : PreconnectedSpace (FoliationCoordinateDisk t) :=
      Subtype.preconnectedSpace (convex_ball (0 : Fin t → ℝ) 1).isPreconnected
    let := C.charts (Quotient.mk F.unstablePartition (p x))
    have heq : (fun v ↦ L (z, v)) = UL x ∘ j := hp.eq_of_comp_eq
      (L.continuous.comp (continuous_const.prodMk continuous_id))
      ((hULcont x).comp hj)
      (by funext v; exact (hL (z, v)).trans (hULproj x (j v)).symm) w (by
        have hjw : j w = F.uPoint (p x) := Subtype.ext (hL (z, w)).symm
        simpa only [Function.comp_apply, hjw] using (hULpoint x).symm)
    apply hpole_unstable x
    have hm : L (z, w') ∈ Set.range (UL x) := ⟨j w', (congrFun heq w').symm⟩
    rw [hULrange x] at hm
    exact hm
  have hpoleLoc : IsLocallyConstant pole := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨i, hi⟩ := F.cover (p x)
    let q := (F.box i).chart.symm ⟨p x, hi⟩
    obtain ⟨L, hLpoint, hL⟩ := covering_foliation_box_lift F p hp i q x
      (congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨p x, hi⟩)).symm
    have hLc : IsOpenEmbedding (p ∘ L) := by
      have heq : p ∘ L = fun z ↦ ((F.box i).chart z).val := funext hL
      rw [heq]
      exact (F.box i).isOpen_image.isOpenEmbedding_subtypeVal.comp
        (F.box i).chart.isOpenEmbedding
    have hLo := hp.isLocalHomeomorph.isOpenEmbedding_of_comp hLc L.continuous
    filter_upwards [hLo.isOpen_range.mem_nhds ⟨q, hLpoint⟩] with y hy
    obtain ⟨r, rfl⟩ := hy
    calc
      pole (L r) = pole (L (q.1, r.2)) := hpoleSbox i L hL r.1 q.1 r.2
      _ = pole (L q) := hpoleUbox i L hL q.1 r.2 q.2
      _ = pole x := congrArg pole hLpoint
  exact fun x ↦ hpoleLoc.apply_eq_of_preconnectedSpace x e0

end HolomorphicAnosov
