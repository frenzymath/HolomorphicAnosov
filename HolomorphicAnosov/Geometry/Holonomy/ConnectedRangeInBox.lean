import HolomorphicAnosov.Geometry.FoliationPlaqueLabelFiberCountableG9
import Mathlib.Topology.Separation.Lemmas
import HolomorphicAnosov.Geometry.FinitePlaqueHolonomy

noncomputable section
open Set Filter TopologicalSpace
open scoped _root_.Topology
namespace HolomorphicAnosov
universe u v

/-- A continuous connected family of points of one separable stable leaf, all in one receiving box, lies in one plaque of that box.    This is the whole-family version of the countable-plaque argument in `continuous_stable_leaf_lift_g9`. (Ghys, Proposition 4.1) -/
theorem stable_connected_range_in_box {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.stablePartition)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (g : X → M) (hg : Continuous g)
    (hbox : ∀ x, g x ∈ (F.box b).image)
    (hleaf : ∀ x, Quotient.mk F.stablePartition (g x) = q) :
    (letI := F.stableTopology q;
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q)) →
    ∀ x y, ((F.box b).chart.symm ⟨g x, hbox x⟩).2 =
      ((F.box b).chart.symm ⟨g y, hbox y⟩).2 := by
  intro hsep
  let coords : X → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
    fun x ↦ (F.box b).chart.symm ⟨g x, hbox x⟩
  have hc : Continuous coords := (F.box b).chart.symm.continuous.comp (hg.subtype_mk _)
  have hlabel (x : X) : F.stableLabel b (coords x).2 = q := by
    calc
      F.stableLabel b (coords x).2 =
          Quotient.mk F.stablePartition ((F.box b).chart (coords x)).val :=
        (F.stable_label b (coords x).1 (coords x).2).symm
      _ = q := by simpa only [coords, Homeomorph.apply_symm_apply] using hleaf x
  have hrange : range (fun x ↦ (coords x).2) ⊆ {w | F.stableLabel b w = q} := by
    rintro _ ⟨x, rfl⟩
    exact hlabel x
  have hconstant := (stable_plaque_label_fiber_countable_g9 F b q hsep).isTotallyDisconnected
    _ hrange (isPreconnected_range hc.snd)
  exact fun x y ↦ hconstant (mem_range_self x) (mem_range_self y)

/-- If a compact connected family stays in one receiving box at one transverse parameter, it stays there for all nearby parameters.    If each such family lies in one separable stable leaf, its entire transverse coordinate is constant. -/
theorem stable_compact_connected_family_in_box {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) (b : F.boxIndex)
    {X T : Type*} [TopologicalSpace X] [CompactSpace X] [PreconnectedSpace X]
    [TopologicalSpace T] (H : X × T → M) (hH : Continuous H)
    (q : T → Quotient F.stablePartition)
    (hleaf : ∀ x t, Quotient.mk F.stablePartition (H (x,t)) = q t)
    (hsep : ∀ t, letI := F.stableTopology (q t);
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition (q t)))
    (t₀ : T) (hbox : ∀ x, H (x,t₀) ∈ (F.box b).image) :
    ∀ᶠ t in 𝓝 t₀, ∃ hb : ∀ x, H (x,t) ∈ (F.box b).image,
      ∀ x y, ((F.box b).chart.symm ⟨H (x,t), hb x⟩).2 =
        ((F.box b).chart.symm ⟨H (y,t), hb y⟩).2 := by
  obtain ⟨U, V, _, hV, hXU, htV, hUV⟩ :=
    generalized_tube_lemma (s := (univ : Set X)) isCompact_univ
      (t := ({t₀} : Set T)) isCompact_singleton
      ((F.box b).isOpen_image.preimage hH) (by
        rintro ⟨x,t⟩ ⟨_, ht⟩
        rcases Set.mem_singleton_iff.mp ht with rfl
        exact hbox x)
  filter_upwards [hV.mem_nhds (htV (mem_singleton t₀))] with t ht
  have hb : ∀ x, H (x,t) ∈ (F.box b).image :=
    fun x ↦ hUV ⟨hXU (mem_univ x), ht⟩
  refine ⟨hb, ?_⟩
  exact stable_connected_range_in_box F b (q t) (fun x ↦ H (x,t))
    (hH.comp (continuous_id.prodMk continuous_const)) hb (fun x ↦ hleaf x t) (hsep t)

/-- A continuous injective parametrization of an intrinsic unstable leaf has locally injective receiving transverse coordinate wherever it enters a box.    The other box coordinate is locally constant on the intrinsic leaf. -/
theorem unstable_receiving_projection_locally_injective {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) (b : F.boxIndex)
    (q : Quotient F.unstablePartition) {X : Type*} [TopologicalSpace X]
    (g : X → IntrinsicFoliationLeaf F.unstablePartition q)
    (hg : @Continuous X _ _ (F.unstableTopology q) g) (hinj : Function.Injective g)
    {Z : Type*} (proj : M → Z) (label : FoliationCoordinateDisk t → Z)
    (hlabel : Function.Injective label)
    (hπ : ∀ z (hz : z ∈ (F.box b).image), proj z = label ((F.box b).chart.symm ⟨z,hz⟩).2)
    (x : X) (hx : (g x).val ∈ (F.box b).image) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V.InjOn (fun y ↦ proj (g y).val) := by
  let := F.unstableTopology q
  let O : Set X := {y | (g y).val ∈ (F.box b).image}
  have hO : IsOpen O := (F.box b).isOpen_image.preimage
    ((F.unstable_inclusion q).comp hg)
  let g' : O → IntrinsicFoliationLeaf F.unstablePartition q := g ∘ Subtype.val
  have hc := unstable_box_first_locally_constant F b q g'
    (hg.comp continuous_subtype_val) (fun y ↦ y.property)
  let x' : O := ⟨x,hx⟩
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp
    ((IsLocallyConstant.iff_eventually_eq _).mp hc x')
  refine ⟨Subtype.val '' V,hO.isOpenMap_subtype_val V hVo,⟨x',hxV,rfl⟩,?_⟩
  rintro y ⟨y',hy,rfl⟩ z ⟨z',hz,rfl⟩ he
  apply hinj
  apply Subtype.ext
  have hsnd : proj (g y'.val).val = proj (g z'.val).val := he
  rw [hπ _ y'.property,hπ _ z'.property] at hsnd
  have hfst := (hV hy).trans (hV hz).symm
  have hp : (F.box b).chart.symm ⟨(g y'.val).val,y'.property⟩ =
      (F.box b).chart.symm ⟨(g z'.val).val,z'.property⟩ := Prod.ext hfst (hlabel hsnd)
  exact congrArg (fun z : (F.box b).image ↦ z.val)
    ((F.box b).chart.symm.injective hp)


/-- A finite holonomy chain along a stable path contained in one ambient box has the germ of the direct plaque transport in that box.    The countable-leaf argument first puts the whole path in a single receiving plaque, and the proved finite-chain comparison then applies. -/
theorem path_holonomy_in_box_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.stablePartition) :
    letI := F.stableTopology q
    SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q) →
    ∀ {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
      (H : PathHolonomyRepresentative F γ 0 1),
      (∀ r, (γ r).val ∈ (F.box b).image) →
      ∃ e : LocalPlaqueTransport F (γ 0).val (γ 1).val,
        e.box = b ∧
        (Filter.Germ.ofFun H.map : Filter.Germ (𝓝 (F.uPoint (γ 0).val))
          (F.ULeaf (γ 1).val)) = Filter.Germ.ofFun e.map := by
  let := F.stableTopology q
  intro hsep x y γ H hbox
  let c : unitInterval → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
    fun r ↦ (F.box b).chart.symm ⟨(γ r).val,hbox r⟩
  have hc : ∀ r, (c r).2 = (c 0).2 :=
    fun r ↦ stable_connected_range_in_box F b q (fun r ↦ (γ r).val)
      ((F.stable_inclusion q).comp γ.continuous) hbox (fun r ↦ (γ r).property)
      hsep r 0
  have hpoint (r : unitInterval) : ((F.box b).chart ((c r).1,(c 0).2)).val = (γ r).val := by
    rw [← hc r]
    exact congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(γ r).val,hbox r⟩)
  obtain ⟨e,heb,hef,hes,het,_⟩ := local_plaque_transport_of_box F b
    (c 0).1 (c 1).1 (c 0).2 (γ 0).val (γ 1).val (hpoint 0) (hpoint 1)
  refine ⟨e,heb,plaque_chain_germ_in_one_plaque F γ H.chain e ?_⟩
  intro r _ _
  refine ⟨(c r).1,?_⟩
  have heq := congrArg (fun i ↦ ((F.box i).chart ((c r).1,(c 0).2)).val) heb
  simpa only [het] using heq.trans (hpoint r)

end HolomorphicAnosov
