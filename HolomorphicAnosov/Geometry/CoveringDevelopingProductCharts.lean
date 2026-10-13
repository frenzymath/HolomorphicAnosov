import HolomorphicAnosov.Geometry.CoveringGlobalHolonomyDevelopingGerm

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v w k
variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u, v} s t M)

/-- A developing map constant on horizontal slices and giving global coordinates on lifted unstable
leaves admits local product charts in which it is the second projection. (Ghys, p.598) -/
theorem covering_developing_product_charts
    {E : Type w} {Z : Type k} [TopologicalSpace E] [TopologicalSpace Z]
    (p : E → M) (hp : IsCoveringMap p) (D : E → Z)
    (hDbox : ∀ (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E)),
      (∀ z, p (L z) = ((F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)))
    (R : E → E → Prop)
    (UL : ∀ x : E, F.ULeaf (p x) → E)
    (hUL : ∀ x, Continuous (UL x))
    (hproj : ∀ x z, p (UL x z) = z.val)
    (hpoint : ∀ x, UL x (F.uPoint (p x)) = x)
    (hrange : ∀ x, Set.range (UL x) = {y | Relation.EqvGen R x y})
    (coordinate : ∀ x : E, F.ULeaf (p x) ≃ₜ Z)
    (hcoord : ∀ x z, coordinate x z = D (UL x z))
    (x : E) :
    ∃ (O : TopologicalSpace.Opens E) (W : TopologicalSpace.Opens Z)
      (H : (FoliationCoordinateDisk s × W) ≃ₜ O),
      x ∈ O ∧ D x ∈ W ∧
      (∀ r z, D (H (r, z)).val = z.val) ∧
      (∀ (e : O) (z : W), Relation.EqvGen R e.val
        (H ((H.symm e).1, z)).val) ∧
      ∃ j : FoliationCoordinateDisk s →
          IntrinsicFoliationLeaf F.stablePartition (Quotient.mk F.stablePartition (p x)),
        IsOpenEmbedding j ∧
        (∀ r z, z.val = D x → p (H (r, z)).val = (j r).val) ∧
        (∃ (i : F.boxIndex) (w : FoliationCoordinateDisk t),
          ∀ r, (j r).val = ((F.box i).chart (r, w)).val) := by
  have hvertical (i : F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk t, E))
      (hL : ∀ z, p (L z) = ((F.box i).chart z).val)
      (u : FoliationCoordinateDisk s) (v : FoliationCoordinateDisk t) :
      IsOpenEmbedding (fun w ↦ D (L (u, w))) ∧
      (∀ w, Relation.EqvGen R (L (u, v)) (L (u, w))) := by
    let y := L (u, v)
    have hlabel : F.unstableLabel i u = Quotient.mk F.unstablePartition (p y) :=
      (F.unstable_label i u v).symm.trans (congrArg (Quotient.mk _) (hL (u, v)).symm)
    let j : FoliationCoordinateDisk t → F.ULeaf (p y) := fun w ↦
      ⟨((F.box i).chart (u, w)).val, (F.unstable_label i u w).trans hlabel⟩
    have hj : IsOpenEmbedding j := by
      have aux (q : Quotient F.unstablePartition) (hq : F.unstableLabel i u = q) :
          letI := F.unstableTopology q
          IsOpenEmbedding (fun w : FoliationCoordinateDisk t ↦
            (⟨((F.box i).chart (u, w)).val,
              (F.unstable_label i u w).trans hq⟩ : IntrinsicFoliationLeaf F.unstablePartition q)) := by
        subst q
        exact F.unstable_plaque i u
      exact aux _ hlabel
    let : PreconnectedSpace (FoliationCoordinateDisk t) :=
      Subtype.preconnectedSpace (convex_ball (0 : Fin t → ℝ) 1).isPreconnected
    have heq : (fun w ↦ L (u, w)) = UL y ∘ j := hp.eq_of_comp_eq
      (L.continuous.comp (continuous_const.prodMk continuous_id))
      ((hUL y).comp hj.continuous)
      (by funext w; exact (hL (u, w)).trans (hproj y (j w)).symm) v (by
        have hjv : j v = F.uPoint (p y) := Subtype.ext (hL (u, v)).symm
        simpa only [Function.comp_apply, hjv] using (hpoint y).symm)
    constructor
    · have hd : (fun w ↦ D (L (u, w))) = coordinate y ∘ j := by
        funext w
        exact (congrArg D (congrFun heq w)).trans (hcoord y (j w)).symm
      rw [hd]
      exact (coordinate y).isOpenEmbedding.comp hj
    · intro w
      have hm : L (u, w) ∈ Set.range (UL y) := ⟨j w, (congrFun heq w).symm⟩
      rw [hrange y] at hm
      exact hm
  obtain ⟨i, hi⟩ := F.cover (p x)
  let q := (F.box i).chart.symm ⟨p x, hi⟩
  obtain ⟨L, hLpoint, hL⟩ := covering_foliation_box_lift F p hp i q x
    (congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨p x, hi⟩)).symm
  have hLc : IsOpenEmbedding (p ∘ L) := by
    rw [show p ∘ L = fun z ↦ ((F.box i).chart z).val from funext hL]
    exact (F.box i).isOpen_image.isOpenEmbedding_subtypeVal.comp
      (F.box i).chart.isOpenEmbedding
  have hLo := hp.isLocalHomeomorph.isOpenEmbedding_of_comp hLc L.continuous
  let k : FoliationCoordinateDisk t → Z := fun w ↦ D (L (q.1, w))
  have hk : IsOpenEmbedding k := (hvertical i L hL q.1 q.2).1
  let O : TopologicalSpace.Opens E := ⟨Set.range L, hLo.isOpen_range⟩
  let W : TopologicalSpace.Opens Z := ⟨Set.range k, hk.isOpen_range⟩
  let K : FoliationCoordinateDisk t ≃ₜ W := hk.isEmbedding.toHomeomorph
  let LH : (FoliationCoordinateDisk s × FoliationCoordinateDisk t) ≃ₜ O :=
    hLo.isEmbedding.toHomeomorph
  let H : (FoliationCoordinateDisk s × W) ≃ₜ O :=
    (Homeomorph.prodCongr (Homeomorph.refl _) K.symm).trans LH
  have hH (r : FoliationCoordinateDisk s) (z : W) :
      (H (r, z)).val = L (r, K.symm z) := rfl
  have hK (z : W) : k (K.symm z) = z.val :=
    congrArg Subtype.val (K.apply_symm_apply z)
  refine ⟨O, W, H, ⟨q, hLpoint⟩, ⟨q.2, congrArg D hLpoint⟩, ?_, ?_, ?_⟩
  · intro r z
    rw [hH, hDbox i L hL r q.1]
    exact hK z
  · intro e z
    have he := congrArg Subtype.val (H.apply_symm_apply e)
    rw [← he, hH]
    exact (hvertical i L hL (H.symm e).1 (K.symm (H.symm e).2)).2 (K.symm z)
  · have hlabel : F.stableLabel i q.2 = Quotient.mk F.stablePartition (p x) :=
      (F.stable_label i q.1 q.2).symm.trans
        (congrArg (Quotient.mk _) ((hL q).symm.trans (congrArg p hLpoint)))
    let j : FoliationCoordinateDisk s →
        IntrinsicFoliationLeaf F.stablePartition (Quotient.mk F.stablePartition (p x)) :=
      fun r ↦ ⟨((F.box i).chart (r, q.2)).val, (F.stable_label i r q.2).trans hlabel⟩
    have hj : IsOpenEmbedding j := by
      have aux (Q : Quotient F.stablePartition) (hQ : F.stableLabel i q.2 = Q) :
          letI := F.stableTopology Q
          IsOpenEmbedding (fun r : FoliationCoordinateDisk s ↦
            (⟨((F.box i).chart (r, q.2)).val,
              (F.stable_label i r q.2).trans hQ⟩ : IntrinsicFoliationLeaf F.stablePartition Q)) := by
        subst Q
        exact F.stable_plaque i q.2
      exact aux _ hlabel
    refine ⟨j, hj, ?_, i, q.2, fun _ ↦ rfl⟩
    intro r z hz
    have hzz : K.symm z = q.2 := hk.injective ((hK z).trans
      (hz.trans (congrArg D hLpoint).symm))
    rw [hH, hzz]
    exact hL (r, q.2)
end HolomorphicAnosov
namespace HolomorphicAnosov
/-- A continuous leaf lift onto a fibre is an embedding if local product charts on the fibre project
through continuous intrinsic leaf charts. -/
theorem fibre_lift_embedding_of_product_charts
    {L E M Z V : Type*} [TopologicalSpace L] [TopologicalSpace E]
    [TopologicalSpace Z] [TopologicalSpace V]
    (p : E → M) (inc : L → M) (hi : Function.Injective inc)
    (D : E → Z) (z₀ : Z) (l : L → E) (hl : Continuous l)
    (hproj : ∀ a, p (l a) = inc a)
    (hrange : Set.range l = {y | D y = z₀})
    (hcharts : ∀ y : {y // D y = z₀},
      ∃ (O : TopologicalSpace.Opens E) (W : TopologicalSpace.Opens Z)
        (H : (V × W) ≃ₜ O) (j : V → L),
        y.val ∈ O ∧ Continuous j ∧
        (∀ r z, D (H (r, z)).val = z.val) ∧
        (∀ r z, z.val = z₀ → p (H (r, z)).val = inc (j r))) :
    IsEmbedding l := by
  classical
  let f : L → {y // D y = z₀} := fun a ↦ ⟨l a, by
    have h : l a ∈ Set.range l := Set.mem_range_self a
    rwa [hrange] at h⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact hi ((hproj a).symm.trans
        ((congrArg p (congrArg Subtype.val h)).trans (hproj b)))
    · intro y
      obtain ⟨a, ha⟩ := (show y.val ∈ Set.range l by rw [hrange]; exact y.property)
      exact ⟨a, Subtype.ext ha⟩
  let e := Equiv.ofBijective f hf
  have hinv : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨O, W, H, j, hy, hj, hD, hp⟩ := hcharts y
    let U : Set {y // D y = z₀} := {y | y.val ∈ O}
    have hU : IsOpen U := O.isOpen.preimage continuous_subtype_val
    let yU : U := ⟨y, hy⟩
    let c : U → O := fun a ↦ ⟨a.val.val, a.property⟩
    have hc : Continuous c := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have heq : (fun a : U ↦ e.symm a.val) = fun a ↦ j (H.symm (c a)).1 := by
      funext a
      apply hi
      have hea : l (e.symm a.val) = a.val.val := congrArg Subtype.val (e.apply_symm_apply a.val)
      have hh := congrArg Subtype.val (H.apply_symm_apply (c a))
      have hz : ((H.symm (c a)).2).val = z₀ := by
        rw [← hD (H.symm (c a)).1 (H.symm (c a)).2]
        simpa only [Prod.mk.eta, Homeomorph.apply_symm_apply] using a.val.property
      calc
        inc (e.symm a.val) = p a.val.val := (hproj _).symm.trans (congrArg p hea)
        _ = p (H ((H.symm (c a)).1, (H.symm (c a)).2)).val := (congrArg p hh).symm
        _ = inc (j (H.symm (c a)).1) := hp _ _ hz
    have hh : Continuous (fun a : U ↦ e.symm a.val) := by
      rw [heq]
      exact hj.comp ((H.symm.continuous.comp hc).fst)
    exact (hU.isOpenEmbedding_subtypeVal.continuousAt_iff).mp (hh.continuousAt (x := yU))
  let H : L ≃ₜ {y // D y = z₀} :=
    { toEquiv := e, continuous_toFun := hl.subtype_mk _, continuous_invFun := hinv }
  exact IsEmbedding.subtypeVal.comp H.isEmbedding
end HolomorphicAnosov
