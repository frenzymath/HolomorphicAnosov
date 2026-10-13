import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import Mathlib.Topology.Maps.Proper.Basic
import HolomorphicAnosov.Topology.CoordinateLeafSaturation

/-! This file proves openness, connectedness, and developing-map injectivity on the first unstable
saturation of a complete lifted stable leaf. Its developing image is the complement of a
continuous missing graph over a punctured projective line (Ghys, Lemma 5.2, p. 599). -/


noncomputable section
open Set _root_.Topology
open scoped ContDiff

namespace HolomorphicAnosov.Ghys

universe u v w

attribute [local instance] complex_isManifold_real



/-- The first unstable saturation of a complete lifted stable leaf is open and connected, and the
developing map is injective there. Its image is a family of vertical projective lines punctured
by a continuous missing-value map, with biholomorphic unstable leaf restrictions (Ghys, Lemma
5.2, p. 599, case `k = 1`). -/
theorem surface_developing_injective_base_stage
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D) (x : U) :
    letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
    ∃ (pole baseValue : ComplexProjectiveLine)
      (missing : C({q : ComplexProjectiveLine // q ≠ pole}, ComplexProjectiveLine)),
      (unstableSaturation D x).Nonempty ∧ IsOpen (unstableSaturation D x) ∧
      IsConnected (unstableSaturation D x) ∧
      Set.InjOn D.developingMap (unstableSaturation D x) ∧
      D.developingMap '' stableDevelopingLeaf D x =
        {q | q.1 ≠ pole ∧ q.2 = baseValue} ∧
      D.developingMap '' unstableSaturation D x =
        {q | ∃ hq : q.1 ≠ pole, q.2 ≠ missing ⟨q.1, hq⟩} ∧
      (∀ y ∈ unstableSaturation D x, ∃! z : U,
        z ∈ stableDevelopingLeaf D x ∧ y ∈ unstableDevelopingLeaf D z) ∧
      (∀ q : {q : ComplexProjectiveLine // q ≠ pole}, ∃! z : U,
        z ∈ stableDevelopingLeaf D x ∧ (D.developingMap z).1 = q.val) ∧
      (∀ (y : U) (_hy : y ∈ stableDevelopingLeaf D x),
        ∃ hq : (D.developingMap y).1 ≠ pole,
          let L := A.unstableLeaf (p y)
          letI := L.native.topology
          letI := L.complexCharts
          ∃ (lift : UnstableAsymptoticLeaf f.toHomeomorph (p y) → U)
            (e : OpenPartialHomeomorph
              (UnstableAsymptoticLeaf f.toHomeomorph (p y)) ComplexProjectiveLine),
            ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
            Function.Injective lift ∧ (∀ z, p (lift z) = z.val) ∧
            Set.range lift = unstableDevelopingLeaf D y ∧
            e.source = Set.univ ∧
            e.target = {missing ⟨(D.developingMap y).1, hq⟩}ᶜ ∧
            (∀ z, e z = (D.developingMap (lift z)).2) ∧
            ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
            ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
            Set.range (fun z ↦ D.developingMap (lift z)) =
              {q | q.1 = (D.developingMap y).1 ∧
                q.2 ≠ missing ⟨(D.developingMap y).1, hq⟩}) := by
  have complete_leaf_coordinate_injective
      (hLeaves : CompleteLiftedProjectiveLeaves D) (x : U) :
      Set.InjOn (fun y ↦ (D.developingMap y).1) (stableDevelopingLeaf D x) ∧
      Set.InjOn (fun y ↦ (D.developingMap y).2) (unstableDevelopingLeaf D x) := by
    let : MetricSpace S := A.metric.replaceTopology A.metric_topology
    constructor
    · let := (A.stableLeaf (p x)).native.topology
      obtain ⟨lift, _, _, _, hl, pole, e, hsource, _, he, _, _, _⟩ := hLeaves.1 x
      intro y hy z hz hyz
      rw [← hl] at hy hz
      obtain ⟨b, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := hz
      have hb : b ∈ e.source := hsource.symm ▸ Set.mem_univ b
      have hc : c ∈ e.source := hsource.symm ▸ Set.mem_univ c
      exact congrArg lift (e.injOn hb hc ((he b).trans (hyz.trans (he c).symm)))
    · let := (A.unstableLeaf (p x)).native.topology
      obtain ⟨lift, _, _, _, hl, pole, e, hsource, _, he, _, _, _⟩ := hLeaves.2 x
      intro y hy z hz hyz
      rw [← hl] at hy hz
      obtain ⟨b, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := hz
      have hb : b ∈ e.source := hsource.symm ▸ Set.mem_univ b
      have hc : c ∈ e.source := hsource.symm ▸ Set.mem_univ c
      exact congrArg lift (e.injOn hb hc ((he b).trans (hyz.trans (he c).symm)))
  
  have first_saturation_injective_and_unique_meeting
      (hLeaves : CompleteLiftedProjectiveLeaves D) (x : U) :
      Set.InjOn D.developingMap (unstableSaturation D x) ∧
      (∀ y ∈ unstableSaturation D x, ∃! z : U,
        z ∈ stableDevelopingLeaf D x ∧ y ∈ unstableDevelopingLeaf D z) := by
    have hstable := (complete_leaf_coordinate_injective hLeaves x).1
    have hconst {z y : U} (hy : y ∈ unstableDevelopingLeaf D z) :
        (D.developingMap y).1 = (D.developingMap z).1 :=
      connectedComponentIn_subset {t | (D.developingMap t).1 = (D.developingMap z).1} z hy
    constructor
    · rintro y ⟨b, hb, hy⟩ z ⟨c, hc, hz⟩ he
      have hbc : b = c := hstable hb hc
        ((hconst hy).symm.trans ((congrArg Prod.fst he).trans (hconst hz)))
      subst c
      exact (complete_leaf_coordinate_injective hLeaves b).2 hy hz (congrArg Prod.snd he)
    · rintro y ⟨b, hb, hy⟩
      refine ⟨b, ⟨hb, hy⟩, ?_⟩
      rintro c ⟨hc, hyc⟩
      exact hstable hc hb ((hconst hyc).symm.trans (hconst hy))
  
  have first_stable_leaf_coordinates
      (hLeaves : CompleteLiftedProjectiveLeaves D) (x : U) :
      ∃ pole : ComplexProjectiveLine,
        D.developingMap '' stableDevelopingLeaf D x =
          {q | q.1 ≠ pole ∧ q.2 = (D.developingMap x).2} ∧
        (∀ q : {q : ComplexProjectiveLine // q ≠ pole}, ∃! z : U,
          z ∈ stableDevelopingLeaf D x ∧ (D.developingMap z).1 = q.val) := by
    let : MetricSpace S := A.metric.replaceTopology A.metric_topology
    obtain ⟨lift, _, _, _, hl, pole, e, _, _, _, _, _, hrange⟩ := hLeaves.1 x
    have himage : D.developingMap '' stableDevelopingLeaf D x =
        {q | q.1 ≠ pole ∧ q.2 = (D.developingMap x).2} := by
      rw [← hl, ← Set.range_comp]
      exact hrange
    refine ⟨pole, himage, fun q ↦ ?_⟩
    have hm : (q.val, (D.developingMap x).2) ∈ D.developingMap '' stableDevelopingLeaf D x := by
      rw [himage]
      exact ⟨q.property, rfl⟩
    obtain ⟨z, hz, he⟩ := hm
    refine ⟨z, ⟨hz, congrArg Prod.fst he⟩, ?_⟩
    rintro y ⟨hy, hey⟩
    exact (complete_leaf_coordinate_injective hLeaves x).1 hy hz
      (hey.trans (congrArg Prod.fst he).symm)
  
  have first_saturation_connected (x : U) : IsConnected (unstableSaturation D x) := by
    have hself (z : U) : z ∈ unstableDevelopingLeaf D z := mem_connectedComponentIn rfl
    have hstable : x ∈ stableDevelopingLeaf D x := mem_connectedComponentIn rfl
    have hsub : stableDevelopingLeaf D x ⊆ unstableSaturation D x :=
      fun z hz ↦ ⟨z, hz, hself z⟩
    refine ⟨⟨x, hsub hstable⟩, isPreconnected_of_forall_pair ?_⟩
    rintro y ⟨b, hb, hy⟩ z ⟨c, hc, hz⟩
    refine ⟨(stableDevelopingLeaf D x ∪ unstableDevelopingLeaf D b) ∪
      unstableDevelopingLeaf D c, ?_, Or.inl (Or.inr hy), Or.inr hz, ?_⟩
    · exact Set.union_subset (Set.union_subset hsub (fun t ht ↦ ⟨b, hb, ht⟩))
        (fun t ht ↦ ⟨c, hc, ht⟩)
    · have hp : IsPreconnected (stableDevelopingLeaf D x ∪ unstableDevelopingLeaf D b) :=
        isPreconnected_connectedComponentIn.union b hb (hself b)
          isPreconnected_connectedComponentIn
      exact hp.union c (Or.inl hc) (hself c) isPreconnected_connectedComponentIn
  classical
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  obtain ⟨pole, hstable, hcoord⟩ := first_stable_leaf_coordinates hLeaves x
  obtain ⟨hinj, hmeet⟩ := first_saturation_injective_and_unique_meeting hLeaves x
  have hconn := first_saturation_connected x
  have hopen : IsOpen (unstableSaturation D x) := by
    let : LocallyConnectedSpace ComplexProjectiveLine :=
      ChartedSpace.locallyConnectedSpace (ComplexModel 1) ComplexProjectiveLine
    exact HolomorphicAnosov.Topology.isOpen_coordinate_component_saturation
      D.developingMap D.localBiholomorph.isLocalHomeomorph x
  choose point hpoint using fun q ↦ (hcoord q).exists
  have hpoint_unique (y : U) (hy : y ∈ stableDevelopingLeaf D x)
      (hq : (D.developingMap y).1 ≠ pole) :
      point ⟨(D.developingMap y).1, hq⟩ = y := by
    exact (complete_leaf_coordinate_injective hLeaves x).1
      (hpoint _).1 hy (hpoint _).2
  have hex (y : U) : ∃ c : ComplexProjectiveLine,
      D.developingMap '' unstableDevelopingLeaf D y =
        {q | q.1 = (D.developingMap y).1 ∧ q.2 ≠ c} := by
    obtain ⟨lift, _, _, _, hr, c, e, _, _, _, _, _, he⟩ := hLeaves.2 y
    exact ⟨c, by rw [← hr, ← Set.range_comp]; exact he⟩
  choose omitted homitted using hex
  let missing : {q : ComplexProjectiveLine // q ≠ pole} → ComplexProjectiveLine :=
    fun q ↦ omitted (point q)
  have hgraph : D.developingMap '' unstableSaturation D x =
      {q | ∃ hq : q.1 ≠ pole, q.2 ≠ missing ⟨q.1, hq⟩} := by
    ext q
    constructor
    · rintro ⟨y, ⟨z, hz, hy⟩, rfl⟩
      have hz' : (D.developingMap z).1 ≠ pole := by
        have hm : D.developingMap z ∈ D.developingMap '' stableDevelopingLeaf D x :=
          ⟨z, hz, rfl⟩
        rw [hstable] at hm
        exact hm.1
      have hm : D.developingMap y ∈ D.developingMap '' unstableDevelopingLeaf D z :=
        ⟨y, hy, rfl⟩
      rw [homitted z] at hm
      refine ⟨hm.1.trans_ne hz', ?_⟩
      have he : point ⟨(D.developingMap y).1, hm.1.trans_ne hz'⟩ = z := by
        rw [show (⟨(D.developingMap y).1, hm.1.trans_ne hz'⟩ :
          {q : ComplexProjectiveLine // q ≠ pole}) = ⟨(D.developingMap z).1, hz'⟩
          from Subtype.ext hm.1]
        exact hpoint_unique z hz hz'
      simpa only [missing, he] using hm.2
    · rintro ⟨hq, hq'⟩
      have hm : q ∈ D.developingMap '' unstableDevelopingLeaf D (point ⟨q.1, hq⟩) := by
        rw [homitted]
        exact ⟨(hpoint ⟨q.1, hq⟩).2.symm, hq'⟩
      obtain ⟨y, hy, he⟩ := hm
      exact ⟨y, ⟨point ⟨q.1, hq⟩, (hpoint _).1, hy⟩, he⟩
  have hcontinuous : Continuous missing := by
    let : CompactSpace ComplexProjectiveLine :=
      NativeProjectiveTopology.compact_native_projective_line
    apply continuous_of_isClosed_graph
    have ho := D.localBiholomorph.isOpenMap _ hopen
    have hp := ho.preimage (continuous_subtype_val.prodMap continuous_id :
      Continuous (fun q : {q : ComplexProjectiveLine // q ≠ pole} × ComplexProjectiveLine ↦
        (q.1.val, q.2)))
    have he : (fun q : {q : ComplexProjectiveLine // q ≠ pole} × ComplexProjectiveLine ↦
        (q.1.val, q.2)) ⁻¹' (D.developingMap '' unstableSaturation D x) =
        missing.graphᶜ := by
      ext q
      simp only [hgraph, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff]
      constructor
      · rintro ⟨hq, hne⟩ heq
        exact hne heq.symm
      · intro hne
        exact ⟨q.1.property, Ne.symm hne⟩
    change IsOpen ((fun q : {q : ComplexProjectiveLine // q ≠ pole} × ComplexProjectiveLine ↦
      (q.1.val, q.2)) ⁻¹' (D.developingMap '' unstableSaturation D x)) at hp
    rw [he] at hp
    exact isOpen_compl_iff.mp hp
  refine ⟨pole, (D.developingMap x).2, ⟨missing, hcontinuous⟩,
    hconn.nonempty, hopen, hconn, hinj, hstable, hgraph, hmeet, hcoord, ?_⟩
  intro y hy
  have hq : (D.developingMap y).1 ≠ pole := by
    have hm : D.developingMap y ∈ D.developingMap '' stableDevelopingLeaf D x := ⟨y, hy, rfl⟩
    rw [hstable] at hm
    exact hm.1
  refine ⟨hq, ?_⟩
  obtain ⟨lift, hl, hin, hp, hr, c, e, hs, ht, he, hd, hi, him⟩ := hLeaves.2 y
  have heq : c = omitted y := by
    by_contra hn
    have hm : ((D.developingMap y).1, c) ∈
        D.developingMap '' unstableDevelopingLeaf D y := by
      rw [homitted y]
      exact ⟨rfl, hn⟩
    rw [← hr, ← Set.range_comp] at hm
    change ((D.developingMap y).1, c) ∈ Set.range (fun z ↦ D.developingMap (lift z)) at hm
    rw [him] at hm
    exact hm.2 rfl
  have heq' : c = missing ⟨(D.developingMap y).1, hq⟩ := by
    simpa only [missing, hpoint_unique y hy hq] using heq
  rw [heq'] at ht him
  exact ⟨lift, e, hl, hin, hp, hr, hs, ht, he, hd, hi, him⟩


end HolomorphicAnosov.Ghys
