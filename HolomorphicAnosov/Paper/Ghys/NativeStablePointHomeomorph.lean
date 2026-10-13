import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.LocallyConnected

/-! This file compares the intrinsic stable leaves supplied by two native identifications of the same dynamics (HPS, §7; Ghys, §§2, 5). -/

noncomputable section
open Set Topology _root_.Topology Filter
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u

/-- Two native identifications of the same dynamics induce point-preserving homeomorphisms between their intrinsic stable carriers. (HPS, §7; Ghys, §§2, 5) -/
theorem native_stable_point_homeomorph
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification f Ps Pu s' t') (x : M) :
    letI := A.realAmbientCharts
    letI := B.realAmbientCharts
    letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
    letI := B.F.stableTopology (Quotient.mk B.F.stablePartition x)
    ∃ e : (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)) ≃ₜ (IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)),
      ∀ z : (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)), (e z).val = z.val := by
  have labels_countable_A :
      letI := A.realAmbientCharts
      ∀ i : A.F.boxIndex,
        {z : FoliationCoordinateDisk t |
          A.F.stableLabel i z = Quotient.mk A.F.stablePartition x}.Countable := by
    let := A.realAmbientCharts
    intro i
    let q := Quotient.mk A.F.stablePartition x
    let := A.F.stableTopology q
    let := A.stableTopology x
    let : SecondCountableTopology (StableAsymptoticLeaf f x) :=
      (A.nativeS x).secondCountable
    let : SecondCountableTopology ((IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x))) :=
      (A.stableClassHomeomorph x).secondCountableTopology
    let Z := {z : FoliationCoordinateDisk t // A.F.stableLabel i z = q}
    let plaque : Z → FoliationCoordinateDisk s → (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)) := fun z w ↦
      ⟨((A.F.box i).chart (w, z.val)).val, (A.F.stable_label i w z.val).trans z.property⟩
    have hopen_aux (z : FoliationCoordinateDisk t) (q' : Quotient A.F.stablePartition)
        (hz : A.F.stableLabel i z = q') :
        letI := A.F.stableTopology q'
        IsOpen (Set.range (fun w : FoliationCoordinateDisk s ↦
          (⟨((A.F.box i).chart (w, z)).val, (A.F.stable_label i w z).trans hz⟩ :
            IntrinsicFoliationLeaf A.F.stablePartition q'))) := by
      subst q'
      let := A.F.stableTopology (A.F.stableLabel i z)
      exact (A.F.stable_plaque i z).isOpen_range
    have hopen : ∀ z : Z, IsOpen (Set.range (plaque z)) :=
      fun z ↦ hopen_aux z.val q z.property
    have hne : ∀ z : Z, (Set.range (plaque z)).Nonempty := by
      intro z
      exact ⟨plaque z ⟨0, by simp⟩, ⟨⟨0, by simp⟩, rfl⟩⟩
    have hdis : Pairwise (fun z z' : Z ↦ Disjoint (Set.range (plaque z)) (Set.range (plaque z'))) := by
      intro z z' hne
      apply Set.disjoint_left.mpr
      rintro y ⟨w, hw⟩ ⟨w', hw'⟩
      apply hne
      apply Subtype.ext
      have hval := congrArg Subtype.val (hw.trans hw'.symm)
      have heq := (A.F.box i).chart.injective (Subtype.ext hval)
      exact congrArg Prod.snd heq
    have hcount : (Set.univ : Set Z).Countable :=
      Set.PairwiseDisjoint.countable_of_isOpen
        (fun _ _ _ _ h ↦ hdis h) (fun z _ ↦ hopen z) (fun z _ ↦ hne z)
    have : Countable Z := Set.countable_univ_iff.mp hcount
    exact @Set.to_countable _ _ (show Countable Z from inferInstance)
  have continuous_intrinsic_A {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X] :
      letI := A.realAmbientCharts
      letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
      ∀ g : X → (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)), Continuous (fun z ↦ (g z).val) → Continuous g := by
    let := A.realAmbientCharts
    let := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
    intro g hg
    apply continuous_iff_continuousAt.mpr
    intro a
    obtain ⟨i, hi⟩ := A.F.cover (g a).val
    have hn : (fun z ↦ (g z).val) ⁻¹' (A.F.box i).image ∈ 𝓝 a :=
      ((A.F.box i).isOpen_image.preimage hg).mem_nhds hi
    obtain ⟨V, ⟨hV, haV, hcV⟩, hsub⟩ :=
      (LocallyConnectedSpace.open_connected_basis a).mem_iff.mp hn
    let : PreconnectedSpace V := Subtype.preconnectedSpace hcV.isPreconnected
    let u : V → ↥(A.F.box i).image := fun z ↦ ⟨(g z.val).val, hsub z.property⟩
    have hu : Continuous u := (hg.comp continuous_subtype_val).subtype_mk _
    let coords : V → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
      fun z ↦ (A.F.box i).chart.symm (u z)
    have hcoords : Continuous coords := (A.F.box i).chart.symm.continuous.comp hu
    have hr : Set.range (fun z : V ↦ (coords z).2) ⊆
        {w | A.F.stableLabel i w = Quotient.mk A.F.stablePartition x} := by
      rintro w ⟨z, rfl⟩
      have h := A.F.stable_label i (coords z).1 (coords z).2
      rw [Prod.mk.eta] at h
      change Quotient.mk _ ((A.F.box i).chart ((A.F.box i).chart.symm (u z))).val = _ at h
      rw [(A.F.box i).chart.apply_symm_apply] at h
      exact h.symm.trans (g z.val).property
    have hconst := (labels_countable_A i).isTotallyDisconnected
      (Set.range (fun z : V ↦ (coords z).2)) hr
      (isPreconnected_range (continuous_snd.comp hcoords))
    let aV : V := ⟨a, haV⟩
    have hz : ∀ z : V, (coords z).2 = (coords aV).2 :=
      fun z ↦ hconst ⟨z, rfl⟩ ⟨aV, rfl⟩
    have hlabel := hr ⟨aV, rfl⟩
    have hplaque (w : FoliationCoordinateDisk t) (q : Quotient A.F.stablePartition)
        (hw : A.F.stableLabel i w = q) :
        letI := A.F.stableTopology q
        Continuous (fun z : FoliationCoordinateDisk s ↦
          (⟨((A.F.box i).chart (z, w)).val, (A.F.stable_label i z w).trans hw⟩ :
            IntrinsicFoliationLeaf A.F.stablePartition q)) := by
      subst q
      let := A.F.stableTopology (A.F.stableLabel i w)
      exact (A.F.stable_plaque i w).continuous
    have hc : Continuous (fun z : V ↦ g z.val) := by
      convert (hplaque (coords aV).2 _ hlabel).comp (continuous_fst.comp hcoords) using 1
      funext z
      apply Subtype.ext
      change (g z.val).val = ((A.F.box i).chart ((coords z).1, (coords aV).2)).val
      rw [← hz z, Prod.mk.eta]
      exact (congrArg Subtype.val ((A.F.box i).chart.apply_symm_apply (u z))).symm
    exact (hV.isOpenEmbedding_subtypeVal.continuousAt_iff).mp (hc.continuousAt (x := aV))
  have labels_countable_B :
      letI := B.realAmbientCharts
      ∀ i : B.F.boxIndex,
        {z : FoliationCoordinateDisk t' |
          B.F.stableLabel i z = Quotient.mk B.F.stablePartition x}.Countable := by
    let := B.realAmbientCharts
    intro i
    let q := Quotient.mk B.F.stablePartition x
    let := B.F.stableTopology q
    let := B.stableTopology x
    let : SecondCountableTopology (StableAsymptoticLeaf f x) :=
      (B.nativeS x).secondCountable
    let : SecondCountableTopology ((IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x))) :=
      (B.stableClassHomeomorph x).secondCountableTopology
    let Z := {z : FoliationCoordinateDisk t' // B.F.stableLabel i z = q}
    let plaque : Z → FoliationCoordinateDisk s' → (IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)) := fun z w ↦
      ⟨((B.F.box i).chart (w, z.val)).val, (B.F.stable_label i w z.val).trans z.property⟩
    have hopen_aux (z : FoliationCoordinateDisk t') (q' : Quotient B.F.stablePartition)
        (hz : B.F.stableLabel i z = q') :
        letI := B.F.stableTopology q'
        IsOpen (Set.range (fun w : FoliationCoordinateDisk s' ↦
          (⟨((B.F.box i).chart (w, z)).val, (B.F.stable_label i w z).trans hz⟩ :
            IntrinsicFoliationLeaf B.F.stablePartition q'))) := by
      subst q'
      let := B.F.stableTopology (B.F.stableLabel i z)
      exact (B.F.stable_plaque i z).isOpen_range
    have hopen : ∀ z : Z, IsOpen (Set.range (plaque z)) :=
      fun z ↦ hopen_aux z.val q z.property
    have hne : ∀ z : Z, (Set.range (plaque z)).Nonempty := by
      intro z
      exact ⟨plaque z ⟨0, by simp⟩, ⟨⟨0, by simp⟩, rfl⟩⟩
    have hdis : Pairwise (fun z z' : Z ↦ Disjoint (Set.range (plaque z)) (Set.range (plaque z'))) := by
      intro z z' hne
      apply Set.disjoint_left.mpr
      rintro y ⟨w, hw⟩ ⟨w', hw'⟩
      apply hne
      apply Subtype.ext
      have hval := congrArg Subtype.val (hw.trans hw'.symm)
      have heq := (B.F.box i).chart.injective (Subtype.ext hval)
      exact congrArg Prod.snd heq
    have hcount : (Set.univ : Set Z).Countable :=
      Set.PairwiseDisjoint.countable_of_isOpen
        (fun _ _ _ _ h ↦ hdis h) (fun z _ ↦ hopen z) (fun z _ ↦ hne z)
    have : Countable Z := Set.countable_univ_iff.mp hcount
    exact @Set.to_countable _ _ (show Countable Z from inferInstance)
  have continuous_intrinsic_B {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X] :
      letI := B.realAmbientCharts
      letI := B.F.stableTopology (Quotient.mk B.F.stablePartition x)
      ∀ g : X → (IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)), Continuous (fun z ↦ (g z).val) → Continuous g := by
    let := B.realAmbientCharts
    let := B.F.stableTopology (Quotient.mk B.F.stablePartition x)
    intro g hg
    apply continuous_iff_continuousAt.mpr
    intro a
    obtain ⟨i, hi⟩ := B.F.cover (g a).val
    have hn : (fun z ↦ (g z).val) ⁻¹' (B.F.box i).image ∈ 𝓝 a :=
      ((B.F.box i).isOpen_image.preimage hg).mem_nhds hi
    obtain ⟨V, ⟨hV, haV, hcV⟩, hsub⟩ :=
      (LocallyConnectedSpace.open_connected_basis a).mem_iff.mp hn
    let : PreconnectedSpace V := Subtype.preconnectedSpace hcV.isPreconnected
    let u : V → ↥(B.F.box i).image := fun z ↦ ⟨(g z.val).val, hsub z.property⟩
    have hu : Continuous u := (hg.comp continuous_subtype_val).subtype_mk _
    let coords : V → FoliationCoordinateDisk s' × FoliationCoordinateDisk t' :=
      fun z ↦ (B.F.box i).chart.symm (u z)
    have hcoords : Continuous coords := (B.F.box i).chart.symm.continuous.comp hu
    have hr : Set.range (fun z : V ↦ (coords z).2) ⊆
        {w | B.F.stableLabel i w = Quotient.mk B.F.stablePartition x} := by
      rintro w ⟨z, rfl⟩
      have h := B.F.stable_label i (coords z).1 (coords z).2
      rw [Prod.mk.eta] at h
      change Quotient.mk _ ((B.F.box i).chart ((B.F.box i).chart.symm (u z))).val = _ at h
      rw [(B.F.box i).chart.apply_symm_apply] at h
      exact h.symm.trans (g z.val).property
    have hconst := (labels_countable_B i).isTotallyDisconnected
      (Set.range (fun z : V ↦ (coords z).2)) hr
      (isPreconnected_range (continuous_snd.comp hcoords))
    let aV : V := ⟨a, haV⟩
    have hz : ∀ z : V, (coords z).2 = (coords aV).2 :=
      fun z ↦ hconst ⟨z, rfl⟩ ⟨aV, rfl⟩
    have hlabel := hr ⟨aV, rfl⟩
    have hplaque (w : FoliationCoordinateDisk t') (q : Quotient B.F.stablePartition)
        (hw : B.F.stableLabel i w = q) :
        letI := B.F.stableTopology q
        Continuous (fun z : FoliationCoordinateDisk s' ↦
          (⟨((B.F.box i).chart (z, w)).val, (B.F.stable_label i z w).trans hw⟩ :
            IntrinsicFoliationLeaf B.F.stablePartition q)) := by
      subst q
      let := B.F.stableTopology (B.F.stableLabel i w)
      exact (B.F.stable_plaque i w).continuous
    have hc : Continuous (fun z : V ↦ g z.val) := by
      convert (hplaque (coords aV).2 _ hlabel).comp (continuous_fst.comp hcoords) using 1
      funext z
      apply Subtype.ext
      change (g z.val).val = ((B.F.box i).chart ((coords z).1, (coords aV).2)).val
      rw [← hz z, Prod.mk.eta]
      exact (congrArg Subtype.val ((B.F.box i).chart.apply_symm_apply (u z))).symm
    exact (hV.isOpenEmbedding_subtypeVal.continuousAt_iff).mp (hc.continuousAt (x := aV))
  let := A.realAmbientCharts
  let := B.realAmbientCharts
  let := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
  let := B.F.stableTopology (Quotient.mk B.F.stablePartition x)
  let eA : (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)) ≃ StableAsymptoticLeaf f x :=
    letI := A.stableTopology x
    (A.stableClassHomeomorph x).toEquiv
  let eB : (IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)) ≃ StableAsymptoticLeaf f x :=
    letI := B.stableTopology x
    (B.stableClassHomeomorph x).toEquiv
  let e := eA.trans eB.symm
  have he : ∀ z : (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)), (e z).val = z.val := by
    intro z
    have h := B.stable_points x (e z)
    have h' : (eB (e z)).val = (eA z).val := congrArg Subtype.val (eB.apply_symm_apply (eA z))
    exact h.symm.trans (h'.trans (A.stable_points x z))
  have he' : ∀ z : (IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)), (e.symm z).val = z.val := by
    intro z
    simpa using (he (e.symm z)).symm
  let := A.F.stableCharts (Quotient.mk A.F.stablePartition x)
  let := B.F.stableCharts (Quotient.mk B.F.stablePartition x)
  let : LocallyConnectedSpace ((IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x))) := ChartedSpace.locallyConnectedSpace (Fin s → ℝ) ((IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)))
  let : LocallyConnectedSpace ((IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x))) := ChartedSpace.locallyConnectedSpace (Fin s' → ℝ) ((IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition x)))
  have hc : Continuous e := continuous_intrinsic_B e (by
    simpa only [he] using A.F.stable_inclusion (Quotient.mk A.F.stablePartition x))
  have hc' : Continuous e.symm := continuous_intrinsic_A e.symm (by
    simpa only [he'] using B.F.stable_inclusion (Quotient.mk B.F.stablePartition x))
  exact ⟨⟨e, hc, hc'⟩, he⟩

end HolomorphicAnosov.Ghys
