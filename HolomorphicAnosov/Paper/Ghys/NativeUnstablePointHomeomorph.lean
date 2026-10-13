import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.LocallyConnected

/-! This file compares the intrinsic unstable leaves supplied by two native identifications of the same dynamics (HPS, §7; Ghys, §§2, 5). -/

noncomputable section
open Set Topology _root_.Topology Filter
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u

/-- Two native identifications of the same dynamics induce point-preserving homeomorphisms between their intrinsic unstable carriers. (HPS, §7; Ghys, §§2, 5) -/
theorem native_unstable_point_homeomorph
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification f Ps Pu s' t') (x : M) :
    letI := A.realAmbientCharts
    letI := B.realAmbientCharts
    ∃ e : A.F.ULeaf x ≃ₜ B.F.ULeaf x,
      ∀ z : A.F.ULeaf x, (e z).val = z.val := by
  have labels_countable_A :
      letI := A.realAmbientCharts
      ∀ i : A.F.boxIndex,
        {z : FoliationCoordinateDisk s |
          A.F.unstableLabel i z = Quotient.mk A.F.unstablePartition x}.Countable := by
    let := A.realAmbientCharts
    intro i
    let q := Quotient.mk A.F.unstablePartition x
    let := A.F.unstableTopology q
    let := A.unstableTopology x
    let : SecondCountableTopology (UnstableAsymptoticLeaf f x) :=
      (A.nativeU x).secondCountable
    let : SecondCountableTopology (A.F.ULeaf x) :=
      (A.unstableClassHomeomorph x).secondCountableTopology
    let Z := {z : FoliationCoordinateDisk s // A.F.unstableLabel i z = q}
    let plaque : Z → FoliationCoordinateDisk t → A.F.ULeaf x := fun z w ↦
      ⟨((A.F.box i).chart (z.val, w)).val, (A.F.unstable_label i z.val w).trans z.property⟩
    have hopen_aux (z : FoliationCoordinateDisk s) (q' : Quotient A.F.unstablePartition)
        (hz : A.F.unstableLabel i z = q') :
        letI := A.F.unstableTopology q'
        IsOpen (Set.range (fun w : FoliationCoordinateDisk t ↦
          (⟨((A.F.box i).chart (z, w)).val, (A.F.unstable_label i z w).trans hz⟩ :
            IntrinsicFoliationLeaf A.F.unstablePartition q'))) := by
      subst q'
      let := A.F.unstableTopology (A.F.unstableLabel i z)
      exact (A.F.unstable_plaque i z).isOpen_range
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
      exact congrArg Prod.fst heq
    have hcount : (Set.univ : Set Z).Countable :=
      Set.PairwiseDisjoint.countable_of_isOpen
        (fun _ _ _ _ h ↦ hdis h) (fun z _ ↦ hopen z) (fun z _ ↦ hne z)
    have : Countable Z := Set.countable_univ_iff.mp hcount
    exact @Set.to_countable _ _ (show Countable Z from inferInstance)
  have continuous_intrinsic_A {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X] :
      letI := A.realAmbientCharts
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      ∀ g : X → A.F.ULeaf x, Continuous (fun z ↦ (g z).val) → Continuous g := by
    let := A.realAmbientCharts
    let := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
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
    have hr : Set.range (fun z : V ↦ (coords z).1) ⊆
        {w | A.F.unstableLabel i w = Quotient.mk A.F.unstablePartition x} := by
      rintro w ⟨z, rfl⟩
      have h := A.F.unstable_label i (coords z).1 (coords z).2
      rw [Prod.mk.eta] at h
      change Quotient.mk _ ((A.F.box i).chart ((A.F.box i).chart.symm (u z))).val = _ at h
      rw [(A.F.box i).chart.apply_symm_apply] at h
      exact h.symm.trans (g z.val).property
    have hconst := (labels_countable_A i).isTotallyDisconnected
      (Set.range (fun z : V ↦ (coords z).1)) hr
      (isPreconnected_range (continuous_fst.comp hcoords))
    let aV : V := ⟨a, haV⟩
    have hz : ∀ z : V, (coords z).1 = (coords aV).1 :=
      fun z ↦ hconst ⟨z, rfl⟩ ⟨aV, rfl⟩
    have hlabel := hr ⟨aV, rfl⟩
    have hplaque (w : FoliationCoordinateDisk s) (q : Quotient A.F.unstablePartition)
        (hw : A.F.unstableLabel i w = q) :
        letI := A.F.unstableTopology q
        Continuous (fun z : FoliationCoordinateDisk t ↦
          (⟨((A.F.box i).chart (w, z)).val, (A.F.unstable_label i w z).trans hw⟩ :
            IntrinsicFoliationLeaf A.F.unstablePartition q)) := by
      subst q
      let := A.F.unstableTopology (A.F.unstableLabel i w)
      exact (A.F.unstable_plaque i w).continuous
    have hc : Continuous (fun z : V ↦ g z.val) := by
      convert (hplaque (coords aV).1 _ hlabel).comp (continuous_snd.comp hcoords) using 1
      funext z
      apply Subtype.ext
      change (g z.val).val = ((A.F.box i).chart ((coords aV).1, (coords z).2)).val
      rw [← hz z, Prod.mk.eta]
      exact (congrArg Subtype.val ((A.F.box i).chart.apply_symm_apply (u z))).symm
    exact (hV.isOpenEmbedding_subtypeVal.continuousAt_iff).mp (hc.continuousAt (x := aV))
  have labels_countable_B :
      letI := B.realAmbientCharts
      ∀ i : B.F.boxIndex,
        {z : FoliationCoordinateDisk s' |
          B.F.unstableLabel i z = Quotient.mk B.F.unstablePartition x}.Countable := by
    let := B.realAmbientCharts
    intro i
    let q := Quotient.mk B.F.unstablePartition x
    let := B.F.unstableTopology q
    let := B.unstableTopology x
    let : SecondCountableTopology (UnstableAsymptoticLeaf f x) :=
      (B.nativeU x).secondCountable
    let : SecondCountableTopology (B.F.ULeaf x) :=
      (B.unstableClassHomeomorph x).secondCountableTopology
    let Z := {z : FoliationCoordinateDisk s' // B.F.unstableLabel i z = q}
    let plaque : Z → FoliationCoordinateDisk t' → B.F.ULeaf x := fun z w ↦
      ⟨((B.F.box i).chart (z.val, w)).val, (B.F.unstable_label i z.val w).trans z.property⟩
    have hopen_aux (z : FoliationCoordinateDisk s') (q' : Quotient B.F.unstablePartition)
        (hz : B.F.unstableLabel i z = q') :
        letI := B.F.unstableTopology q'
        IsOpen (Set.range (fun w : FoliationCoordinateDisk t' ↦
          (⟨((B.F.box i).chart (z, w)).val, (B.F.unstable_label i z w).trans hz⟩ :
            IntrinsicFoliationLeaf B.F.unstablePartition q'))) := by
      subst q'
      let := B.F.unstableTopology (B.F.unstableLabel i z)
      exact (B.F.unstable_plaque i z).isOpen_range
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
      exact congrArg Prod.fst heq
    have hcount : (Set.univ : Set Z).Countable :=
      Set.PairwiseDisjoint.countable_of_isOpen
        (fun _ _ _ _ h ↦ hdis h) (fun z _ ↦ hopen z) (fun z _ ↦ hne z)
    have : Countable Z := Set.countable_univ_iff.mp hcount
    exact @Set.to_countable _ _ (show Countable Z from inferInstance)
  have continuous_intrinsic_B {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X] :
      letI := B.realAmbientCharts
      letI := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
      ∀ g : X → B.F.ULeaf x, Continuous (fun z ↦ (g z).val) → Continuous g := by
    let := B.realAmbientCharts
    let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
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
    have hr : Set.range (fun z : V ↦ (coords z).1) ⊆
        {w | B.F.unstableLabel i w = Quotient.mk B.F.unstablePartition x} := by
      rintro w ⟨z, rfl⟩
      have h := B.F.unstable_label i (coords z).1 (coords z).2
      rw [Prod.mk.eta] at h
      change Quotient.mk _ ((B.F.box i).chart ((B.F.box i).chart.symm (u z))).val = _ at h
      rw [(B.F.box i).chart.apply_symm_apply] at h
      exact h.symm.trans (g z.val).property
    have hconst := (labels_countable_B i).isTotallyDisconnected
      (Set.range (fun z : V ↦ (coords z).1)) hr
      (isPreconnected_range (continuous_fst.comp hcoords))
    let aV : V := ⟨a, haV⟩
    have hz : ∀ z : V, (coords z).1 = (coords aV).1 :=
      fun z ↦ hconst ⟨z, rfl⟩ ⟨aV, rfl⟩
    have hlabel := hr ⟨aV, rfl⟩
    have hplaque (w : FoliationCoordinateDisk s') (q : Quotient B.F.unstablePartition)
        (hw : B.F.unstableLabel i w = q) :
        letI := B.F.unstableTopology q
        Continuous (fun z : FoliationCoordinateDisk t' ↦
          (⟨((B.F.box i).chart (w, z)).val, (B.F.unstable_label i w z).trans hw⟩ :
            IntrinsicFoliationLeaf B.F.unstablePartition q)) := by
      subst q
      let := B.F.unstableTopology (B.F.unstableLabel i w)
      exact (B.F.unstable_plaque i w).continuous
    have hc : Continuous (fun z : V ↦ g z.val) := by
      convert (hplaque (coords aV).1 _ hlabel).comp (continuous_snd.comp hcoords) using 1
      funext z
      apply Subtype.ext
      change (g z.val).val = ((B.F.box i).chart ((coords aV).1, (coords z).2)).val
      rw [← hz z, Prod.mk.eta]
      exact (congrArg Subtype.val ((B.F.box i).chart.apply_symm_apply (u z))).symm
    exact (hV.isOpenEmbedding_subtypeVal.continuousAt_iff).mp (hc.continuousAt (x := aV))
  let := A.realAmbientCharts
  let := B.realAmbientCharts
  let := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
  let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
  let eA : A.F.ULeaf x ≃ UnstableAsymptoticLeaf f x :=
    letI := A.unstableTopology x
    (A.unstableClassHomeomorph x).toEquiv
  let eB : B.F.ULeaf x ≃ UnstableAsymptoticLeaf f x :=
    letI := B.unstableTopology x
    (B.unstableClassHomeomorph x).toEquiv
  let e := eA.trans eB.symm
  have he : ∀ z : A.F.ULeaf x, (e z).val = z.val := by
    intro z
    have h := B.unstable_points x (e z)
    have h' : (eB (e z)).val = (eA z).val := congrArg Subtype.val (eB.apply_symm_apply (eA z))
    exact h.symm.trans (h'.trans (A.unstable_points x z))
  have he' : ∀ z : B.F.ULeaf x, (e.symm z).val = z.val := by
    intro z
    simpa using (he (e.symm z)).symm
  let := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
  let := B.F.unstableCharts (Quotient.mk B.F.unstablePartition x)
  let : LocallyConnectedSpace (A.F.ULeaf x) := ChartedSpace.locallyConnectedSpace (Fin t → ℝ) (A.F.ULeaf x)
  let : LocallyConnectedSpace (B.F.ULeaf x) := ChartedSpace.locallyConnectedSpace (Fin t' → ℝ) (B.F.ULeaf x)
  have hc : Continuous e := continuous_intrinsic_B e (by
    simpa only [he] using A.F.unstable_inclusion (Quotient.mk A.F.unstablePartition x))
  have hc' : Continuous e.symm := continuous_intrinsic_A e.symm (by
    simpa only [he'] using B.F.unstable_inclusion (Quotient.mk B.F.unstablePartition x))
  exact ⟨⟨e, hc, hc'⟩, he⟩

end HolomorphicAnosov.Ghys
