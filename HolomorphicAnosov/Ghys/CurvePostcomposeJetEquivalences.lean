import HolomorphicAnosov.Ghys.CurveParamGermPostcompose

/-! Biholomorphic postcomposition induces equivalences of first and second curve jet quotients.
(Ghys, Lemma 3.2, p.591; Michor, §1.6 pp.2–3) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

noncomputable section
namespace HolomorphicAnosov.Ghys

universe u v

/-- A biholomorphism induces equivalences of the first and second contact quotients, sending each
class to the class of its postcomposed germ. -/
theorem curve_postcompose_jet_equivalences
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L']
    (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) L L' ∞) :
    ∃ (E1 : CurveJet1 L ≃ CurveJet1 L') (E2 : CurveJet2 L ≃ CurveJet2 L'),
      (∀ γ : CurveParamGerm L,
        E1 (curveJet1Class L γ) = curveJet1Class L' (curveParamGermPostcompose T γ)) ∧
      (∀ γ : CurveParamGerm L,
        E2 (curveJet2Class L γ) = curveJet2Class L' (curveParamGermPostcompose T γ)) := by
  have curveGermBase_postcompose
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L L' ∞) (γ : CurveParamGerm L) :
      curveGermBase L' (γ.1.map (T : L → L')) =
        T (curveGermBase L γ.1) := by
    induction γ.1 using Filter.Germ.inductionOn with
    | h f => rfl
  have curve_postcompose_contact1
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L L' ∞)
      {γ δ : CurveParamGerm L} (h : CurveContact1 L γ δ) :
      CurveContact1 L' (curveParamGermPostcompose T γ)
        (curveParamGermPostcompose T δ) := by
    rcases h with ⟨hbase, c, hc, hfirst⟩
    let t : OpenPartialHomeomorph L L' := T.toHomeomorph.toOpenPartialHomeomorph
    let c' : OpenPartialHomeomorph L' ℂ := t.symm.trans c
    have hc' : c' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L' := by
      apply c'.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas c.2).comp
          (T.symm.contMDiff.contMDiffOn) (fun x hx => hx.2)
      · have htarg : c'.target = c.1.target := by simp [c', t]
        rw [htarg]
        exact T.contMDiff.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)
    let cLeaf : LeafChart L' := ⟨c', hc'⟩
    refine ⟨?_, cLeaf, ?_, ?_⟩
    · change curveGermBase L' (γ.1.map (T : L → L')) =
        curveGermBase L' (δ.1.map (T : L → L'))
      rw [curveGermBase_postcompose, curveGermBase_postcompose, hbase]
    · change curveGermBase L' (γ.1.map (T : L → L')) ∈ c'.source
      rw [curveGermBase_postcompose]
      simpa [c', t] using hc
    · change germFirst ((γ.1.map (T : L → L')).map (c' : L' → ℂ)) =
        germFirst ((δ.1.map (T : L → L')).map (c' : L' → ℂ))
      have hmap (η : CurveGerm L) :
          (η.map (T : L → L')).map (c' : L' → ℂ) = η.map (c.1 : L → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hfirst
  have curve_postcompose_contact2
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L L' ∞)
      {γ δ : CurveParamGerm L} (h : CurveContact2 L γ δ) :
      CurveContact2 L' (curveParamGermPostcompose T γ)
        (curveParamGermPostcompose T δ) := by
    rcases h with ⟨hbase, c, hc, hfirst, hsecond⟩
    let t : OpenPartialHomeomorph L L' := T.toHomeomorph.toOpenPartialHomeomorph
    let c' : OpenPartialHomeomorph L' ℂ := t.symm.trans c
    have hc' : c' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L' := by
      apply c'.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas c.2).comp
          (T.symm.contMDiff.contMDiffOn) (fun x hx => hx.2)
      · have htarg : c'.target = c.1.target := by simp [c', t]
        rw [htarg]
        exact T.contMDiff.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)
    let cLeaf : LeafChart L' := ⟨c', hc'⟩
    refine ⟨?_, cLeaf, ?_, ?_, ?_⟩
    · change curveGermBase L' (γ.1.map (T : L → L')) =
        curveGermBase L' (δ.1.map (T : L → L'))
      rw [curveGermBase_postcompose, curveGermBase_postcompose, hbase]
    · change curveGermBase L' (γ.1.map (T : L → L')) ∈ c'.source
      rw [curveGermBase_postcompose]
      simpa [c', t] using hc
    · change germFirst ((γ.1.map (T : L → L')).map (c' : L' → ℂ)) =
        germFirst ((δ.1.map (T : L → L')).map (c' : L' → ℂ))
      have hmap (η : CurveGerm L) :
          (η.map (T : L → L')).map (c' : L' → ℂ) = η.map (c.1 : L → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hfirst
    · change germSecond ((⟨γ.1.map (T : L → L'),
        curve_postcompose_admissible T γ⟩ : CurveParamGerm L').1.map (c' : L' → ℂ)) =
        germSecond ((⟨δ.1.map (T : L → L'),
        curve_postcompose_admissible T δ⟩ : CurveParamGerm L').1.map (c' : L' → ℂ))
      have hmap (η : CurveGerm L) :
          (η.map (T : L → L')).map (c' : L' → ℂ) = η.map (c.1 : L → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hsecond
  have curveGermBase_postcompose_reverse
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L' L ∞) (γ : CurveParamGerm L') :
      curveGermBase L (γ.1.map (T : L' → L)) =
        T (curveGermBase L' γ.1) := by
    induction γ.1 using Filter.Germ.inductionOn with
    | h f => rfl
  have curve_postcompose_contact1_reverse
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L' L ∞)
      {γ δ : CurveParamGerm L'} (h : CurveContact1 L' γ δ) :
      CurveContact1 L (curveParamGermPostcompose T γ)
        (curveParamGermPostcompose T δ) := by
    rcases h with ⟨hbase, c, hc, hfirst⟩
    let t : OpenPartialHomeomorph L' L := T.toHomeomorph.toOpenPartialHomeomorph
    let c' : OpenPartialHomeomorph L ℂ := t.symm.trans c
    have hc' : c' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L := by
      apply c'.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas c.2).comp
          (T.symm.contMDiff.contMDiffOn) (fun x hx => hx.2)
      · have htarg : c'.target = c.1.target := by simp [c', t]
        rw [htarg]
        exact T.contMDiff.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)
    let cLeaf : LeafChart L := ⟨c', hc'⟩
    refine ⟨?_, cLeaf, ?_, ?_⟩
    · change curveGermBase L (γ.1.map (T : L' → L)) =
        curveGermBase L (δ.1.map (T : L' → L))
      rw [curveGermBase_postcompose_reverse, curveGermBase_postcompose_reverse, hbase]
    · change curveGermBase L (γ.1.map (T : L' → L)) ∈ c'.source
      rw [curveGermBase_postcompose_reverse]
      simpa [c', t] using hc
    · change germFirst ((γ.1.map (T : L' → L)).map (c' : L → ℂ)) =
        germFirst ((δ.1.map (T : L' → L)).map (c' : L → ℂ))
      have hmap (η : CurveGerm L') :
          (η.map (T : L' → L)).map (c' : L → ℂ) = η.map (c.1 : L' → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hfirst
  have curve_postcompose_contact2_reverse
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L' L ∞)
      {γ δ : CurveParamGerm L'} (h : CurveContact2 L' γ δ) :
      CurveContact2 L (curveParamGermPostcompose T γ)
        (curveParamGermPostcompose T δ) := by
    rcases h with ⟨hbase, c, hc, hfirst, hsecond⟩
    let t : OpenPartialHomeomorph L' L := T.toHomeomorph.toOpenPartialHomeomorph
    let c' : OpenPartialHomeomorph L ℂ := t.symm.trans c
    have hc' : c' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L := by
      apply c'.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas c.2).comp
          (T.symm.contMDiff.contMDiffOn) (fun x hx => hx.2)
      · have htarg : c'.target = c.1.target := by simp [c', t]
        rw [htarg]
        exact T.contMDiff.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)
    let cLeaf : LeafChart L := ⟨c', hc'⟩
    refine ⟨?_, cLeaf, ?_, ?_, ?_⟩
    · change curveGermBase L (γ.1.map (T : L' → L)) =
        curveGermBase L (δ.1.map (T : L' → L))
      rw [curveGermBase_postcompose_reverse, curveGermBase_postcompose_reverse, hbase]
    · change curveGermBase L (γ.1.map (T : L' → L)) ∈ c'.source
      rw [curveGermBase_postcompose_reverse]
      simpa [c', t] using hc
    · change germFirst ((γ.1.map (T : L' → L)).map (c' : L → ℂ)) =
        germFirst ((δ.1.map (T : L' → L)).map (c' : L → ℂ))
      have hmap (η : CurveGerm L') :
          (η.map (T : L' → L)).map (c' : L → ℂ) = η.map (c.1 : L' → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hfirst
    · change germSecond ((⟨γ.1.map (T : L' → L),
        curve_postcompose_admissible T γ⟩ : CurveParamGerm L).1.map (c' : L → ℂ)) =
        germSecond ((⟨δ.1.map (T : L' → L),
        curve_postcompose_admissible T δ⟩ : CurveParamGerm L).1.map (c' : L → ℂ))
      have hmap (η : CurveGerm L') :
          (η.map (T : L' → L)).map (c' : L → ℂ) = η.map (c.1 : L' → ℂ) := by
        induction η using Filter.Germ.inductionOn with
        | h f =>
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [] with z
          change c.1 (T.symm (T (f z))) = c.1 (f z)
          rw [T.symm_apply_apply]
      rw [hmap, hmap]
      exact hsecond
  have curveParamGermPostcompose_roundtrip
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L L' ∞)
      (γ : CurveParamGerm L) :
      curveParamGermPostcompose T.symm (curveParamGermPostcompose T γ) = γ := by
    apply Subtype.ext
    change (γ.1.map (T : L → L')).map (T.symm : L' → L) = γ.1
    induction γ.1 using Filter.Germ.inductionOn with
    | h f =>
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [] with z
        exact T.symm_apply_apply (f z)
  have curveParamGermPostcompose_roundtrip_reverse
      (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) L' L ∞)
      (γ : CurveParamGerm L') :
      curveParamGermPostcompose T.symm (curveParamGermPostcompose T γ) = γ := by
    apply Subtype.ext
    change (γ.1.map (T : L' → L)).map (T.symm : L → L') = γ.1
    induction γ.1 using Filter.Germ.inductionOn with
    | h f =>
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [] with z
        exact T.symm_apply_apply (f z)
  let F1 : CurveJet1 L → CurveJet1 L' :=
    Quotient.map (curveParamGermPostcompose T)
      (fun _ _ h => curve_postcompose_contact1 T h)
  let G1 : CurveJet1 L' → CurveJet1 L :=
    Quotient.map (curveParamGermPostcompose T.symm)
      (fun _ _ h => curve_postcompose_contact1_reverse T.symm h)
  let E1 : CurveJet1 L ≃ CurveJet1 L' := {
    toFun := F1
    invFun := G1
    left_inv := by
      intro j
      refine Quotient.inductionOn j ?_
      intro γ
      change Quotient.mk (curveContactSetoid1 L)
          (curveParamGermPostcompose T.symm (curveParamGermPostcompose T γ)) =
        Quotient.mk (curveContactSetoid1 L) γ
      rw [curveParamGermPostcompose_roundtrip]
    right_inv := by
      intro j
      refine Quotient.inductionOn j ?_
      intro γ
      change Quotient.mk (curveContactSetoid1 L')
          (curveParamGermPostcompose T (curveParamGermPostcompose T.symm γ)) =
        Quotient.mk (curveContactSetoid1 L') γ
      exact congrArg (Quotient.mk (curveContactSetoid1 L'))
        (curveParamGermPostcompose_roundtrip_reverse T.symm γ) }
  let F2 : CurveJet2 L → CurveJet2 L' :=
    Quotient.map (curveParamGermPostcompose T)
      (fun _ _ h => curve_postcompose_contact2 T h)
  let G2 : CurveJet2 L' → CurveJet2 L :=
    Quotient.map (curveParamGermPostcompose T.symm)
      (fun _ _ h => curve_postcompose_contact2_reverse T.symm h)
  let E2 : CurveJet2 L ≃ CurveJet2 L' := {
    toFun := F2
    invFun := G2
    left_inv := by
      intro j
      refine Quotient.inductionOn j ?_
      intro γ
      change Quotient.mk (curveContactSetoid2 L)
          (curveParamGermPostcompose T.symm (curveParamGermPostcompose T γ)) =
        Quotient.mk (curveContactSetoid2 L) γ
      rw [curveParamGermPostcompose_roundtrip]
    right_inv := by
      intro j
      refine Quotient.inductionOn j ?_
      intro γ
      change Quotient.mk (curveContactSetoid2 L')
          (curveParamGermPostcompose T (curveParamGermPostcompose T.symm γ)) =
        Quotient.mk (curveContactSetoid2 L') γ
      exact congrArg (Quotient.mk (curveContactSetoid2 L'))
        (curveParamGermPostcompose_roundtrip_reverse T.symm γ) }
  exact ⟨E1, E2, fun _ => rfl, fun _ => rfl⟩


end HolomorphicAnosov.Ghys
