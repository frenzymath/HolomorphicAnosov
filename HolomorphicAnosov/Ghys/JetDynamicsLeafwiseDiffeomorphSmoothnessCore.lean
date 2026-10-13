import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.CurveJetAffineData
import Mathlib.Geometry.Manifold.Diffeomorph

namespace HolomorphicAnosov.Ghys

open Set _root_.HolomorphicAnosov.Topology _root_.Topology
open scoped Topology _root_.Topology Manifold ContDiff

universe u v

/-! This file records the coefficient-atlas Taylor calculation for fixed-leaf jet transport. -/

/-- The first and second Taylor coefficient maps for leafwise postcomposition are smooth on each scalar coordinate overlap. -/
theorem curve_postcompose_coefficient_taylor_contDiffOn
    {s : Set ℂ} (hs : IsOpen s) {h : ℂ → ℂ}
    (hcoord : ContDiffOn ℂ ∞ h s) :
    ContDiffOn ℂ ∞ (fun w : ℂ × ℂ ↦ (h w.1, deriv h w.1 * w.2))
      {w | w.1 ∈ s} ∧
    ContDiffOn ℂ ∞ (fun w : (ℂ × ℂ) × ℂ ↦
      ((h w.1.1, deriv h w.1.1 * w.1.2),
        deriv h w.1.1 * w.2 + iteratedDeriv 2 h w.1.1 * w.1.2 ^ 2 / 2))
      {w | w.1.1 ∈ s} := by
  exact scalar_two_jet_transition_regular hs hcoord

private theorem curve_postcompose_jet_equiv_contMDiff_forward
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
    [IsManifold 𝓘(ℂ) ∞ L] [IsManifold 𝓘(ℂ) ∞ L']
    [T2Space L] [T2Space L'] [SecondCountableTopology L]
    [SecondCountableTopology L']
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L)]
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L')]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L)]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L')]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L)]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L')]
    (hAtlases :
      CurveJetCoefficientAtlases L (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) ∧
      CurveJetCoefficientAtlases L' (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L'))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')))
    (T : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) L L' ∞)
    (E1 : CurveJet1 L ≃ CurveJet1 L')
    (E2 : CurveJet2 L ≃ CurveJet2 L')
    (hE1 : ∀ γ : CurveParamGerm L,
      E1 (curveJet1Class L γ) =
        curveJet1Class L' (curveParamGermPostcompose T γ))
    (hE2 : ∀ γ : CurveParamGerm L,
      E2 (curveJet2Class L γ) =
        curveJet2Class L' (curveParamGermPostcompose T γ)) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ∞ E1 ∧
    ContMDiff 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ E2 := by
  have hcharts (c : LeafChart L) : ∃ d : LeafChart L',
      (∀ x, d.1 (T x) = c.1 x) ∧
      (∀ x, T x ∈ d.1.source ↔ x ∈ c.1.source) ∧
      (∀ γ : CurveParamGerm L,
        (curveParamGermPostcompose T γ).1.map (d.1 : L' → ℂ) =
          γ.1.map (c.1 : L → ℂ)) := by
    let t := T.toHomeomorph.toOpenPartialHomeomorph
    let d : OpenPartialHomeomorph L' ℂ := t.symm.trans c.1
    have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ L' := by
      apply d.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas c.2).comp
          T.symm.contMDiff.contMDiffOn (fun x hx ↦ hx.2)
      · have htarget : d.target = c.1.target := by simp [d, t]
        rw [htarget]
        exact T.contMDiff.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas c.2)
    refine ⟨⟨d, hd⟩, ?_, ?_, ?_⟩
    · intro x
      change c.1 (T.symm (T x)) = c.1 x
      rw [T.symm_apply_apply]
    · intro x
      simp [d, t]
    · intro γ
      change (γ.1.map (T : L → L')).map (d : L' → ℂ) = γ.1.map (c.1 : L → ℂ)
      induction γ.1 using Filter.Germ.inductionOn with
      | h f =>
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [] with z
        change c.1 (T.symm (T (f z))) = c.1 (f z)
        rw [T.symm_apply_apply]
  have hbase (γ : CurveParamGerm L) :
      curveGermBase L' (curveParamGermPostcompose T γ).1 = T (curveGermBase L γ.1) := by
    change curveGermBase L' (γ.1.map (T : L → L')) = T (curveGermBase L γ.1)
    induction γ.1 using Filter.Germ.inductionOn with
    | h f => rfl
  have hcoord (c : LeafChart L) (d : LeafChart L')
      (hd : ∀ x, d.1 (T x) = c.1 x)
      (hs : ∀ x, T x ∈ d.1.source ↔ x ∈ c.1.source)
      (hg : ∀ γ : CurveParamGerm L,
        (curveParamGermPostcompose T γ).1.map (d.1 : L' → ℂ) =
          γ.1.map (c.1 : L → ℂ)) :
      (∀ j, curveJet1Base L j ∈ c.1.source →
        curveJet1Base L' (E1 j) ∈ d.1.source ∧
        curveJet1Coeff L' d (E1 j) = curveJet1Coeff L c j) ∧
      (∀ j, curveJet2Base L j ∈ c.1.source →
        curveJet2Base L' (E2 j) ∈ d.1.source ∧
        curveJet2Coeff L' d (E2 j) = curveJet2Coeff L c j) := by
    constructor
    · intro j
      refine Quotient.inductionOn j ?_
      intro γ hγ
      change curveJet1Base L (curveJet1Class L γ) ∈ c.1.source at hγ
      rw [(leaf_jet_complex_manifold L).2.1 γ |>.1] at hγ
      change curveJet1Base L' (E1 (curveJet1Class L γ)) ∈ d.1.source ∧ _
      rw [hE1 γ]
      have hγ' : curveGermBase L' (curveParamGermPostcompose T γ).1 ∈ d.1.source := by
        rw [hbase]; exact (hs _).mpr hγ
      refine ⟨?_, ?_⟩
      · rw [(leaf_jet_complex_manifold L').2.1 (curveParamGermPostcompose T γ) |>.1]
        exact hγ'
      · change curveJet1Coeff L' d (E1 (curveJet1Class L γ)) =
          curveJet1Coeff L c (curveJet1Class L γ)
        rw [hE1 γ]
        rw [((leaf_jet_complex_manifold L').2.1 _).2.2.2 d hγ' |>.2.1,
          ((leaf_jet_complex_manifold L).2.1 γ).2.2.2 c hγ |>.2.1]
        simp only [curveGermFirst, hg γ, hbase, hd]
    · intro j
      refine Quotient.inductionOn j ?_
      intro γ hγ
      change curveJet2Base L (curveJet2Class L γ) ∈ c.1.source at hγ
      rw [((leaf_jet_complex_manifold L).2.1 γ).2.1] at hγ
      change curveJet2Base L' (E2 (curveJet2Class L γ)) ∈ d.1.source ∧ _
      rw [hE2 γ]
      have hγ' : curveGermBase L' (curveParamGermPostcompose T γ).1 ∈ d.1.source := by
        rw [hbase]; exact (hs _).mpr hγ
      refine ⟨?_, ?_⟩
      · rw [((leaf_jet_complex_manifold L').2.1 (curveParamGermPostcompose T γ)).2.1]
        exact hγ'
      · change curveJet2Coeff L' d (E2 (curveJet2Class L γ)) =
          curveJet2Coeff L c (curveJet2Class L γ)
        rw [hE2 γ]
        rw [((leaf_jet_complex_manifold L').2.1 _).2.2.2 d hγ' |>.2.2,
          ((leaf_jet_complex_manifold L).2.1 γ).2.2.2 c hγ |>.2.2]
        simp only [curveGermFirst, curveGermSecond, hg γ, hbase, hd]
  constructor
  · intro j
    let c : LeafChart L := ⟨chartAt ℂ (curveJet1Base L j), IsManifold.chart_mem_maximalAtlas _⟩
    obtain ⟨d, hd, hs, hg⟩ := hcharts c
    obtain ⟨e1, e2, _, _, he1s, _, _, _, he1, _, he1sm, _, _, _⟩ := hAtlases.1.2.2.1 c
    obtain ⟨f1, f2, _, _, hf1s, _, _, _, hf1, _, _, hf1sm, _, _⟩ := hAtlases.2.2.2.1 d
    have hmap : Set.MapsTo E1 e1.source f1.source := by
      intro x hx
      rw [hf1s]
      exact (hcoord c d hd hs hg).1 x (by simpa only [he1s, Set.mem_preimage] using hx) |>.1
    have heq : Set.EqOn (f1 ∘ E1) e1 e1.source := by
      intro x hx
      exact (hf1 (hmap hx)).trans (((hcoord c d hd hs hg).1 x (by simpa only [he1s, Set.mem_preimage] using hx)).2.trans
        (he1 hx).symm)
    have htarget : Set.MapsTo e1 e1.source f1.target := by
      intro x hx
      rw [← heq hx]
      exact f1.map_source (hmap hx)
    have hsm := hf1sm.comp he1sm htarget
    have hEsm : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ∞ E1 e1.source :=
      hsm.congr (fun x hx ↦ by
        change E1 x = f1.symm (e1 x)
        rw [← heq hx]
        exact (f1.left_inv (hmap hx)).symm)
    exact hEsm.contMDiffAt (e1.open_source.mem_nhds (by
      rw [he1s]; exact mem_chart_source ℂ _))
  · intro j
    let c : LeafChart L := ⟨chartAt ℂ (curveJet2Base L j), IsManifold.chart_mem_maximalAtlas _⟩
    obtain ⟨d, hd, hs, hg⟩ := hcharts c
    obtain ⟨e1, e2, _, _, _, he2s, _, _, _, he2, _, _, he2sm, _⟩ := hAtlases.1.2.2.1 c
    obtain ⟨f1, f2, _, _, _, hf2s, _, _, _, hf2, _, _, _, hf2sm⟩ := hAtlases.2.2.2.1 d
    have hmap : Set.MapsTo E2 e2.source f2.source := by
      intro x hx
      rw [hf2s]
      exact (hcoord c d hd hs hg).2 x (by simpa only [he2s, Set.mem_preimage] using hx) |>.1
    have heq : Set.EqOn (f2 ∘ E2) e2 e2.source := by
      intro x hx
      exact (hf2 (hmap hx)).trans (((hcoord c d hd hs hg).2 x (by simpa only [he2s, Set.mem_preimage] using hx)).2.trans
        (he2 hx).symm)
    have htarget : Set.MapsTo e2 e2.source f2.target := by
      intro x hx
      rw [← heq hx]
      exact f2.map_source (hmap hx)
    have hsm := hf2sm.comp he2sm htarget
    have hEsm : ContMDiffOn 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ E2 e2.source :=
      hsm.congr (fun x hx ↦ by
        change E2 x = f2.symm (e2 x)
        rw [← heq hx]
        exact (f2.left_inv (hmap hx)).symm)
    exact hEsm.contMDiffAt (e2.open_source.mem_nhds (by
      rw [he2s]; exact mem_chart_source ℂ _))

theorem curve_postcompose_jet_equiv_contMDiff
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
    [IsManifold 𝓘(ℂ) ∞ L] [IsManifold 𝓘(ℂ) ∞ L']
    [T2Space L] [T2Space L'] [SecondCountableTopology L]
    [SecondCountableTopology L']
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L)]
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L')]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L)]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L')]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L)]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L')]
    (hAtlases :
      CurveJetCoefficientAtlases L (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) ∧
      CurveJetCoefficientAtlases L' (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L'))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')))
    (T : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) L L' ∞)
    (E1 : CurveJet1 L ≃ CurveJet1 L')
    (E2 : CurveJet2 L ≃ CurveJet2 L')
    (hE1 : ∀ γ : CurveParamGerm L,
      E1 (curveJet1Class L γ) =
        curveJet1Class L' (curveParamGermPostcompose T γ))
    (hE2 : ∀ γ : CurveParamGerm L,
      E2 (curveJet2Class L γ) =
        curveJet2Class L' (curveParamGermPostcompose T γ)) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ℂ))
      (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ E1 ∧
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ℂ))
      (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ E1.symm ∧
    ContMDiff (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
      (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ E2 ∧
    ContMDiff (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
      (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ E2.symm := by
  have hround1 (γ : CurveParamGerm L') :
      curveParamGermPostcompose T (curveParamGermPostcompose T.symm γ) = γ := by
    apply Subtype.ext
    change (γ.1.map (T.symm : L' → L)).map (T : L → L') = γ.1
    induction γ.1 using Filter.Germ.inductionOn with
    | h f =>
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [] with z
      exact T.apply_symm_apply (f z)
  have hround2 (γ : CurveParamGerm L) :
      curveParamGermPostcompose T.symm (curveParamGermPostcompose T γ) = γ := by
    apply Subtype.ext
    change (γ.1.map (T : L → L')).map (T.symm : L' → L) = γ.1
    induction γ.1 using Filter.Germ.inductionOn with
    | h f =>
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [] with z
      exact T.symm_apply_apply (f z)
  have hE1back : ∀ γ : CurveParamGerm L',
      E1.symm (curveJet1Class L' γ) =
        curveJet1Class L (curveParamGermPostcompose T.symm γ) := by
    intro γ
    let δ := curveParamGermPostcompose T.symm γ
    have h := hE1 δ
    rw [hround1 γ] at h
    apply E1.injective
    simpa only [E1.apply_symm_apply] using h.symm
  have hE2back : ∀ γ : CurveParamGerm L',
      E2.symm (curveJet2Class L' γ) =
        curveJet2Class L (curveParamGermPostcompose T.symm γ) := by
    intro γ
    let δ := curveParamGermPostcompose T.symm γ
    have h := hE2 δ
    rw [hround1 γ] at h
    apply E2.injective
    simpa only [E2.apply_symm_apply] using h.symm
  obtain ⟨h1i, h2i⟩ := curve_postcompose_jet_equiv_contMDiff_forward
    (L := L') (L' := L) hAtlases.symm T.symm E1.symm E2.symm hE1back hE2back
  obtain ⟨h1, h2⟩ := curve_postcompose_jet_equiv_contMDiff_forward
    hAtlases T E1 E2 hE1 hE2
  exact ⟨h1, h1i, h2, h2i⟩


end HolomorphicAnosov.Ghys
