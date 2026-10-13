import HolomorphicAnosov.Ghys.CurveJetHomogeneousLocalCoordinates
import HolomorphicAnosov.Ghys.CurveJetAffineGluing
import HolomorphicAnosov.Ghys.AffineAtlasTransport
import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences

/-! This file identifies affine structures on the base with homogeneous holomorphic sections of the curve two-jet bundle. (Ghys, Lemma 3.2) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

noncomputable section

namespace HolomorphicAnosov.Ghys

universe u v

variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

attribute [local instance] curveScalarToProductChartedSpace



variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]

variable {L}
variable {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L']


variable (L)

/-- Affine structures on a Riemann surface are naturally equivalent to homogeneous holomorphic sections of its curve two-jet bundle, with the prescribed coefficient atlases and parametrization relation. (Ghys, Lemma 3.2) -/
theorem jet_affine_equivalence [T2Space L] [SecondCountableTopology L] :
    ∃ (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
      (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)),
      CurveJetCoefficientAtlases L A1 A2 ∧
      ∃ E : CurveJetAffineCorrespondence L A1 A2,
        ∀ (L' : Type v) [TopologicalSpace L'] [ChartedSpace ℂ L']
          [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L'] [T2Space L']
          [SecondCountableTopology L']
          (A1' : ChartedSpace (ℂ × ℂ) (CurveJet1 L'))
          (A2' : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')),
          CurveJetCoefficientAtlases L' A1' A2' →
          ∀ (E' : CurveJetAffineCorrespondence L' A1' A2')
            (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
              (modelWithCornersSelf ℂ ℂ) L L' ∞) (A : ComplexAffineAtlas L),
            ∃ B : ComplexAffineAtlas L',
              B.charts = {d | ∃ c ∈ A.charts,
                d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} ∧
              ∀ γ δ : CurveParamGerm L,
                ((E.equiv (Quotient.mk (complexAffineAtlasSetoid L) A)).1
                    (curveJet1Class L γ) = curveJet2Class L δ ↔
                  (E'.equiv (Quotient.mk (complexAffineAtlasSetoid L') B)).1
                    (curveJet1Class L' (curveParamGermPostcompose T γ)) =
                      curveJet2Class L' (curveParamGermPostcompose T δ)) := by
  obtain ⟨A1, A2, h⟩ := (leaf_jet_complex_manifold L).2.2.2.2
  rcases h with ⟨_, _, _, _, hM1, hM2, _, _, _, _, _, hcharts, ha1, ha2⟩
  have hsection_truncation
      (σ : HomogeneousCurveJetSection L A1 A2) (j : CurveJet1 L) :
      curveJetTruncation L (σ.1 j) = j := σ.2.1 j
  refine ⟨A1, A2, ⟨hM1, hM2, hcharts, ha1, ha2⟩, ?_⟩


  suffices hdiagonal :
      ∃ E : CurveJetAffineCorrespondence L A1 A2,
        ∀ (L' : Type v) [TopologicalSpace L'] [ChartedSpace ℂ L']
          [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L'] [T2Space L']
          [SecondCountableTopology L']
          (A1' : ChartedSpace (ℂ × ℂ) (CurveJet1 L'))
          (A2' : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')),
          CurveJetCoefficientAtlases L' A1' A2' →
          ∀ (E' : CurveJetAffineCorrespondence L' A1' A2')
            (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
              (modelWithCornersSelf ℂ ℂ) L L' ∞) (A : ComplexAffineAtlas L),
            ∃ B : ComplexAffineAtlas L',
              B.charts = {d | ∃ c ∈ A.charts,
                d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} ∧
              ∀ δ : CurveParamGerm L,
                ((E.equiv (Quotient.mk (complexAffineAtlasSetoid L) A)).1
                    (curveJet1Class L δ) = curveJet2Class L δ ↔
                  (E'.equiv (Quotient.mk (complexAffineAtlasSetoid L') B)).1
                    (curveJet1Class L' (curveParamGermPostcompose T δ)) =
                      curveJet2Class L' (curveParamGermPostcompose T δ)) by
    obtain ⟨E, hE⟩ := hdiagonal
    refine ⟨E, ?_⟩
    intro L' _ _ _ _ _ A1' A2' hA' E' T A
    obtain ⟨B, hB, hdiag⟩ := hE L' A1' A2' hA' E' T A
    refine ⟨B, hB, ?_⟩
    intro γ δ
    obtain ⟨J1, J2, hJ1, hJ2⟩ := curve_postcompose_jet_equivalences T
    let σ := E.equiv (Quotient.mk (complexAffineAtlasSetoid L) A)
    let σ' := E'.equiv (Quotient.mk (complexAffineAtlasSetoid L') B)
    change (σ.1 (curveJet1Class L γ) = curveJet2Class L δ ↔
      σ'.1 (curveJet1Class L' (curveParamGermPostcompose T γ)) =
        curveJet2Class L' (curveParamGermPostcompose T δ))
    have htr (j : CurveJet1 L) : curveJetTruncation L (σ.1 j) = j :=
      hsection_truncation σ j
    have htr' (j : CurveJet1 L') : curveJetTruncation L' (σ'.1 j) = j := σ'.2.1 j
    constructor
    · intro hgraph
      have hfirst : curveJet1Class L γ = curveJet1Class L δ := by
        exact (htr _).symm.trans (congrArg (curveJetTruncation L) hgraph)
      have hfirst' : curveJet1Class L' (curveParamGermPostcompose T γ) =
          curveJet1Class L' (curveParamGermPostcompose T δ) := by
        rw [← hJ1 γ, ← hJ1 δ, hfirst]
      rw [hfirst']
      apply (hdiag δ).mp
      exact hfirst ▸ hgraph
    · intro hgraph
      have hfirst' : curveJet1Class L' (curveParamGermPostcompose T γ) =
          curveJet1Class L' (curveParamGermPostcompose T δ) := by
        exact (htr' _).symm.trans (congrArg (curveJetTruncation L') hgraph)
      have hfirst : curveJet1Class L γ = curveJet1Class L δ := by
        apply J1.injective
        simpa only [hJ1] using hfirst'
      rw [hfirst]
      apply (hdiag δ).mpr
      exact hfirst' ▸ hgraph


  suffices hconstruction :
      Nonempty (CurveJetAffineCorrespondence L A1 A2) ∧
        ∀ (L' : Type v) [TopologicalSpace L'] [ChartedSpace ℂ L']
          [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L'] [T2Space L']
          [SecondCountableTopology L']
          (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
            (modelWithCornersSelf ℂ ℂ) L L' ∞) (A : ComplexAffineAtlas L),
          ∃ B : ComplexAffineAtlas L',
            B.charts = {d | ∃ c ∈ A.charts,
              d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} by
    obtain ⟨⟨E⟩, htransport⟩ := hconstruction
    refine ⟨E, ?_⟩
    intro L' _ _ _ _ _ A1' A2' hA' E' T A
    obtain ⟨B, hB⟩ := htransport L' T A
    refine ⟨B, hB, ?_⟩
    intro δ
    obtain ⟨c, hc, hxc⟩ := A.cover (curveGermBase L δ.1)
    let d : OpenPartialHomeomorph L' ℂ :=
      T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c
    have hd : d ∈ B.charts := by
      rw [hB]
      exact ⟨c, hc, rfl⟩
    have hcmax : c ∈ ComplexAffineStructure.maximalAtlas L
        (Quotient.mk (complexAffineAtlasSetoid L) A) := by
      rw [ComplexAffineStructure.maximalAtlas_eq_of_representative]
      exact ⟨A.holomorphic c hc, fun e he ↦ A.compatible e he c hc⟩
    have hdmax : d ∈ ComplexAffineStructure.maximalAtlas L'
        (Quotient.mk (complexAffineAtlasSetoid L') B) := by
      rw [ComplexAffineStructure.maximalAtlas_eq_of_representative]
      exact ⟨B.holomorphic d hd, fun e he ↦ B.compatible e he d hd⟩
    have hbase : curveGermBase L' (curveParamGermPostcompose T δ).1 =
        T (curveGermBase L δ.1) := by
      change curveGermBase L' (δ.1.map (T : L → L')) = _
      induction δ.1 using Filter.Germ.inductionOn with
      | h f => rfl
    have hxd : curveGermBase L' (curveParamGermPostcompose T δ).1 ∈ d.source := by
      rw [hbase]
      simpa [d] using hxc
    have hgerm : (curveParamGermPostcompose T δ).1.map (d : L' → ℂ) =
        δ.1.map (c : L → ℂ) := by
      change (δ.1.map (T : L → L')).map (d : L' → ℂ) = _
      rw [Filter.Germ.map_map]
      congr 1
      funext x
      change c (T.symm (T x)) = c x
      rw [T.symm_apply_apply]
    rw [E.affine_parametrization _ c hcmax δ hxc,
      E'.affine_parametrization _ d hdmax (curveParamGermPostcompose T δ) hxd,
      hgerm]
  constructor
  · apply curve_jet_affine_correspondence_of_local_coordinates L A1 A2
      ⟨hM1, hM2, hcharts, ha1, ha2⟩
    intro σ
    exact (homogeneous_curve_jet_section_local_coordinates L A1 A2
      ⟨hM1, hM2, hcharts, ha1, ha2⟩ σ).2
  · intro L' _ _ _ _ _ T A
    let T' : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞ :=
      { T.toEquiv with
        contMDiff_toFun := curveScalarToProduct_contMDiff T.contMDiff
        contMDiff_invFun := curveScalarToProduct_contMDiff T.symm.contMDiff }
    exact exists_complexAffineAtlas_transport T' A

end HolomorphicAnosov.Ghys

