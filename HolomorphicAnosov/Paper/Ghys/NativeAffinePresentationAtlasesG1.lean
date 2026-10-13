import HolomorphicAnosov.Paper.Ghys.NativeAffinePresentationIdentificationG1
import HolomorphicAnosov.Ghys.AffineMaximalAtlasTransportG1

/-! This file transports maximal affine leaf atlases to a supplied intrinsic presentation,
preserving their flat-chart characterization and completeness. (Ghys, Prop. 3.1, pp. 590–593) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The supplied intrinsic leaf presentation admits affine structures whose maximal charts are the
pullbacks of the native flat charts, with completeness preserved under transport. (Ghys, Prop.
3.1, p. 590; Lemma 3.2, p. 591) -/
theorem native_affine_presentation_atlases_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (hcomplete : ∀ i, (G.affineAt f a L U i).Complete (L i)) :
    letI := P.realCharts
    ∃ A : AffineUnstableLeafStructures P.foliations P.complexLeaves,
      ∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞)
          (B : ComplexAffineAtlas (IntrinsicFoliationLeaf P.foliations.unstablePartition q)),
          (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
          B.charts = {e | ∃ c ∈ (G.affineAt f a L U i).out.charts,
            e = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} ∧
          A.structureAt q = Quotient.mk _ B ∧
          ComplexAffineStructure.Complete _ (A.structureAt q) ∧
          ∀ e : OpenPartialHomeomorph
              (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
            e ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ↔
              IsHolomorphicScalarChart (L i) (T.toHomeomorph.toOpenPartialHomeomorph.trans e) ∧
                ∀ gamma : CurveParamGerm (L i),
                  curveGermBase (L i) gamma.1 ∈
                    (T.toHomeomorph.toOpenPartialHomeomorph.trans e).source →
                  (G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
                    nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) gamma) ↔
                    germSecond (gamma.1.map
                      (T.toHomeomorph.toOpenPartialHomeomorph.trans e : L i → ℂ)) = 0) := by
  classical
  let := P.realCharts
  have hex (q : Quotient P.foliations.unstablePartition) :
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
        ∀ z, (T z).val = (U.leaf i).inclusion z := by
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i, E, hE⟩ := native_affine_presentation_identification_g1 f a P L U G q
    let T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
        (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞ :=
      { E.toEquiv with
        contMDiff_toFun := E.contMDiff.comp (curveProductToScalar_contMDiff_id (L i))
        contMDiff_invFun := (curveScalarToProduct_contMDiff_id (L i)).comp E.symm.contMDiff }
    exact ⟨i, T, hE⟩
  choose idx T hT using hex
  have hB (q : Quotient P.foliations.unstablePartition) :
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ∃ B : ComplexAffineAtlas (IntrinsicFoliationLeaf P.foliations.unstablePartition q),
        B.charts = {e | ∃ c ∈ (G.affineAt f a L U (idx q)).out.charts,
          e = (T q).toHomeomorph.symm.toOpenPartialHomeomorph.trans c} := by
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    exact exists_complexAffineAtlas_transport (T q) (G.affineAt f a L U (idx q)).out
  choose B hB using hB
  let A : AffineUnstableLeafStructures P.foliations P.complexLeaves :=
    ⟨fun q ↦ Quotient.mk _ (B q)⟩
  refine ⟨A, ?_⟩
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  refine ⟨idx q, T q, B q, hT q, hB q, rfl, ?_, ?_⟩
  · exact affine_complete_transported_atlas_g1 (T q) _ (B q) (hB q) (hcomplete (idx q))
  · intro e
    change e ∈ ComplexAffineStructure.maximalAtlas _ (Quotient.mk _ (B q)) ↔ _
    rw [affine_maximalAtlas_transport_iff_g1 (T q) _ (B q) (hB q) e]
    have hout : Quotient.mk (complexAffineAtlasSetoid (L (idx q)))
        (G.affineAt f a L U (idx q)).out = G.affineAt f a L U (idx q) :=
      Quotient.out_eq _
    rw [hout]
    exact G.flat_chart_iff (idx q) _

end HolomorphicAnosov.Ghys
