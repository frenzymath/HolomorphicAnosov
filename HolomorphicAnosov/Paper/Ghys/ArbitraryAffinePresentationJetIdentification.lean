import HolomorphicAnosov.Paper.Ghys.NativeInvariantAffinePresentationG1
import HolomorphicAnosov.Paper.Ghys.NativeInvariantJetAffineFamilyExistenceG1
import HolomorphicAnosov.Ghys.AffineCompleteness

/-! An invariant affine family on an intrinsic foliation presentation is identified with
the transported invariant jet family and admits ambient continuous local affine coordinates.
(Ghys, Prop. 3.1 and Lemmas 3.2–3.3) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- An affine family satisfying affine invariance and continuity along stable holonomy has
the same maximal atlas as the point-preserving transport of a complete invariant jet family.
(Ghys, Prop. 3.1) -/
theorem arbitrary_affine_presentation_jet_identification
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
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      ∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
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
  intro A hAct hCont
  by_cases hM : IsEmpty M
  · intro q
    obtain ⟨x, _⟩ := Quotient.exists_rep q
    exact (hM.false x).elim
  let : Nonempty M := not_isEmpty_iff.mp hM
  obtain ⟨B, hB⟩ := native_affine_presentation_atlases_g1 f a P L U G hcomplete
  have htransfer : ∀ q : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
        (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
        ∀ e : OpenPartialHomeomorph
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
          e ∈ ComplexAffineStructure.maximalAtlas _ (B.structureAt q) ↔
            T.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
              ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i) := by
    intro q
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i, T, b, hT, hb, hBb, hcomp, hflat⟩ := hB q
    exact ⟨i, T, hT, fun e ↦ (hflat e).trans (G.flat_chart_iff i _).symm⟩
  have hBAct := native_affine_presentation_action_g1 f a P L U G B htransfer
  have hBPrefix := native_affine_holonomy_coordinates_g1 f a P L U G B htransfer
  have hBCont := affine_holonomy_ratio_continuous_of_prefix_coordinates_g1
    P.foliations P.complexLeaves B hBPrefix
  obtain ⟨C, _, _, hUnique, _⟩ := native_invariant_affine_family_on_presentation_g1 f a P L U G hcomplete
  have hAB : A = B := (hUnique A hAct hCont).trans (hUnique B hBAct hBCont).symm
  subst A
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  obtain ⟨i, T, b, hT, hb, hBb, hcomp, hflat⟩ := hB q
  exact ⟨i, T, hT, hflat⟩

/-- An affine family satisfying affine invariance and continuity along stable holonomy
admits ambient continuous local affine coordinates. -/
theorem arbitrary_affine_presentation_local_continuous_coordinates
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      ∀ x : M, ∃ (O : Set M) (K : M → ℂ), IsOpen O ∧ x ∈ O ∧ ContinuousOn K O ∧
        ∀ q : Quotient P.foliations.unstablePartition,
          letI := P.foliations.unstableTopology q
          letI := P.complexLeaves.charts q
          ∀ y : IntrinsicFoliationLeaf P.foliations.unstablePartition q, y.val ∈ O →
            ∃ c : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
              c ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ∧ y ∈ c.source ∧
                (c : _ → ℂ) =ᶠ[𝓝 y] K ∘ Subtype.val := by
  classical
  let := P.realCharts
  intro A hAct hCont
  obtain ⟨ι,L,top,h⟩ := native_invariant_jet_affine_family_exists_g1 f a hRank
  let := top
  obtain ⟨realChart,h⟩ := h
  let := realChart
  obtain ⟨realSmooth,h⟩ := h
  let := realSmooth
  obtain ⟨U,complexChart,h⟩ := h
  let := complexChart
  obtain ⟨complexSmooth,⟨G⟩⟩ := h
  let := complexSmooth
  apply native_local_affine_coordinate_on_presentation_g1 f a P L U G A
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  obtain ⟨i,T,hT,hflat⟩ := arbitrary_affine_presentation_jet_identification f a P L U G
    (fun i ↦ (affine_completeness f a L U G i).1) A hAct hCont q
  exact ⟨i,T,hT,fun e ↦ (hflat e).trans (G.flat_chart_iff i _).symm⟩

end HolomorphicAnosov.Ghys
