import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Ghys.JetAffineEquivalence

/-! The original invariant section and its affine-structure correspondence on the intrinsic leaves. (Ghys, Lemmas 3.2–3.3) -/

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff

namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The jet/affine correspondence on the native coefficient atlases. (Ghys, Lemmas 3.2–3.3) -/
theorem native_leaf_jet_affine_correspondence_g1
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)] (i : ι) :
    Nonempty (CurveJetAffineCorrespondence (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i)) := by
  have h := (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec
  rcases h with ⟨_, _, _, _, hM1, hM2, _, _, _, _, _, hcharts, ha1, ha2⟩
  have hA : CurveJetCoefficientAtlases (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) :=
    ⟨hM1, hM2, hcharts, ha1, ha2⟩
  apply curve_jet_affine_correspondence_of_local_coordinates (L i) _ _ hA
  intro t
  exact (homogeneous_curve_jet_section_local_coordinates (L i) _ _ hA t).2

/-- A family of affine structures on the native intrinsic leaves determines a section on the dependent jet carrier. (Ghys, Lemmas 3.2–3.3) -/
theorem native_affine_family_has_section_g1
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
    (A : ∀ i, ComplexAffineStructure (L i)) :
    ∃ σ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L,
      (∀ j, nativeLeafwiseJetTruncation L (σ j) = j) ∧
      (∀ (omega : ℂˣ) j, σ (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet2Reparametrize L (.scale omega) (σ j)) ∧
      (∀ i, ∃ τ : HomogeneousCurveJetSection (L i)
          (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i),
        ∀ j, σ (nativeLeafwiseJet1Inclusion L i j) =
          nativeLeafwiseJet2Inclusion L i (τ.1 j)) ∧
      ∀ i (e : OpenPartialHomeomorph (L i) ℂ),
        e ∈ ComplexAffineStructure.maximalAtlas (L i) (A i) ↔
          IsHolomorphicScalarChart (L i) e ∧
          ∀ γ : CurveParamGerm (L i), curveGermBase (L i) γ.1 ∈ e.source →
            (σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
                nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) γ) ↔
              germSecond (γ.1.map (e : L i → ℂ)) = 0) := by
  classical
  let E := fun i ↦ Classical.choice (native_leaf_jet_affine_correspondence_g1 L i)
  let σ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L :=
    fun j ↦ ⟨j.1, ((E j.1).equiv (A j.1)).1 j.2⟩
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    change (Sigma.mk i (curveJetTruncation (L i) (((E i).equiv (A i)).1 j)) :
      NativeLeafwiseJet1 L) = Sigma.mk i j
    rw [((E i).equiv (A i)).2.1 j]
  · intro omega j
    change (Sigma.mk j.1 (((E j.1).equiv (A j.1)).1 (curveJet1Scale (L j.1) omega j.2)) :
      NativeLeafwiseJet2 L) =
      Sigma.mk j.1 (curveJet2Reparametrize (L j.1) (.scale omega)
        (((E j.1).equiv (A j.1)).1 j.2))
    rw [((E j.1).equiv (A j.1)).2.2.2 omega j.2]
  · intro i
    exact ⟨(E i).equiv (A i), fun _ ↦ rfl⟩
  · intro i e
    rw [(E i).flat_chart_iff]
    simp only [σ, nativeLeafwiseJet1Inclusion, nativeLeafwiseJet2Inclusion,
      Sigma.mk.inj_iff, heq_eq_eq, true_and]

/-- Affine pullback of maximal charts preserves the section graph. (Ghys, Lemmas 3.2–3.3) -/
theorem native_affine_family_section_graph_preserved_g1
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (A : ∀ i, ComplexAffineStructure (L i))
    (σ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (htrunc : ∀ j, nativeLeafwiseJetTruncation L (σ j) = j)
    (hflat : ∀ i (e : OpenPartialHomeomorph (L i) ℂ),
      e ∈ ComplexAffineStructure.maximalAtlas (L i) (A i) →
      ∀ γ : CurveParamGerm (L i), curveGermBase (L i) γ.1 ∈ e.source →
        (σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
            nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) γ) ↔
          germSecond (γ.1.map (e : L i → ℂ)) = 0))
    (perm : ι → ι) (F : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞)
    (hpull : ∀ i (e : OpenPartialHomeomorph (L (perm i)) ℂ),
      e ∈ ComplexAffineStructure.maximalAtlas _ (A (perm i)) →
        (F i).toHomeomorph.toOpenPartialHomeomorph.trans e ∈
          ComplexAffineStructure.maximalAtlas _ (A i))
    (i : ι) (γ η : CurveParamGerm (L i))
    (hgraph : σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
      nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η)) :
    σ (nativeLeafwiseJet1Inclusion L (perm i)
      (curveJet1Class (L (perm i)) (curveParamGermPostcompose (F i) γ))) =
      nativeLeafwiseJet2Inclusion L (perm i)
        (curveJet2Class (L (perm i)) (curveParamGermPostcompose (F i) η)) := by
  have hfirst : curveJet1Class (L i) γ = curveJet1Class (L i) η := by
    have h := (htrunc (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ))).symm.trans
      (congrArg (nativeLeafwiseJetTruncation L) hgraph)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨J1, _, hJ1, _⟩ := curve_postcompose_jet_equivalences (F i)
  have hfirst' : curveJet1Class (L (perm i)) (curveParamGermPostcompose (F i) γ) =
      curveJet1Class (L (perm i)) (curveParamGermPostcompose (F i) η) := by
    rw [← hJ1, ← hJ1, hfirst]
  rw [hfirst']
  have hdiag : σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) η)) =
      nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η) := hfirst ▸ hgraph
  let η' := curveParamGermPostcompose (F i) η
  obtain ⟨e, he, hpoint⟩ := (A (perm i)).out.cover (curveGermBase (L (perm i)) η'.1)
  have hemax : e ∈ ComplexAffineStructure.maximalAtlas _ (A (perm i)) :=
    ⟨(A (perm i)).out.holomorphic e he, fun c hc ↦ (A (perm i)).out.compatible c hc e he⟩
  let c := (F i).toHomeomorph.toOpenPartialHomeomorph.trans e
  have hcmax : c ∈ ComplexAffineStructure.maximalAtlas _ (A i) := hpull i e hemax
  have hb : curveGermBase (L (perm i)) η'.1 = (F i) (curveGermBase (L i) η.1) := by
    change curveGermBase _ (η.1.map (F i : L i → L (perm i))) = _
    induction η.1 using Filter.Germ.inductionOn with
    | h g => rfl
  have hsource : curveGermBase (L i) η.1 ∈ c.source := by
    simp only [c, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_source, mem_univ, true_and]
    change (F i) (curveGermBase (L i) η.1) ∈ e.source
    rwa [hb] at hpoint
  apply (hflat (perm i) e hemax η' hpoint).mpr
  have hz := (hflat i c hcmax η hsource).mp hdiag
  have heq : η'.1.map (e : L (perm i) → ℂ) = η.1.map (c : L i → ℂ) := by
    change (η.1.map (F i : L i → L (perm i))).map (e : _ → ℂ) = _
    rw [Filter.Germ.map_map]
    rfl
  rwa [heq]



variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))

/-- The original scalar slice of an ambient leaf-flowbox. (Ghys, Lemmas 3.2–3.3) -/
def nativeAffineFlowboxSlice (c : OpenPartialHomeomorph M
    (ℂ × (Fin (2*d-2) → ℝ))) (t : Fin (2*d-2) → ℝ) : Opens ℂ :=
  ⟨{z | (z,t) ∈ c.target},
    c.open_target.preimage (continuous_id.prodMk continuous_const)⟩

/-- The original invariant homogeneous section and its affine-structure correspondence on the intrinsic leaves. (Ghys, Lemmas 3.2–3.3) -/
structure NativeInvariantJetAffineLeafFamily where
  rankOne : HasComplexRankOne a.splitting.unstable.toDistribution
  holomorphic_inclusion : ∀ i,
    ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ x, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion x)
  asymptotic : ∃ m : MetricSpace M,
    m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M) ∧
    ∀ i (x : L i) y, (∃ z, (U.leaf i).inclusion z = y) ↔
      @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y
  boxCount : ℕ
  transverse : Fin boxCount → Opens (Fin (2*d-2) → ℝ)
  box : Fin boxCount → OpenPartialHomeomorph M (ℂ × (Fin (2*d-2) → ℝ))
  label : ∀ j, transverse j → ι
  branch : ∀ j t, Opens (L (label j t))
  parametrization : ∀ j t, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
    (nativeAffineFlowboxSlice (box j) t.val) (branch j t) ∞
  box_cover : ∀ x : M, ∃ j, x ∈ (box j).source
  transverse_contains : ∀ j p, p ∈ (box j).target → p.2 ∈ transverse j
  parametrization_inclusion : ∀ j t (z : nativeAffineFlowboxSlice (box j) t.val),
    (box j).symm (z.val,t.val) =
      (U.leaf (label j t)).inclusion (parametrization j t z).val
  permutation : ι ≃ ι
  leafMap : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (permutation i)) ∞
  leafMap_inclusion : ∀ i x,
    (U.leaf (permutation i)).inclusion (leafMap i x) = f ((U.leaf i).inclusion x)
  jetSection : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L
  section_continuous :
    @Continuous (NativeLeafwiseJet1 L) (NativeLeafwiseJet2 L)
      (nativeLeafwiseJet1Topology L U box) (nativeLeafwiseJet2Topology L U box) jetSection
  section_truncation : ∀ j, nativeLeafwiseJetTruncation L (jetSection j) = j
  section_homogeneous : ∀ (omega : ℂˣ) j,
    jetSection (nativeLeafwiseJet1Scale L omega j) =
      nativeLeafwiseJet2Reparametrize L (CurveJetReparametrization.scale omega) (jetSection j)
  leaf_holomorphic : ∀ i,
    letI : ∀ k, T2Space (L k) := fun k ↦ (U.leaf k).hausdorff
    letI : ∀ k, SecondCountableTopology (L k) := fun k ↦ (U.leaf k).countable
    letI := nativeLeafJet1Charts L i
    letI := nativeLeafJet2Charts L i
    ∃ tau : CurveJet1 (L i) → CurveJet2 (L i),
      (∀ v, jetSection (nativeLeafwiseJet1Inclusion L i v) =
        nativeLeafwiseJet2Inclusion L i (tau v)) ∧
      ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ tau
  section_invariant : ∀ i (gamma eta : CurveParamGerm (L i)),
    jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
      nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) eta) →
    ∃ delta theta : CurveParamGerm (L (permutation i)),
      delta.1 = gamma.1.map (leafMap i : L i → L (permutation i)) ∧
      theta.1 = eta.1.map (leafMap i : L i → L (permutation i)) ∧
      jetSection (nativeLeafwiseJet1Inclusion L (permutation i)
          (curveJet1Class (L (permutation i)) delta)) =
        nativeLeafwiseJet2Inclusion L (permutation i)
          (curveJet2Class (L (permutation i)) theta)
  affineAtlas : ∀ i, ComplexAffineAtlas (L i)
  flat_chart_iff : ∀ i (c : OpenPartialHomeomorph (L i) ℂ),
    c ∈ ComplexAffineStructure.maximalAtlas (L i)
      (Quotient.mk (complexAffineAtlasSetoid (L i)) (affineAtlas i)) ↔
    IsHolomorphicScalarChart (L i) c ∧
      ∀ gamma : CurveParamGerm (L i), curveGermBase (L i) gamma.1 ∈ c.source →
        (jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) gamma)) =
          nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) gamma) ↔
            germSecond (gamma.1.map (c : L i → ℂ)) = 0)

/-- The affine-structure class determined by the maximal flat-chart graph of the original section. (Ghys, Lemmas 3.2–3.3) -/
def NativeInvariantJetAffineLeafFamily.affineAt
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι) : ComplexAffineStructure (L i) :=
  Quotient.mk (complexAffineAtlasSetoid (L i)) (G.affineAtlas i)

end HolomorphicAnosov.Ghys
