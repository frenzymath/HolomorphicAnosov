import HolomorphicAnosov.Paper.Ghys.InvariantJetSection
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily

/-! This file constructs the affine leaf family induced by a native invariant jet section (Ghys, Lemmas 3.2–3.3). -/

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Constructs the affine leaf family associated with a native invariant homogeneous jet section. (Ghys, Lemmas 3.2–3.3) -/
theorem native_invariant_jet_affine_family_exists_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ (ι : Type u) (L : ι → Type u) (top : ∀ i, TopologicalSpace (L i)),
    let := top
    ∃ (realChart : ∀ i, ChartedSpace (Fin 2 → ℝ) (L i)),
    let := realChart
    ∃ (realSmooth : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)),
    let := realSmooth
    ∃ (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
      (complexChart : ∀ i, ChartedSpace ℂ (L i)),
    let := complexChart
    ∃ (complexSmooth : ∀ i, IsManifold 𝓘(ℂ) ∞ (L i)),
    let := complexSmooth
    Nonempty (NativeInvariantJetAffineLeafFamily f a L U) := by
  classical
  obtain ⟨ι, L, top, h⟩ := invariant_jet_section f a hRank
  let := top
  obtain ⟨realChart, h⟩ := h
  let := realChart
  obtain ⟨realSmooth, h⟩ := h
  let := realSmooth
  obtain ⟨U, complexChart, h⟩ := h
  let := complexChart
  obtain ⟨complexSmooth, h⟩ := h
  let := complexSmooth
  obtain ⟨himm, hasym, n, T, c, label, branch, param, hcover, htrans, hparam,
    perm, F, hF, hsection⟩ := h
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let : ∀ i, ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) := nativeLeafJet1Charts L
  let : ∀ i, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) := nativeLeafJet2Charts L
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  obtain ⟨σ, ⟨htrunc, hhom, hhol, hinv⟩, _⟩ := hsection
  choose tau htau htauhol using hhol
  have hleaftrunc (i : ι) (j : CurveJet1 (L i)) :
      curveJetTruncation (L i) (tau i j) = j := by
    have h := htrunc (nativeLeafwiseJet1Inclusion L i j)
    rw [htau] at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hleafhom (i : ι) (omega : ℂˣ) (j : CurveJet1 (L i)) :
      tau i (curveJet1Scale (L i) omega j) =
        curveJet2Reparametrize (L i) (.scale omega) (tau i j) := by
    have h := hhom omega (nativeLeafwiseJet1Inclusion L i j)
    change σ (nativeLeafwiseJet1Inclusion L i (curveJet1Scale (L i) omega j)) =
      nativeLeafwiseJet2Reparametrize L (.scale omega)
        (σ (nativeLeafwiseJet1Inclusion L i j)) at h
    rw [htau, htau] at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  let s (i : ι) : HomogeneousCurveJetSection (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) :=
    ⟨tau i, hleaftrunc i, htauhol i, hleafhom i⟩
  have hex (i : ι) : Nonempty (CurveJetAffineCorrespondence (L i)
      (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i)) :=
    native_leaf_jet_affine_correspondence_g1 L i
  let E := fun i ↦ Classical.choice (hex i)
  let affine (i : ι) : ComplexAffineStructure (L i) := (E i).equiv.symm (s i)
  have hrep (i : ι) : ∃ A : ComplexAffineAtlas (L i),
      Quotient.mk (complexAffineAtlasSetoid (L i)) A = affine i :=
    Quotient.exists_rep (affine i)
  choose A hA using hrep
  refine ⟨ι, L, top, realChart, realSmooth, U, complexChart, complexSmooth, ⟨{
    rankOne := hRank
    holomorphic_inclusion := himm
    asymptotic := hasym
    boxCount := n
    transverse := T
    box := c
    label := label
    branch := branch
    parametrization := param
    box_cover := hcover
    transverse_contains := htrans
    parametrization_inclusion := hparam
    permutation := perm
    leafMap := F
    leafMap_inclusion := hF
    jetSection := σ
    section_continuous := σ.continuous
    section_truncation := htrunc
    section_homogeneous := hhom
    leaf_holomorphic := fun i ↦ ⟨tau i, htau i, htauhol i⟩
    section_invariant := hinv
    affineAtlas := A
    flat_chart_iff := ?_
  }⟩⟩
  intro i e
  rw [hA, (E i).flat_chart_iff]
  constructor
  · rintro ⟨he, hflat⟩
    refine ⟨he, fun gamma hg ↦ ?_⟩
    have hf := hflat gamma hg
    simp only [affine, Equiv.apply_symm_apply] at hf
    rw [htau]
    simpa [s, nativeLeafwiseJet2Inclusion] using hf
  · rintro ⟨he, hflat⟩
    refine ⟨he, fun gamma hg ↦ ?_⟩
    have hf := hflat gamma hg
    rw [htau] at hf
    change ((E i).equiv ((E i).equiv.symm (s i))).1 _ = _ ↔ _
    rw [(E i).equiv.apply_symm_apply]
    simpa [s, nativeLeafwiseJet2Inclusion] using hf

end HolomorphicAnosov.Ghys

