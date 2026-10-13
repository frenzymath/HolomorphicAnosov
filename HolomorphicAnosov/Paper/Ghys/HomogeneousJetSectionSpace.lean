import HolomorphicAnosov.Paper.Ghys.JetPartitionSection
import HolomorphicAnosov.Paper.Ghys.NativeJetTangentCovectorTorsor

/-! This module describes the affine space of continuous homogeneous jet sections. (Ghys, §3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys

open Set _root_.Topology TopologicalSpace Bundle
open scoped ContDiff Manifold
universe u
set_option autoImplicit false

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

/-- The space of continuous homogeneous truncating sections of the original parametrization jets is nonempty and is an affine space over continuous complex covector fields on the unstable line. (Ghys, §3) -/
theorem homogeneous_jet_section_space [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    let K := fun x : M ↦ (hRank x).choose
    let E := fun x : M ↦ ↥(K x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
    ∃ (ι : Type u) (L : ι → Type u) (top : ∀ i, TopologicalSpace (L i)),
    letI := top
    ∃ (realChart : ∀ i, ChartedSpace (Fin 2 → ℝ) (L i)),
    letI := realChart
    ∃ (realSmooth : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)),
    letI := realSmooth
    ∃ (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
      (complexChart : ∀ i, ChartedSpace ℂ (L i)),
    letI := complexChart
    ∃ (complexSmooth : ∀ i, IsManifold 𝓘(ℂ) ∞ (L i)),
    letI := complexSmooth
    (∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z)) ∧
    (∃ m : MetricSpace M,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      ∀ i (x : L i) y, (∃ z, (U.leaf i).inclusion z = y) ↔
        @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y) ∧
    ∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
      (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
      (parametrization : ∀ i t,
        Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val) (branch i t) ∞),
    (∀ x : M, ∃ i, x ∈ (c i).source) ∧
    (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
    (∀ i t (z : scalarSlice (c i) t.val), (c i).symm (z.val, t.val) =
      (U.leaf (label i t)).inclusion ((parametrization i t z).val)) ∧
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∃ (hp : Continuous (nativeLeafwiseJetTruncation L)),
    let p : C(NativeLeafwiseJet2 L, NativeLeafwiseJet1 L) :=
      ⟨nativeLeafwiseJetTruncation L, hp⟩
    let S := SectionTransport.Section p (nativeLeafwiseJet1Scale L)
      (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
    ∃ (firstTangent : NativeLeafwiseJet1 L ≃ₜ P),
    (∀ j, (firstTangent j).val.proj = nativeLeafwiseJet1Base L U j) ∧
    (∀ i (gamma : CurveParamGerm (L i)),
      let j : NativeLeafwiseJet1 L := ⟨i, curveJet1Class (L i) gamma⟩
      let representative := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)
      (⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩ :
        TangentBundle (complexModel d) M) =
      ⟨representative 0, mfderiv 𝓘(ℂ) (complexModel d) representative 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩) ∧
    (∀ (omega : ℂˣ) j,
      (firstTangent (nativeLeafwiseJet1Scale L omega j)).val =
        ⟨(firstTangent j).val.proj, (omega : ℂ) • (firstTangent j).val.snd⟩) ∧
    Nonempty S ∧
    ∃ (alpha : S → S → ∀ x : M, E x →L[ℂ] ℂ),
      (∀ s t, Continuous (fun v : TotalSpace ℂ E ↦ alpha s t v.proj v.snd)) ∧
      (∀ s t (v : NativeLeafwiseJet1 L),
        nativeLeafwiseJet2Reparametrize L
          ⟨1, alpha s t (firstTangent v).val.proj (firstTangent v).val.snd⟩ (s.val v) =
        t.val v) ∧
      (∀ s, alpha s s = 0) ∧
      (∀ s t, alpha t s = -alpha s t) ∧
      (∀ s t r, alpha s r = alpha s t + alpha t r) ∧
      (∀ (s : S) (beta : ∀ x : M, E x →L[ℂ] ℂ),
        Continuous (fun v : TotalSpace ℂ E ↦ beta v.proj v.snd) →
        ∃! t : S, alpha s t = beta) := by
  obtain ⟨ι, L, top, realChart, realSmooth, U, complexChart, complexSmooth,
    himm, hmetric, hinv, n, T, c, label, branch, parametrization,
    hcover, htarget, hparam, hjet⟩ :=
    JetPartitionSection.jet_partition_section f a hRank
  let := top
  let := realChart
  let := realSmooth
  let := complexChart
  let := complexSmooth
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  obtain ⟨e1, e2, hcharts, localSection, rho, s, hlocalContinuous, hlocalTruncation,
    hlocalGerm, hlocalHolomorphic, hlocalScaling, hrho, hrhoSum, hsContinuous,
    hsTruncation, hsScaling, hsWeighted, hsAnchor⟩ := hjet
  obtain ⟨hp, firstTangent, hbase, hderivative, hscale, alpha, halpha⟩ :=
    native_jet_tangent_covector_torsor L hRank U himm T c label branch
      parametrization hcover htarget hparam
  refine ⟨ι, L, top, realChart, realSmooth, U, complexChart, complexSmooth,
    himm, hmetric, n, T, c, label, branch, parametrization, hcover, htarget,
    hparam, hp, firstTangent, hbase, hderivative, hscale, ?_, alpha, halpha⟩
  exact ⟨⟨⟨s, hsContinuous⟩, hsTruncation, hsScaling⟩⟩

end HolomorphicAnosov.Ghys
