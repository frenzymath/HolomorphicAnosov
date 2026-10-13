import HolomorphicAnosov.Ghys.TransportedJetApproximationG16
import HolomorphicAnosov.Ghys.CompactLocalJetShiftBoundG16
import HolomorphicAnosov.Geometry.CompactFlowboxSliceBuffers
import HolomorphicAnosov.Ghys.InvariantJetHolomorphicLimitG16
import HolomorphicAnosov.Ghys.BackwardLeafDiskPlaqueG16
import HolomorphicAnosov.Ghys.NativeFlowboxJetGluingG13
import HolomorphicAnosov.Ghys.NativeFlowboxJetZeroSectionsG13
import HolomorphicAnosov.Ghys.NativeFlowboxOverlapContinuityG16
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Ghys.CurveJetAffineData
import Mathlib.Topology.MetricSpace.Contracting
import HolomorphicAnosov.Ghys.CurveParamGermTangent
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalNormComparison
import HolomorphicAnosov.Paper.Ghys.NativeUnstableLineNormComparisonCompatible
import HolomorphicAnosov.Analysis.ContinuousLineCovectorNorm
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Ghys.JetDynamics
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Paper.Ghys.HomogeneousJetSectionMetric
import HolomorphicAnosov.Paper.Ghys.HomogeneousJetSectionSpace
import HolomorphicAnosov.Paper.Ghys.JetPartitionSection
import HolomorphicAnosov.Paper.Ghys.SectionTransport
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle
import HolomorphicAnosov.Ghys.NativeLeafwiseJetTopologyRange
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineVectorBundle
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineMetric

/-! This module constructs the invariant homogeneous jet section. (Ghys, Lems. 3.2–3.3) -/

set_option maxHeartbeats 800000
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Bundle BigOperators
universe u
set_option autoImplicit false
attribute [local instance] complex_isManifold_real

/-- There is a continuous, homogeneous, leafwise-holomorphic section of the original jet bundle invariant under the holomorphic Anosov map. (Ghys, Lems. 3.2–3.3) -/
theorem invariant_jet_section {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
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
      ∀ x, Function.Injective
        (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion x)) ∧
    (∃ m : MetricSpace M,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      ∀ i (x : L i) y, (∃ z, (U.leaf i).inclusion z = y) ↔
        @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y) ∧
    ∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
      (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
      (param : ∀ i t, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
        (scalarSlice (c i) t.val)
        (branch i t) ∞),
      (∀ x : M, ∃ i, x ∈ (c i).source) ∧
      (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
      (∀ i t (z : scalarSlice (c i) t.val),
        (c i).symm (z.val, t.val) = (U.leaf (label i t)).inclusion (param i t z).val) ∧
      ∃ (perm : ι ≃ ι)
        (F : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞),
        (∀ i x, (U.leaf (perm i)).inclusion (F i x) = f ((U.leaf i).inclusion x)) ∧
        letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
        letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
        letI : ∀ i, ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) := nativeLeafJet1Charts L
        letI : ∀ i, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) :=
          nativeLeafJet2Charts L
        letI : ∀ i, IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L i)) :=
          nativeLeafJet1Manifold L
        letI : ∀ i, IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L i)) :=
          nativeLeafJet2Manifold L
        letI := nativeLeafwiseJet1Topology L U c
        letI := nativeLeafwiseJet2Topology L U c
        ∃! σ : C(NativeLeafwiseJet1 L, NativeLeafwiseJet2 L),
          (∀ j, nativeLeafwiseJetTruncation L (σ j) = j) ∧
          (∀ (omega : ℂˣ) j, σ (nativeLeafwiseJet1Scale L omega j) =
            nativeLeafwiseJet2Reparametrize L (CurveJetReparametrization.scale omega) (σ j)) ∧
          (∀ i, ∃ τ : CurveJet1 (L i) → CurveJet2 (L i),
            (∀ v, σ (nativeLeafwiseJet1Inclusion L i v) =
              nativeLeafwiseJet2Inclusion L i (τ v)) ∧
            ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ τ) ∧
          (∀ i (γ η : CurveParamGerm (L i)),
            σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
                nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) η) →
            ∃ δ θ : CurveParamGerm (L (perm i)),
              δ.1 = γ.1.map (F i : L i → L (perm i)) ∧
              θ.1 = η.1.map (F i : L i → L (perm i)) ∧
              σ (nativeLeafwiseJet1Inclusion L (perm i)
                  (curveJet1Class (L (perm i)) δ)) =
                nativeLeafwiseJet2Inclusion L (perm i)
                  (curveJet2Class (L (perm i)) θ)) := by
  classical
  obtain ⟨ι, L, top, h⟩ := jet_dynamics f a hRank
  let := top
  obtain ⟨realChart, h⟩ := h
  let := realChart
  obtain ⟨realSmooth, U, complexChart, h⟩ := h
  let := realSmooth
  let := complexChart
  obtain ⟨complexSmooth, h⟩ := h
  let := complexSmooth
  obtain ⟨himm, hasym, D, F, G, hF, hFi, hGi, n, T, c, label, branch,
    param, hcover, htrans, hparam, hjet⟩ := h
  refine ⟨ι, L, top, realChart, realSmooth, U, complexChart, complexSmooth,
    himm, hasym, n, T, c, label, branch, param, hcover, htrans, hparam,
    D.permutation, F, hFi, ?_⟩
  have htop1 := nativeLeafwiseJet1Topology_eq_leafFamilyJet1Topology_range U c
  have htop2 := nativeLeafwiseJet2Topology_eq_leafFamilyJet2Topology_range U c
  rw [← htop1, ← htop2] at hjet
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  obtain ⟨Φ₁, Φ₂, hforward, hbackward, hbase, htrunc, hscale1, hscale2, hcharts⟩ := hjet
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let : ∀ i, ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) := nativeLeafJet1Charts L
  let : ∀ i, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) := nativeLeafJet2Charts L
  let : ∀ i, IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L i)) := nativeLeafJet1Manifold L
  let : ∀ i, IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L i)) :=
    nativeLeafJet2Manifold L
  suffices hex : ∃! σ : C(NativeLeafwiseJet1 L, NativeLeafwiseJet2 L),
      (∀ j, nativeLeafwiseJetTruncation L (σ j) = j) ∧
      (∀ (omega : ℂˣ) j, σ (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet2Reparametrize L (.scale omega) (σ j)) ∧
      (∀ i, ∃ τ : CurveJet1 (L i) → CurveJet2 (L i),
        (∀ v, σ (nativeLeafwiseJet1Inclusion L i v) =
          nativeLeafwiseJet2Inclusion L i (τ v)) ∧
        ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ τ) ∧
      (∀ j, σ (Φ₁ j) = Φ₂ (σ j)) by
    obtain ⟨σ, ⟨hp, ha, hhol, heq⟩, huniq⟩ := hex
    refine ⟨σ, ⟨hp, ha, hhol, ?_⟩, ?_⟩
    · intro i γ η hση
      obtain ⟨δ, hδ, hδ1, hδ2⟩ := hforward i γ
      obtain ⟨θ, hθ, hθ1, hθ2⟩ := hforward i η
      refine ⟨δ, θ, hδ, hθ, ?_⟩
      change σ ⟨D.permutation i, curveJet1Class (L (D.permutation i)) δ⟩ =
        ⟨D.permutation i, curveJet2Class (L (D.permutation i)) θ⟩
      rw [← hδ1, heq]
      change Φ₂ (σ (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ))) = _
      rw [hση]
      change Φ₂ ⟨i, curveJet2Class (L i) η⟩ = _
      rw [hθ2]
    · intro τ hτ
      obtain ⟨hpτ, haτ, hholτ, heqτ⟩ := hτ
      apply huniq τ
      refine ⟨hpτ, haτ, hholτ, ?_⟩
      rintro ⟨i, j⟩
      induction j using Quotient.inductionOn with
      | h γ =>
        obtain ⟨ρ, hρ, _⟩ := hholτ i
        obtain ⟨η, hη⟩ := Quotient.exists_rep (ρ (curveJet1Class (L i) γ))
        have hw : τ ⟨i, curveJet1Class (L i) γ⟩ =
            ⟨i, curveJet2Class (L i) η⟩ := by
          have hh := hρ (curveJet1Class (L i) γ)
          change τ ⟨i, curveJet1Class (L i) γ⟩ =
            ⟨i, ρ (curveJet1Class (L i) γ)⟩ at hh
          simpa only [← hη, curveJet2Class] using hh
        obtain ⟨δ, θ, hδ, hθ, he⟩ := heqτ i γ η hw
        obtain ⟨δ', hδ', hδ1, hδ2⟩ := hforward i γ
        obtain ⟨θ', hθ', hθ1, hθ2⟩ := hforward i η
        have hdd : δ = δ' := Subtype.ext (hδ.trans hδ'.symm)
        have htt : θ = θ' := Subtype.ext (hθ.trans hθ'.symm)
        subst δ'
        subst θ'
        change τ (Φ₁ ⟨i, curveJet1Class (L i) γ⟩) =
          Φ₂ (τ ⟨i, curveJet1Class (L i) γ⟩)
        rw [hδ1, hw, hθ2]
        exact he
  by_cases hJ : IsEmpty (NativeLeafwiseJet1 L)
  · let := hJ
    let σ : C(NativeLeafwiseJet1 L, NativeLeafwiseJet2 L) :=
      ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun j ↦ isEmptyElim j)⟩
    refine ⟨σ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact fun j ↦ isEmptyElim j
    · exact fun _ j ↦ isEmptyElim j
    · intro i
      refine ⟨fun v ↦ isEmptyElim (nativeLeafwiseJet1Inclusion L i v), ?_, ?_⟩
      · exact fun v ↦ isEmptyElim (nativeLeafwiseJet1Inclusion L i v)
      · exact fun v ↦ isEmptyElim (nativeLeafwiseJet1Inclusion L i v)
    · exact fun j ↦ isEmptyElim j
    · intro τ hτ
      apply ContinuousMap.ext
      intro j
      exact isEmptyElim j
  ·
    have : Nonempty (NativeLeafwiseJet1 L) := not_isEmpty_iff.mp hJ
    have : Nonempty (NativeLeafwiseJet2 L) := by
      obtain ⟨i, j⟩ := Classical.choice (inferInstance : Nonempty (NativeLeafwiseJet1 L))
      obtain ⟨gamma, rfl⟩ := Quotient.exists_rep j
      exact ⟨⟨i, curveJet2Class (L i) gamma⟩⟩
    have hoverlap := native_flowbox_overlap_derivatives_continuous L
      (fun i ↦ (U.leaf i).inclusion) U.cover c (by
        intro k i x hx
        obtain ⟨q, hq, _, hcoord, _⟩ := native_flowbox_receiving_chart L U (T k)
          (c k) (label k) (branch k) (param k) (htrans k) (hparam k) i x hx
        exact ⟨q, hq, hcoord⟩)
    obtain ⟨E1, E2, hE⟩ := native_flowbox_jet_charts L U T c label branch param
      htrans hparam hcover (fun k l ↦ (hoverlap k l).1) (fun k l ↦ (hoverlap k l).2)
    obtain ⟨localSection, hlocalContinuous, hlocalCoeff, hlocalGerm,
      hlocalHolomorphic, hlocalScaling⟩ := native_flowbox_zero_sections_full L U T c
        label branch param htrans hparam E1 E2 hE
    obtain ⟨rho, hrhoSupport, hrhoSum, _, _⟩ :=
      exists_continuous_sum_one_of_isOpen_isCompact
        (fun k ↦ (c k).open_source) isCompact_univ (by
          intro x _
          obtain ⟨k, hk⟩ := hcover x
          exact mem_iUnion.mpr ⟨k, hk⟩)
    have hrhoSumReal : ∀ x, ∑ k : Fin n, rho k x = 1 := by
      intro x
      simpa only [Finset.sum_apply, Pi.one_apply] using hrhoSum (mem_univ x)
    obtain ⟨sRef, hsRefContinuous, hsRefTruncation, hsRefScaling, _⟩ :=
      native_flowbox_glued_section L U T c label branch param htrans hparam hcover
        (fun k ↦ rho k) (fun k ↦ ⟨(rho k).continuous, hrhoSupport k⟩) hrhoSumReal
        E1 E2 hE localSection hlocalContinuous (fun k j ↦ (hlocalCoeff k j).1)
        hlocalScaling
    obtain ⟨hp, firstTangent, hfirstBase, hfirstRep, hfirstScale,
      alpha, halphaContinuous, halphaShift, halphaZero, halphaNeg,
      halphaAdd, halphaTranslate⟩ :=
      native_jet_tangent_covector_torsor L hRank U himm T c label branch
        param hcover htrans hparam
    let tangent : NativeLeafwiseJet1 L → TangentBundle (complexModel d) M :=
      fun j ↦ ⟨(firstTangent j).val.proj, (firstTangent j).val.snd.val⟩
    have hbackTangent (j : NativeLeafwiseJet1 L) :
        tangent (Φ₁.symm j) =
          tangentMap (complexModel d) (complexModel d) f.symm (tangent j) := by
      obtain ⟨i, j⟩ := j
      induction j using Quotient.inductionOn with
      | h gamma =>
        obtain ⟨delta, hd, hd1, hd2⟩ := hbackward i gamma
        change tangent (Φ₁.symm ⟨i, curveJet1Class (L i) gamma⟩) =
          tangentMap (complexModel d) (complexModel d) f.symm
            (tangent ⟨i, curveJet1Class (L i) gamma⟩)
        rw [hd1]
        change (⟨(firstTangent ⟨D.permutation.symm i,
          curveJet1Class (L (D.permutation.symm i)) delta⟩).val.proj,
          (firstTangent ⟨D.permutation.symm i,
          curveJet1Class (L (D.permutation.symm i)) delta⟩).val.snd.val⟩ :
          TangentBundle (complexModel d) M) = _
        rw [hfirstRep (D.permutation.symm i) delta]
        change _ = tangentMap (complexModel d) (complexModel d) f.symm
          ⟨(firstTangent ⟨i, curveJet1Class (L i) gamma⟩).val.proj,
          (firstTangent ⟨i, curveJet1Class (L i) gamma⟩).val.snd.val⟩
        rw [hfirstRep i gamma]
        have hevent : delta.val.out =ᶠ[𝓝 (0 : ℂ)]
            (G i : L i → L (D.permutation.symm i)) ∘ gamma.val.out := by
          apply Filter.Germ.coe_eq.mp
          exact (Quotient.out_eq delta.val).trans
            (hd.trans ((congrArg (fun g : Filter.Germ (𝓝 (0 : ℂ)) (L i) ↦
              g.map (G i : L i → L (D.permutation.symm i)))
              (Quotient.out_eq gamma.val).symm).trans
              (Filter.Germ.map_coe _ _)))
        have hamb : (fun z : ℂ ↦ (U.leaf (D.permutation.symm i)).inclusion
            (delta.val.out z)) =ᶠ[𝓝 (0 : ℂ)]
            (fun z : ℂ ↦ f.symm ((U.leaf i).inclusion (gamma.val.out z))) := by
          filter_upwards [hevent] with z hz
          rw [hz]
          exact hGi i _
        have hgamma : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) gamma.val.out 0 :=
          mdifferentiableAt_of_mfderiv_injective
            (curveParamGerm_mfderiv_bijective gamma).injective
        have hinc : MDifferentiableAt 𝓘(ℂ) (complexModel d)
            (fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z)) 0 :=
          ((himm i).1.mdifferentiable (by simp) _).comp 0 hgamma
        have hchain := tangentMap_comp_at
          (I := 𝓘(ℂ)) (I' := complexModel d) (I'' := complexModel d)
          (f := fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z))
          (g := f.symm)
          (⟨0, (tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1⟩)
          (f.symm.contMDiff.mdifferentiable (by simp) _) hinc
        change _ = tangentMap (complexModel d) (complexModel d) f.symm
          (tangentMap 𝓘(ℂ) (complexModel d)
            (fun z : ℂ ↦ (U.leaf i).inclusion (gamma.val.out z))
            ⟨0, (tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1⟩)
        rw [← hchain]
        apply Bundle.TotalSpace.ext hamb.eq_of_nhds
        rw [hamb.mfderiv_eq]
        rfl
    have hbackTangentIter (n : ℕ) (j : NativeLeafwiseJet1 L) :
        tangent ((Φ₁.symm : _ → _)^[n] j) =
          tangentMap (complexModel d) (complexModel d)
            ((f.symm : M → M)^[n]) (tangent j) := by
      induction n with
      | zero => simp [tangentMap]; rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', hbackTangent, ih]
        simpa only [Function.iterate_succ'] using (tangentMap_comp_at (tangent j)
          (f.symm.contMDiff.mdifferentiable (by simp) _)
          ((f.symm.contMDiff.iterate n).mdifferentiable (by simp) _)).symm
    let originalNorm (v : TangentBundle (complexModel d) M) : ℝ :=
      letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      ‖complexTangentToReal d v.proj v.snd‖
    have horiginalDecay : ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧
        ∀ n j, originalNorm (tangent ((Φ₁.symm : _ → _)^[n] j)) ≤
          C * q ^ n * originalNorm (tangent j) := by
      let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      obtain ⟨C, q, hC, hq, hq1, _, hUdecay⟩ :=
        fixed_block_uniform_anosov_estimates f a
      refine ⟨C, q, hC, hq, hq1, ?_⟩
      intro n j
      have hmem : complexTangentToReal d (tangent j).proj (tangent j).snd ∈
          a.splitting.unstable.toDistribution (tangent j).proj := by
        rw [← (hRank (tangent j).proj).choose_spec.2]
        exact Submodule.mem_map_of_mem (firstTangent j).val.snd.property
      have hh := hUdecay n (tangent j).proj _ hmem
      rw [mfderiv_complex_to_real
        ((f.symm.contMDiff.iterate n).mdifferentiable (by simp) _)] at hh
      rw [hbackTangentIter]
      exact hh
    let p : C(NativeLeafwiseJet2 L, NativeLeafwiseJet1 L) :=
      ⟨nativeLeafwiseJetTruncation L, hp⟩
    let Sections := SectionTransport.Section p (nativeLeafwiseJet1Scale L)
      (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
    have hNonemptySections : Nonempty Sections :=
      ⟨⟨⟨sRef, hsRefContinuous⟩, hsRefTruncation, hsRefScaling⟩⟩
    have hscaleFirst : ∀ (omega : ℂˣ) j,
        Φ₁ (nativeLeafwiseJet1Scale L omega j) =
          nativeLeafwiseJet1Scale L omega (Φ₁ j) := fun omega j ↦
      hscale1 omega 0 j
    have hscaleSecond : ∀ (omega : ℂˣ) j,
        Φ₂ (nativeLeafwiseJet2Reparametrize L (.scale omega) j) =
          nativeLeafwiseJet2Reparametrize L (.scale omega) (Φ₂ j) := fun omega j ↦
      hscale2 omega 0 j
    let Q : Sections → Sections := SectionTransport.forward p
      (nativeLeafwiseJet1Scale L)
      (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
      Φ₁ Φ₂ htrunc hscaleFirst hscaleSecond
    let P : Sections → Sections := SectionTransport.backward p
      (nativeLeafwiseJet1Scale L)
      (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
      Φ₁ Φ₂ htrunc hscaleFirst hscaleSecond
    have htransport : Function.LeftInverse P Q ∧ Function.RightInverse P Q ∧
        ∀ s : Sections, Q s = s ↔ ∀ j, s.val (Φ₁ j) = Φ₂ (s.val j) :=
      SectionTransport.transport_inverse_and_fixed_iff p
        (nativeLeafwiseJet1Scale L)
        (fun omega ↦ nativeLeafwiseJet2Reparametrize L (.scale omega))
        Φ₁ Φ₂ htrunc hscaleFirst hscaleSecond
    let Δ : Sections → Sections → NativeLeafwiseJet1 L → ℂ :=
      fun s t j ↦ alpha s t (firstTangent j).val.proj (firstTangent j).val.snd
    have hΔshift (s t : Sections) (j : NativeLeafwiseJet1 L) :
        nativeLeafwiseJet2Reparametrize L ⟨1, Δ s t j⟩ (s.val j) = t.val j :=
      halphaShift s t j
    have hshiftUnique (z w : NativeLeafwiseJet2 L)
        (hzw : nativeLeafwiseJetTruncation L z = nativeLeafwiseJetTruncation L w) :
        ∃! μ : ℂ, nativeLeafwiseJet2Reparametrize L ⟨1, μ⟩ z = w := by
      rcases z with ⟨i, z⟩
      rcases w with ⟨j, w⟩
      have hij : i = j := congrArg Sigma.fst hzw
      subst j
      have he : curveJetTruncation (L i) z = curveJetTruncation (L i) w :=
        eq_of_heq (Sigma.mk.inj hzw).2
      obtain ⟨μ, hμ, huniq⟩ := nativeLeafFibreShiftUnique i he
      refine ⟨μ, congrArg (Sigma.mk i) hμ, ?_⟩
      intro a ha
      exact huniq a (eq_of_heq (Sigma.mk.inj ha).2)
    have hΔtransport (s t : Sections) (j : NativeLeafwiseJet1 L) :
        Δ (Q s) (Q t) j = Δ s t (Φ₁.symm j) := by
      obtain ⟨μ, hμ, huniq⟩ := hshiftUnique ((Q s).val j) ((Q t).val j)
        ((Q s).property.1 j |>.trans ((Q t).property.1 j).symm)
      apply (huniq _ (hΔshift (Q s) (Q t) j)).trans
      apply Eq.symm
      apply huniq
      change nativeLeafwiseJet2Reparametrize L ⟨1, Δ s t (Φ₁.symm j)⟩
        (Φ₂ (s.val (Φ₁.symm j))) = Φ₂ (t.val (Φ₁.symm j))
      exact (hscale2 1 (Δ s t (Φ₁.symm j)) (s.val (Φ₁.symm j))).symm.trans
        (congrArg Φ₂ (hΔshift s t (Φ₁.symm j)))
    have hΔiterate (n : ℕ) (s t : Sections) (j : NativeLeafwiseJet1 L) :
        Δ (Q^[n] s) (Q^[n] t) j = Δ s t ((Φ₁.symm : _ → _)^[n] j) := by
      induction n generalizing j with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hΔtransport,
          ih, Function.iterate_succ_apply]
    have hΔzero (s : Sections) (j : NativeLeafwiseJet1 L) : Δ s s j = 0 :=
      congrArg (fun b ↦ b (firstTangent j).val.proj (firstTangent j).val.snd)
        (halphaZero s)
    have hΔneg (s t : Sections) (j : NativeLeafwiseJet1 L) :
        Δ t s j = -Δ s t j :=
      congrArg (fun b ↦ b (firstTangent j).val.proj (firstTangent j).val.snd)
        (halphaNeg s t)
    have hΔadd (s t r : Sections) (j : NativeLeafwiseJet1 L) :
        Δ s r j = Δ s t j + Δ t r j :=
      congrArg (fun b ↦ b (firstTangent j).val.proj (firstTangent j).val.snd)
        (halphaAdd s t r)
    let S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x) :=
      fun x ↦ (hRank x).choose
    have hS : ∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x := by
      intro x
      exact (hRank x).choose_spec.2
    obtain ⟨Tbundle, hT⟩ := complex_subbundle_of_realification
      a.splitting.unstable S hS
    have hTS : Tbundle.toDistribution = S := by simpa using hT
    have hRankS : ∀ x, Module.finrank ℂ (S x) = 1 := by
      intro x
      exact (hRank x).choose_spec.1
    let : TopologicalSpace (Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    have hΔcontinuous (s t : Sections) : Continuous (Δ s t) :=
      (halphaContinuous s t).comp
        (continuous_subtype_val.comp firstTangent.continuous)
    obtain ⟨fb, hvb⟩ := exists_native_complex_line_vectorBundle Tbundle S hTS hRankS
    let : FiberBundle ℂ (fun x : M ↦ ↥(S x)) := fb
    let : VectorBundle ℂ ℂ (fun x : M ↦ ↥(S x)) := hvb
    obtain ⟨core, hcore⟩ := exists_native_complex_line_metric Tbundle S hTS hRankS
    let : ∀ x, NormedAddCommGroup (S x) := fun x ↦
      (core x).toNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (S x) := fun x ↦
      InnerProductSpace.ofCore (core x).toCore
    obtain ⟨hNative, hhNative, cNative, CNative, hcNative, hcNativeC,
      hNativeCompare⟩ := exists_native_unstable_line_norm_comparison_compatible
      Tbundle S hTS hRankS core hcore
    have hnorm : Continuous (fun z : Bundle.TotalSpace ℂ (fun x : M ↦ ↥(S x)) ↦ ‖z.snd‖) := hcore
    let ν : NativeLeafwiseJet1 L → ℝ := fun j ↦ ‖(firstTangent j).val.snd‖
    have hνcontinuous : Continuous ν :=
      hnorm.comp (continuous_subtype_val.comp firstTangent.continuous)
    have hνpositive : ∀ j, 0 < ν j := fun j ↦
      norm_pos_iff.mpr (firstTangent j).property
    have hνscale : ∀ (omega : ℂˣ) j,
        ν (nativeLeafwiseJet1Scale L omega j) = ‖(omega : ℂ)‖ * ν j := by
      intro omega j
      have he := hfirstScale omega j
      change ‖(firstTangent (nativeLeafwiseJet1Scale L omega j)).val.snd‖ = _
      rw [he]
      exact norm_smul (omega : ℂ) (firstTangent j).val.snd
    let frames : M → Bundle.Trivialization ℂ
        (Bundle.TotalSpace.proj (F := ℂ) (E := fun x ↦ S x)) :=
      fun x ↦ trivializationAt ℂ (fun y ↦ S y) x
    have hframes : ∀ x, (frames x).IsLinear ℂ := fun x ↦ inferInstance
    have hframesCover : ∀ x : M, ∃ i, x ∈ (frames i).baseSet :=
      fun x ↦ ⟨x, FiberBundle.mem_baseSet_trivializationAt ℂ (fun y ↦ S y) x⟩
    let originalContinuous (b : ∀ x : M, S x →ₗ[ℂ] ℂ) :
        ∀ x : M, S x →L[ℂ] ℂ := fun x ↦ (b x).toContinuousLinearMap
    let αLinear (s t : Sections) (x : M) : S x →ₗ[ℂ] ℂ :=
      (alpha s t x).toLinearMap
    let : ∀ x, TopologicalSpace (S x) := fun x ↦
      (core x).toNormedAddCommGroup.toUniformSpace.toTopologicalSpace
    let β (s t : Sections) (x : M) : S x →L[ℂ] ℂ :=
      (αLinear s t x).toContinuousLinearMap
    have hβcontinuous (s t : Sections) :
        Continuous (fun v : Bundle.TotalSpace ℂ (fun x ↦ S x) ↦
          β s t v.proj v.snd) := halphaContinuous s t
    have hβnorm (s t : Sections) : Continuous (fun x ↦ ‖β s t x‖) :=
      continuous_line_covector_norm hnorm frames hframesCover
        (β s t) (hβcontinuous s t)
    have hβbounded (s t : Sections) : BddAbove (range (fun x ↦ ‖β s t x‖)) :=
      (isCompact_range (hβnorm s t)).bddAbove
    have hΔbounded (s t : Sections) :
        BddAbove (range (fun j ↦ ‖Δ s t j‖ / ν j)) := by
      obtain ⟨C, hC⟩ := hβbounded s t
      refine ⟨C, ?_⟩
      rintro _ ⟨j, rfl⟩
      apply (div_le_iff₀ (hνpositive j)).mpr
      exact ((β s t (firstTangent j).val.proj).le_opNorm
        (firstTangent j).val.snd).trans
        (mul_le_mul_of_nonneg_right (hC ⟨(firstTangent j).val.proj, rfl⟩)
          (hνpositive j).le)
    let distance (s t : Sections) : ℝ :=
      sSup (range (fun j ↦ ‖Δ s t j‖ / ν j))
    have hpointBound (s t : Sections) (j : NativeLeafwiseJet1 L) :
        ‖Δ s t j‖ ≤ distance s t * ν j :=
      (div_le_iff₀ (hνpositive j)).mp (le_csSup (hΔbounded s t) ⟨j, rfl⟩)
    have hdistNonneg (s t : Sections) : 0 ≤ distance s t := by
      obtain ⟨j⟩ := not_isEmpty_iff.mp hJ
      exact (div_nonneg (norm_nonneg _) (hνpositive j).le).trans
        (le_csSup (hΔbounded s t) ⟨j, rfl⟩)
    have hdistContract (n : ℕ) (C : ℝ)
        (hback : ∀ j, ν ((Φ₁.symm : _ → _)^[n] j) ≤ C * ν j)
        (s t : Sections) : distance (Q^[n] s) (Q^[n] t) ≤ C * distance s t := by
      have hne : (range (fun j ↦ ‖Δ (Q^[n] s) (Q^[n] t) j‖ / ν j)).Nonempty := by
        obtain ⟨j⟩ := not_isEmpty_iff.mp hJ
        exact ⟨_, ⟨j, rfl⟩⟩
      apply csSup_le hne
      rintro _ ⟨j, rfl⟩
      apply (div_le_iff₀ (hνpositive j)).mpr
      rw [hΔiterate]
      exact (hpointBound s t _).trans
        ((mul_le_mul_of_nonneg_left (hback j) (hdistNonneg s t)).trans_eq
          (by ring))
    have hdistSelf (s : Sections) : distance s s = 0 := by
      have : Nonempty (NativeLeafwiseJet1 L) := not_isEmpty_iff.mp hJ
      simp only [distance, hΔzero, norm_zero, zero_div, Set.range_const, csSup_singleton]
    have hdistSymm (s t : Sections) : distance s t = distance t s := by
      apply congrArg sSup
      apply congrArg Set.range
      funext j
      rw [hΔneg s t j, norm_neg]
    have hdistTriangle (s t r : Sections) :
        distance s r ≤ distance s t + distance t r := by
      have : Nonempty (NativeLeafwiseJet1 L) := not_isEmpty_iff.mp hJ
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨j, rfl⟩
      apply (div_le_iff₀ (hνpositive j)).mpr
      rw [hΔadd s t r j, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hpointBound s t j) (hpointBound t r j))
    have hdistEq (s t : Sections) (h : distance s t = 0) : s = t := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro j
      have hz : Δ s t j = 0 := norm_eq_zero.mp (le_antisymm
        (by simpa only [h, zero_mul] using hpointBound s t j) (norm_nonneg _))
      have hss := hΔshift s s j
      have hst := hΔshift s t j
      rw [hΔzero] at hss
      rw [hz] at hst
      exact hss.symm.trans hst
    let sectionMetric : MetricSpace Sections :=
      { dist := distance
        dist_self := hdistSelf
        dist_comm := hdistSymm
        dist_triangle := hdistTriangle
        eq_of_dist_eq_zero := fun {s t} h ↦ hdistEq s t h }
    let field (s t : Sections) : lp (fun x : M ↦ S x →L[ℂ] ℂ) (⊤ : ENNReal) :=
      ⟨β s t, memℓp_infty_iff.mpr (hβbounded s t)⟩
    have hfieldNorm (s t : Sections) : ‖field s t‖ = distance s t := by
      apply le_antisymm
      · apply lp.norm_le_of_forall_le (hdistNonneg s t)
        intro x
        apply (β s t x).opNorm_le_bound (hdistNonneg s t)
        intro v
        by_cases hv : v = 0
        · simp [hv]
        · let vp : {v : Bundle.TotalSpace ℂ (fun x ↦ S x) // v.snd ≠ 0} :=
            ⟨⟨x, v⟩, hv⟩
          obtain ⟨j, hj⟩ := firstTangent.surjective vp
          have hh := hpointBound s t j
          change ‖β s t (firstTangent j).val.proj (firstTangent j).val.snd‖ ≤
              distance s t * ‖(firstTangent j).val.snd‖ at hh
          have he := congrArg
            (fun w : {v : Bundle.TotalSpace ℂ (fun x ↦ S x) // v.snd ≠ 0} ↦
              ‖β s t w.val.proj w.val.snd‖ ≤ distance s t * ‖w.val.snd‖) hj
          exact he.mp hh
      · have : Nonempty (NativeLeafwiseJet1 L) := not_isEmpty_iff.mp hJ
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨j, rfl⟩
        apply (div_le_iff₀ (hνpositive j)).mpr
        exact ((β s t (firstTangent j).val.proj).le_opNorm
          (firstTangent j).val.snd).trans
          (mul_le_mul_of_nonneg_right
            (lp.norm_apply_le_norm ENNReal.top_ne_zero (field s t)
              (firstTangent j).val.proj) (hνpositive j).le)
    have hcomplete : @CompleteSpace Sections sectionMetric.toUniformSpace := by
      let : MetricSpace Sections := sectionMetric
      by_cases hne : Nonempty Sections
      · obtain ⟨s₀⟩ := hne
        let V := {b : lp (fun x : M ↦ S x →L[ℂ] ℂ) (⊤ : ENNReal) |
          Continuous (fun v : Bundle.TotalSpace ℂ (fun x ↦ S x) ↦ b v.proj v.snd)}
        have hclosed := continuous_dual_evaluation_closed hnorm
        have : CompleteSpace V := hclosed.completeSpace_coe
        let A : Sections → V := fun s ↦ ⟨field s₀ s, hβcontinuous s₀ s⟩
        have hAinjective : Function.Injective A := by
          intro s t hst
          have he : alpha s₀ s = alpha s₀ t := by
            funext x
            apply DFunLike.ext
            intro v
            exact congrArg (fun b : V ↦ b.val x v) hst
          obtain ⟨r, hr, huniq⟩ :=
            halphaTranslate s₀ (alpha s₀ s) (halphaContinuous s₀ s)
          exact (huniq s rfl).trans (huniq t he.symm).symm
        have hAsurjective : Function.Surjective A := by
          intro b
          let b₀ := originalContinuous (fun x ↦ (b.val x).toLinearMap)
          have hb₀ : Continuous (fun v : Bundle.TotalSpace ℂ (fun x ↦ S x) ↦
              b₀ v.proj v.snd) := b.property
          obtain ⟨t, ht, huniq⟩ := halphaTranslate s₀ b₀ hb₀
          refine ⟨t, ?_⟩
          apply Subtype.ext
          apply lp.ext
          funext x
          apply DFunLike.ext
          intro v
          change alpha s₀ t x v = b.val x v
          exact congrArg (fun a ↦ a x v) ht
        have hisometry : Isometry A := by
          apply isometry_iff_dist_eq.mpr
          intro s t
          have he : (A t).val - (A s).val = field s t := by
            apply lp.ext
            funext x
            apply DFunLike.ext
            intro v
            change alpha s₀ t x v - alpha s₀ s x v = alpha s t x v
            have hh := congrArg (fun a ↦ a x v) (halphaAdd s₀ s t)
            change alpha s₀ t x v = alpha s₀ s x v + alpha s t x v at hh
            rw [hh]
            exact add_sub_cancel_left _ _
          change dist (A s).val (A t).val = distance s t
          rw [dist_eq_norm, norm_sub_rev, he, hfieldNorm]
        let e : Sections ≃ᵢ V :=
          { Equiv.ofBijective A ⟨hAinjective, hAsurjective⟩ with
            isometry_toFun := hisometry }
        exact e.completeSpace
      · have : IsEmpty Sections := not_nonempty_iff.mp hne
        infer_instance
    have hfixedOfDecay (hne : Nonempty Sections) (C q : ℝ)
        (hC : 0 < C) (hq : 0 ≤ q) (hq1 : q < 1)
        (hback : ∀ n j, ν ((Φ₁.symm : _ → _)^[n] j) ≤ C * q ^ n * ν j) :
        ∃! s : Sections, Q s = s := by
      let : MetricSpace Sections := sectionMetric
      have : CompleteSpace Sections := hcomplete
      have : Nonempty Sections := hne
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC) hq1
      have hsmall : C * q ^ n < 1 := by
        simpa only [mul_inv_cancel₀ hC.ne'] using (mul_lt_mul_of_pos_left hn hC)
      let K : NNReal := ⟨C * q ^ n, mul_nonneg hC.le (pow_nonneg hq n)⟩
      have hc : ContractingWith K (Q^[n]) := by
        refine ⟨hsmall, lipschitzWith_iff_dist_le_mul.mpr ?_⟩
        intro s t
        exact hdistContract n (C * q ^ n) (hback n) s t
      refine ⟨hc.fixedPoint (Q^[n]), hc.isFixedPt_fixedPoint_iterate, ?_⟩
      intro s hs
      exact hc.fixedPoint_unique ((show Function.IsFixedPt Q s from hs).iterate n)
    have hDecayOfAmbientComparison
        (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
        (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
        (hcompare : ∀ j,
          c * hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤ ν j ∧
          ν j ≤ C * hermitianBoundsNorm h (tangent j).proj (tangent j).snd) :
        ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧ q < 1 ∧
          ∀ n j, ν ((Φ₁.symm : _ → _)^[n] j) ≤ C * q ^ n * ν j := by
      let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      obtain ⟨C₀, q, hC₀, hq, hq1, hdecay⟩ := horiginalDecay
      obtain ⟨c₁, C₁, hc₁, hc₁C₁, hC₁, hcompareOriginal⟩ :=
        OneFormBundle.original_norm_comparison f a h hh
      have hC : 0 < C := hc.trans_le hcC
      have hC₁pos : 0 < C₁ := zero_lt_one.trans_le hC₁
      have hupper (j : NativeLeafwiseJet1 L) :
          ν j ≤ (C / c₁) * originalNorm (tangent j) := by
        have hbound : hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤
            originalNorm (tangent j) / c₁ := by
          apply (le_div_iff₀ hc₁).mpr
          simpa only [mul_comm, originalNorm, hermitianBoundsNorm] using
            (hcompareOriginal (tangent j).proj (tangent j).snd).1
        calc
          ν j ≤ C * hermitianBoundsNorm h (tangent j).proj (tangent j).snd := (hcompare j).2
          _ ≤ C * (originalNorm (tangent j) / c₁) :=
            mul_le_mul_of_nonneg_left hbound hC.le
          _ = (C / c₁) * originalNorm (tangent j) := by ring
      have hreverse (j : NativeLeafwiseJet1 L) :
          originalNorm (tangent j) ≤ (C₁ / c) * ν j := by
        have hbound : hermitianBoundsNorm h (tangent j).proj (tangent j).snd ≤ ν j / c := by
          apply (le_div_iff₀ hc).mpr
          simpa only [mul_comm] using (hcompare j).1
        calc
          originalNorm (tangent j) ≤ C₁ *
              hermitianBoundsNorm h (tangent j).proj (tangent j).snd :=
            (hcompareOriginal (tangent j).proj (tangent j).snd).2
          _ ≤ C₁ * (ν j / c) := mul_le_mul_of_nonneg_left hbound hC₁pos.le
          _ = (C₁ / c) * ν j := by ring
      refine ⟨((C / c₁) * C₀ * (C₁ / c)), q,
        (mul_pos (mul_pos (div_pos hC hc₁) hC₀) (div_pos hC₁pos hc)), hq.le, hq1, ?_⟩
      intro n j
      calc
        ν ((Φ₁.symm : _ → _)^[n] j) ≤
            (C / c₁) * originalNorm (tangent ((Φ₁.symm : _ → _)^[n] j)) := hupper _
        _ ≤ (C / c₁) * (C₀ * q ^ n * originalNorm (tangent j)) :=
          mul_le_mul_of_nonneg_left (hdecay n j) (div_pos hC hc₁).le
        _ ≤ (C / c₁) * (C₀ * q ^ n * ((C₁ / c) * ν j)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hreverse j) (mul_nonneg hC₀.le (pow_nonneg hq.le n)))
            (div_pos hC hc₁).le
        _ = ((C / c₁) * C₀ * (C₁ / c)) * q ^ n * ν j := by ring
    obtain ⟨Cdec, qdec, hCdec, hqdec, hqdec1, hNormDecay⟩ :=
      hDecayOfAmbientComparison hNative hhNative cNative CNative hcNative hcNativeC
        (fun j ↦ hNativeCompare (firstTangent j).val.proj (firstTangent j).val.snd)
    have hfixed (hne : Nonempty Sections) : ∃! s : Sections, Q s = s :=
      hfixedOfDecay hne Cdec qdec hCdec hqdec hqdec1 hNormDecay
    suffices hfixed : ∃! s : Sections,
        Q s = s ∧ ∀ i, ∃ τ : CurveJet1 (L i) → CurveJet2 (L i),
          (∀ v, s.val (nativeLeafwiseJet1Inclusion L i v) =
            nativeLeafwiseJet2Inclusion L i (τ v)) ∧
          ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ τ by
      obtain ⟨s, hs, huniq⟩ := hfixed
      refine ⟨s.val, ⟨s.property.1, s.property.2, hs.2,
        (htransport.2.2 s).mp hs.1⟩, ?_⟩
      intro t ht
      let t' : Sections := ⟨t, ht.1, ht.2.1⟩
      exact congrArg Subtype.val (huniq t'
        ⟨(htransport.2.2 t').mpr ht.2.2.2, ht.2.2.1⟩)
    let Approximates (s : Sections) : Prop :=
      ∀ i (τ : CurveJet1 (L i) → CurveJet2 (L i)),
        (∀ j, s.val (nativeLeafwiseJet1Inclusion L i j) =
          nativeLeafwiseJet2Inclusion L i (τ j)) →
        ∀ (c₀ : LeafChart (L i)) (A : ℂ → ℂ),
        (∀ j, curveJet1Base (L i) j ∈ c₀.1.source →
          (curveJet2Coeff (L i) c₀ (τ j)).2 =
            A (curveJet1Coeff (L i) c₀ j).1 * (curveJet1Coeff (L i) c₀ j).2 ^ 2) →
        ∀ z ∈ c₀.1.target,
          ∃ (V : Set ℂ) (Fₙ : ℕ → ℂ → ℂ) (ρ : ℂ → ℝ) (C q : ℝ),
            IsOpen V ∧ z ∈ V ∧ V ⊆ c₀.1.target ∧ ContinuousOn ρ V ∧
            0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
            (∀ᶠ n in atTop, DifferentiableOn ℂ (Fₙ n) V) ∧
            (∀ᶠ n in atTop, ∀ z ∈ V, ‖Fₙ n z - A z‖ ≤ C * q ^ n * ρ z)
    suffices hgeometry : ∃ s : Sections, Q s = s ∧ Approximates s by
      obtain ⟨s, hs, happ⟩ := hgeometry
      obtain ⟨r, hr, huniq⟩ := hfixed ⟨s⟩
      refine ⟨s, ⟨hs, invariant_jet_leafwise_holomorphic_of_approximation L s.val
        s.property.1 s.property.2 happ⟩, ?_⟩
      intro t ht
      exact (huniq t ht.1).trans (huniq s hs).symm
    obtain ⟨s, hs, _⟩ := hfixed hNonemptySections
    refine ⟨s, hs, ?_⟩
    have leafJetInclusionContinuous {ι : Type u} (L : ι → Type u)
        [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
        [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
        [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
        {d : ℕ} {M : Type u} [TopologicalSpace M]
        [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
        [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
        [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
        {D : RealTangentDistribution (realModel d) M}
        (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n s : ℕ}
        (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
        (hreceiving : ∀ k i (x : L i), (U.leaf i).inclusion x ∈ (c k).source →
          ∃ q : LeafChart (L i), x ∈ q.val.source ∧
            ∀ gamma : CurveParamGerm (L i), curveGermBase (L i) gamma.val ∈ q.val.source →
              gamma.val.map (nativeLeafFlowboxScalar L U (c k) i) = gamma.val.map (q.val : L i → ℂ)) :
        letI := nativeLeafwiseJet1Topology L U c
        ∀ i, Continuous (nativeLeafwiseJet1Inclusion L i) := by
      let := nativeLeafwiseJet1Topology L U c
      intro i
      obtain ⟨A1, A2, _, _, _, _, hM1, hM2, _, _, hbase, _, _, hcharts, _⟩ :=
        (leaf_jet_complex_manifold (L i)).2.2.2.2
      let := A1
      let := A2
      have hincbase : Continuous (fun j : CurveJet1 (L i) ↦
          (U.leaf i).inclusion (curveJet1Base (L i) j)) :=
        (U.leaf i).immersion.contMDiff.continuous.comp hbase
      have hopen (k : Fin n) : IsOpen {j : CurveJet1 (L i) |
          (U.leaf i).inclusion (curveJet1Base (L i) j) ∈ (c k).source} :=
        (c k).open_source.preimage hincbase
      have hcoeff (k : Fin n) : ContinuousOn
          (fun j : CurveJet1 (L i) ↦ nativeLeafwiseJet1Coeff L U (c k) ⟨i, j⟩)
          {j | (U.leaf i).inclusion (curveJet1Base (L i) j) ∈ (c k).source} := by
        intro j hj
        obtain ⟨q, hq, hqg⟩ := hreceiving k i (curveJet1Base (L i) j) hj
        obtain ⟨e1, _, _, _, hs1, _, _, _, he1, _, _, _⟩ := hcharts q
        have hj1 : j ∈ e1.source := by rwa [hs1]
        have hfirst := (c k).continuousAt hj |>.comp (x := j) hincbase.continuousAt
        have hsecond := (e1.continuousAt hj1).snd
        have heq : (fun v : CurveJet1 (L i) ↦ nativeLeafwiseJet1Coeff L U (c k) ⟨i, v⟩) =ᶠ[𝓝 j]
            (fun v ↦ ((c k) ((U.leaf i).inclusion (curveJet1Base (L i) v)), (e1 v).2)) := by
          filter_upwards [e1.open_source.mem_nhds hj1] with v hv
          apply Prod.ext
          · rfl
          · rw [he1 hv]
            change germFirst (v.out.val.map (nativeLeafFlowboxScalar L U (c k) i)) =
              germFirst (v.out.val.map (q.val : L i → ℂ))
            rw [hqg v.out (by rwa [hs1] at hv)]
        exact ((hfirst.prodMk hsecond).congr_of_eventuallyEq heq).continuousWithinAt
      apply continuous_generateFrom_iff.mpr
      rintro O ⟨k, V, hV, rfl⟩
      exact (hcoeff k).isOpen_inter_preimage (hopen k) hV
    have nativeShiftCoefficient {ι : Type u} (L : ι → Type u)
        [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
        [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
        [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]
        {d : ℕ} {M : Type u} [TopologicalSpace M]
        [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
        [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
        [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
        {D : RealTangentDistribution (realModel d) M}
        (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n t : ℕ}
        (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin t → ℝ)))
        (hreceiving : ∀ k i (x : L i), (U.leaf i).inclusion x ∈ (c k).source →
          ∃ q : LeafChart (L i), x ∈ q.val.source ∧
            ∀ gamma : CurveParamGerm (L i), curveGermBase (L i) gamma.val ∈ q.val.source →
              gamma.val.map (nativeLeafFlowboxScalar L U (c k) i) = gamma.val.map (q.val : L i → ℂ)) :
        ∀ k mu j, nativeLeafwiseJet2Base L U j ∈ (c k).source →
          (nativeLeafwiseJet2Coeff L U (c k) (nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ j)).2 =
            (nativeLeafwiseJet2Coeff L U (c k) j).2 - mu*(nativeLeafwiseJet2Coeff L U (c k) j).1.2 := by
      intro k mu j hj
      obtain ⟨q,hq,hm⟩ := hreceiving k j.1 (curveJet2Base (L j.1) j.2) hj
      have hshift := (curve_jet_reparametrization (L j.1)).2.2.1 ⟨1,mu⟩ j.2
      have hq' := hshift.1.symm ▸ hq
      change germSecond ((curveJet2Reparametrize (L j.1) ⟨1,mu⟩ j.2).out.1.map
        (nativeLeafFlowboxScalar L U (c k) j.1)) =
          germSecond (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1)) -
            mu * germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
      rw [hm _ hq',hm _ hq]
      simpa only [curveJet2Coeff,curveGermSecond,curveGermFirst,Units.val_one,one_pow,one_mul] using
        congrArg Prod.snd (hshift.2.2 q hq)
    have hreceiving : ∀ k i (x : L i), (U.leaf i).inclusion x ∈ (c k).source →
        ∃ q : LeafChart (L i), x ∈ q.val.source ∧
          ∀ gamma : CurveParamGerm (L i), curveGermBase (L i) gamma.val ∈ q.val.source →
            gamma.val.map (nativeLeafFlowboxScalar L U (c k) i) = gamma.val.map (q.val : L i → ℂ) := by
      intro k i x hx
      obtain ⟨q,hq,_,_,hm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
        (label k) (branch k) (param k) (htrans k) (hparam k) i x hx
      exact ⟨q,hq,hm⟩
    have hinc := leafJetInclusionContinuous L U c hreceiving
    have hshiftCoeff := nativeShiftCoefficient L U c hreceiving
    have hpbase (v : NativeLeafwiseJet2 L) :
        nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L v) =
          nativeLeafwiseJet2Base L U v :=
      congrArg (U.leaf v.1).inclusion (curve_jet_truncation_base (L v.1) v.2)
    obtain ⟨cores,_,hcompact,hcore,hcoreCover,_,_⟩ := compact_flowbox_slice_buffers c hcover
    have hlocalBound (k : Fin n) : ∃ B : ℝ, 0 ≤ B ∧
        ∀ j (hj : nativeLeafwiseJet1Base L U j ∈ cores k), ∃ mu,
          nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ (s.val j) =
            localSection k ⟨j,hcore k hj⟩ ∧ ‖mu‖ ≤ B*ν j := by
      apply compact_local_jet_shift_bound (c k) (nativeLeafwiseJet1Base L U)
        (nativeLeafwiseJet2Base L U) (E1 k) (E2 k) (hE k).1 (hE k).2.1
        (fun j ↦ by rw [(hE k).2.2.1]; rfl) (hE k).2.2.2.1
        (nativeLeafwiseJetTruncation L) hpbase
        (fun v hv ↦ by
          rw [(hE k).2.2.1,(hE k).2.2.2.2.2]
          exact (native_flowbox_truncation_coeff L U T c label branch param htrans hparam k v hv).2)
        (nativeLeafwiseJet1Scale L)
        (fun w j hj ↦ by
          rw [(hE k).2.2.1]
          exact (native_flowbox_scale_coeff L U T c label branch param htrans hparam k w).1 j hj)
        (fun w ↦ nativeLeafwiseJet2Reparametrize L (.scale w))
        (fun w v hv ↦ by
          rw [(hE k).2.2.2.2.2]
          exact congrArg Prod.snd ((native_flowbox_scale_coeff L U T c label branch param
            htrans hparam k w).2 v hv).2)
        (fun mu ↦ nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩)
        (fun mu v hv ↦ by rw [(hE k).2.2.2.2.2]; exact hshiftCoeff k mu v hv)
        (fun v w hvw ↦ (hshiftUnique v w hvw).exists)
        s.val s.property.1 s.property.2 (localSection k)
        (fun j ↦ ⟨(hlocalCoeff k j).1,by
          rw [(hE k).2.2.2.2.2,(hlocalCoeff k j).2]⟩)
        ν hνcontinuous hνpositive hνscale (cores k) (hcompact k) (hcore k)
    choose Bk hBk hBkbound using hlocalBound
    let B : ℝ := ∑ k, Bk k
    have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ ↦ hBk k)
    have hBbound : ∀ k j (hj : nativeLeafwiseJet1Base L U j ∈ cores k), ∃ mu,
        nativeLeafwiseJet2Reparametrize L ⟨1,mu⟩ (s.val j) =
          localSection k ⟨j,hcore k hj⟩ ∧ ‖mu‖ ≤ B*ν j := by
      intro k j hj
      obtain ⟨mu,hmu,hbound⟩ := hBkbound k j hj
      refine ⟨mu,hmu,hbound.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun l _ ↦ hBk l)
        (Finset.mem_univ k)) (hνpositive j).le
    have hbaseIter (m : ℕ) (j : NativeLeafwiseJet1 L) :
        nativeLeafwiseJet1Base L U ((Φ₁.symm : _ → _)^[m] j) =
          (f.symm : M → M)^[m] (nativeLeafwiseJet1Base L U j) := by
      have hbackbase (j : NativeLeafwiseJet1 L) :
          nativeLeafwiseJet1Base L U (Φ₁.symm j) = f.symm (nativeLeafwiseJet1Base L U j) := by
        have hh := hbase (Φ₁.symm j)
        rw [Φ₁.apply_symm_apply] at hh
        calc
          nativeLeafwiseJet1Base L U (Φ₁.symm j) = f.symm (f (nativeLeafwiseJet1Base L U (Φ₁.symm j))) :=
            (f.left_inv _).symm
          _ = f.symm (nativeLeafwiseJet1Base L U j) := congrArg f.symm hh.symm
      induction m with
      | zero => rfl
      | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [hbackbase, ih]
    have hdisks : ∀ i (c₀ : LeafChart (L i)) z, z ∈ c₀.val.target →
        ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ c₀.val.target ∧
          ∀ᶠ m in atTop, ∃ k, ∀ j, curveJet1Base (L i) j ∈ c₀.val.source →
            (curveJet1Coeff (L i) c₀ j).1 ∈ V →
            nativeLeafwiseJet1Base L U ((Φ₁.symm : _ → _)^[m] ⟨i,j⟩) ∈ cores k := by
      intro i c₀ z hz
      obtain ⟨r,hr,hrc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (c₀.val.open_target.mem_nhds hz)
      refine ⟨Metric.ball z r,Metric.isOpen_ball,Metric.mem_ball_self hr,
        (Metric.ball_subset_closedBall.trans hrc),?_⟩
      have hp := backward_leaf_disk_one_plaque L f a U (fun i ↦ (himm i).1)
        D.permutation.symm G hGi c T label branch (fun k t ↦ (param k t).toHomeomorph)
        htrans hparam cores hcore hcoreCover i c₀ (Metric.closedBall z r)
        (isCompact_closedBall z r) (convex_closedBall z r) hrc z
        (Metric.mem_closedBall_self hr.le)
      filter_upwards [hp] with m hm
      obtain ⟨k,t,hk⟩ := hm
      refine ⟨k,?_⟩
      intro j hj hw
      rw [hbaseIter]
      have hcoord : (curveJet1Coeff (L i) c₀ j).1 = c₀.val (curveJet1Base (L i) j) := rfl
      have he := (hk (curveJet1Coeff (L i) c₀ j).1 (Metric.ball_subset_closedBall hw)).1
      rw [hcoord,c₀.val.left_inv hj] at he
      exact he
    exact transported_jet_holomorphic_approximation L Φ₁ Φ₂ htrunc
      (fun mu j ↦ hscale2 1 mu j) D.permutation.symm G hbackward
      ν hνcontinuous hinc Cdec qdec hCdec.le hqdec hqdec1 hNormDecay
      (nativeLeafwiseJet1Base L U) (fun k ↦ (c k).source) cores hcore
      s.val s.property.1 ((htransport.2.2 s).mp hs)
      localSection (fun k j ↦ (hlocalCoeff k j).1) hlocalHolomorphic B hB hBbound hdisks


end HolomorphicAnosov.Ghys
