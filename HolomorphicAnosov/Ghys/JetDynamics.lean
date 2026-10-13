import HolomorphicAnosov.Ghys.JetFlowboxTransportRegularity
import HolomorphicAnosov.Ghys.JetFlowboxScalarLocal
import HolomorphicAnosov.Ghys.JetFlowboxTransportContinuous
import HolomorphicAnosov.Ghys.LeafFamilyJet
import HolomorphicAnosov.Geometry.HolomorphicCurveLift
import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.CurvePostcomposeReparametrize
import HolomorphicAnosov.Ghys.JetDynamicsTotalMapLaws
import HolomorphicAnosov.Ghys.JetDynamicsTransportIntertwining
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import HolomorphicAnosov.Ghys.JetGermQuotient
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.JetDynamicsChartWitness
import HolomorphicAnosov.Ghys.JetDynamicsTotalMaps
import HolomorphicAnosov.Ghys.JetDynamicsLeafwiseDiffeomorphSmoothness
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Ghys.CurveJetReparametrization
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import Mathlib.Geometry.Manifold.Diffeomorph

/-! This file defines the induced dynamics on the original leafwise curve-jet spaces of a holomorphic Anosov map. (Ghys, §3) -/

noncomputable section

namespace HolomorphicAnosov.Ghys

open Filter Set TopologicalSpace

set_option autoImplicit false
open scoped _root_.HolomorphicAnosov.Topology Manifold ContDiff



section OriginalDynamics

universe u

attribute [local instance] complex_isManifold_real

/-- A compact holomorphic Anosov map induces biholomorphic dynamics on its original transverse curve-jet spaces by postcomposition with the leaf restrictions. (Ghys, §3) -/
theorem jet_dynamics
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ (Q : Type u) (L : Q → Type u) (top : ∀ q, TopologicalSpace (L q)),
    letI := top
    ∃ (realChart : ∀ q, ChartedSpace (Fin 2 → ℝ) (L q)),
    letI := realChart
    ∃ (realSmooth : ∀ q, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L q)),
    letI := realSmooth
    ∃ (U : HPS.LeafPartition a.splitting.unstable.toDistribution Q L (fun _ ↦ 2))
      (complexChart : ∀ q, ChartedSpace ℂ (L q)),
    letI := complexChart
    ∃ (complexSmooth : ∀ q, IsManifold 𝓘(ℂ) ∞ (L q)),
    letI := complexSmooth
    let inclusion := fun q ↦ (U.leaf q).inclusion
    (∀ q, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (inclusion q) ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (inclusion q) z)) ∧
    (∃ m : MetricSpace M,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      ∀ q (x : L q) y, (∃ z : L q, inclusion q z = y) ↔
        @ForwardAsymptotic M m (f.symm : M → M) (inclusion q x) y) ∧
    ∃ (D : HPS.LeafDynamicalInvariance U f.toReal)
      (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (D.permutation q)) ∞)
      (G : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (D.permutation.symm q)) ∞),
    (∀ q z, F q z = D.transport q z) ∧
    (∀ q z, inclusion (D.permutation q) (F q z) = f (inclusion q z)) ∧
    (∀ q z, inclusion (D.permutation.symm q) (G q z) = f.symm (inclusion q z)) ∧
    ∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
      (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      (label : ∀ i, T i → Q) (branch : ∀ i t, Opens (L (label i t)))
      (parametrization : ∀ (i : Fin n) (t : T i),
        Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
          (⟨{z | (z, t.val) ∈ (c i).target},
            (c i).open_target.preimage
              (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ ↦ t.val)))⟩ : Opens ℂ)
          (branch i t) ∞),
    (∀ x : M, ∃ i, x ∈ (c i).source) ∧
    (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
    (∀ i t z, (c i).symm (z.val, t.val) =
      inclusion (label i t) ((parametrization i t z).val)) ∧
    letI := leafFamilyJet1Topology L inclusion (range c)
    letI := leafFamilyJet2Topology L inclusion (range c)
    ∃ (Φ₁ : LeafFamilyJet1 L ≃ₜ LeafFamilyJet1 L)
      (Φ₂ : LeafFamilyJet2 L ≃ₜ LeafFamilyJet2 L),
    (∀ q (γ : CurveParamGerm (L q)),
      ∃ δ : CurveParamGerm (L (D.permutation q)),
        δ.val = γ.val.map (F q : L q → L (D.permutation q)) ∧
        Φ₁ ⟨q, curveJet1Class (L q) γ⟩ =
          ⟨D.permutation q, curveJet1Class (L (D.permutation q)) δ⟩ ∧
        Φ₂ ⟨q, curveJet2Class (L q) γ⟩ =
          ⟨D.permutation q, curveJet2Class (L (D.permutation q)) δ⟩) ∧
    (∀ q (γ : CurveParamGerm (L q)),
      ∃ δ : CurveParamGerm (L (D.permutation.symm q)),
        δ.val = γ.val.map (G q : L q → L (D.permutation.symm q)) ∧
        Φ₁.symm ⟨q, curveJet1Class (L q) γ⟩ =
          ⟨D.permutation.symm q, curveJet1Class (L (D.permutation.symm q)) δ⟩ ∧
        Φ₂.symm ⟨q, curveJet2Class (L q) γ⟩ =
          ⟨D.permutation.symm q, curveJet2Class (L (D.permutation.symm q)) δ⟩) ∧
    (∀ j, leafFamilyJet1Base L inclusion (Φ₁ j) =
      f (leafFamilyJet1Base L inclusion j)) ∧
    (∀ j, leafFamilyJetTruncation L (Φ₂ j) = Φ₁ (leafFamilyJetTruncation L j)) ∧
    (∀ (omega : ℂˣ) (μ : ℂ) j,
      Φ₁ (leafFamilyJet1Source L omega μ j) = leafFamilyJet1Source L omega μ (Φ₁ j)) ∧
    (∀ (omega : ℂˣ) (μ : ℂ) j,
      Φ₂ (leafFamilyJet2Source L omega μ j) = leafFamilyJet2Source L omega μ (Φ₂ j)) ∧
    ∃ (jetChart1 : ∀ q, ChartedSpace (ℂ × ℂ) (CurveJet1 (L q)))
      (jetChart2 : ∀ q, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L q))),
    let := jetChart1
    let := jetChart2
    (∀ q, IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L q)) ∧
      IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L q))) ∧
    (∀ q (b : LeafChart (L q)),
      ∃ (e₁ : OpenPartialHomeomorph (CurveJet1 (L q)) (ℂ × ℂ))
        (e₂ : OpenPartialHomeomorph (CurveJet2 (L q)) ((ℂ × ℂ) × ℂ)),
        e₁ ∈ atlas (ℂ × ℂ) (CurveJet1 (L q)) ∧
        e₂ ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 (L q)) ∧
        e₁.source = curveJet1Base (L q) ⁻¹' b.val.source ∧
        e₂.source = curveJet2Base (L q) ⁻¹' b.val.source ∧
        e₁.target = curveJet1Target (L q) b ∧ e₂.target = curveJet2Target (L q) b ∧
        EqOn e₁ (curveJet1Coeff (L q) b) e₁.source ∧
        EqOn e₂ (curveJet2Coeff (L q) b) e₂.source) ∧
    (∀ q, ∃ (e₁ : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
        (CurveJet1 (L q)) (CurveJet1 (L (D.permutation q))) ∞)
      (e₂ : Diffeomorph 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ)
        (CurveJet2 (L q)) (CurveJet2 (L (D.permutation q))) ∞),
      (∀ j, Φ₁ ⟨q, j⟩ = ⟨D.permutation q, e₁ j⟩) ∧
      (∀ j, Φ₂ ⟨q, j⟩ = ⟨D.permutation q, e₂ j⟩)) := by
  classical
  obtain ⟨ιs, Q, Ls, L, topS, top, hflow⟩ :=
    ActualInvariantSectionFlowboxCoverG5.actual_invariant_section_flowbox_cover f a hRank
  let := topS
  let := top
  obtain ⟨chartS, realChart, hflow⟩ := hflow
  let := chartS
  let := realChart
  obtain ⟨smoothS, realSmooth, hflow⟩ := hflow
  let := smoothS
  let := realSmooth
  obtain ⟨S, U, complexChart, complexSmooth, hinclusion, hmetric,
    hinvariantS, hinvariantU, hlamination, hboxes, hproduct⟩ := hflow
  let := complexChart
  let := complexSmooth
  obtain ⟨D⟩ := hinvariantU
  refine ⟨Q, L, top, realChart, realSmooth, U, complexChart, complexSmooth,
    hinclusion, ?_, ?_⟩
  · obtain ⟨m, htop, _, hu⟩ := hmetric
    exact ⟨m, htop, hu⟩
  · let inclusion := fun q ↦ (U.leaf q).inclusion
    have hforward (q : Q) :
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (D.transport q) := by
      apply holomorphic_curve_lift (inclusion (D.permutation q))
        (hinclusion (D.permutation q)).1 (hinclusion (D.permutation q)).2
        (D.transport q) (D.transport q).continuous
      have heq : inclusion (D.permutation q) ∘ D.transport q = f ∘ inclusion q := by
        funext z
        exact D.intertwining q z
      rw [heq]
      exact f.contMDiff.comp (hinclusion q).1
    have hbackward (q : Q) :
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (D.transport q).symm := by
      apply holomorphic_curve_lift (inclusion q) (hinclusion q).1 (hinclusion q).2
        (D.transport q).symm (D.transport q).symm.continuous
      have heq : inclusion q ∘ (D.transport q).symm =
          f.symm ∘ inclusion (D.permutation q) := by
        funext z
        apply f.injective
        change f (inclusion q ((D.transport q).symm z)) =
          f (f.symm (inclusion (D.permutation q) z))
        rw [f.apply_symm_apply]
        have he := D.intertwining q ((D.transport q).symm z)
        change inclusion (D.permutation q) (D.transport q ((D.transport q).symm z)) =
          f (inclusion q ((D.transport q).symm z)) at he
        simpa only [Diffeomorph.apply_symm_apply] using he.symm
      rw [heq]
      exact f.symm.contMDiff.comp (hinclusion (D.permutation q)).1
    let F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (D.permutation q)) ∞ :=
      fun q ↦ { toEquiv := (D.transport q).toEquiv
                contMDiff_toFun := hforward q
                contMDiff_invFun := hbackward q }
    have hinverse : ∀ q, ∃ Gq :
        Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (D.permutation.symm q)) ∞,
        ∀ z, inclusion (D.permutation.symm q) (Gq z) = f.symm (inclusion q z) := by
      intro q
      obtain ⟨r, rfl⟩ := D.permutation.surjective q
      rw [D.permutation.symm_apply_apply]
      refine ⟨(F r).symm, ?_⟩
      intro z
      apply f.injective
      change f (inclusion r ((D.transport r).symm z)) =
        f (f.symm (inclusion (D.permutation r) z))
      rw [f.apply_symm_apply]
      have he := D.intertwining r ((D.transport r).symm z)
      change inclusion (D.permutation r) (D.transport r ((D.transport r).symm z)) =
        f (inclusion r ((D.transport r).symm z)) at he
      simpa only [Diffeomorph.apply_symm_apply] using he.symm
    choose G hG using hinverse
    refine ⟨D, F, G, (fun _ _ ↦ rfl), D.intertwining, hG, ?_⟩
    obtain ⟨n, T, c, label, branch, parametrization, hcover, htarget, hslice,
      hopen, hcontinuous, hfirst, hsecond, hlocal⟩ := hboxes
    refine ⟨n, T, c, label, branch, parametrization, hcover, htarget, hslice, ?_⟩
    let : ∀ q, T2Space (L q) := fun q ↦ (U.leaf q).hausdorff
    let : ∀ q, SecondCountableTopology (L q) := fun q ↦ (U.leaf q).countable
    let : TopologicalSpace (LeafFamilyJet1 L) :=
      leafFamilyJet1Topology L inclusion (range c)
    let : TopologicalSpace (LeafFamilyJet2 L) :=
      leafFamilyJet2Topology L inclusion (range c)
    have hinj : Function.Injective (fun p : (q : Q) × L q ↦ inclusion p.1 p.2) := by
      rintro ⟨q, x⟩ ⟨r, y⟩ h
      have hqr : q = r := U.disjoint q r x y h
      subst r
      exact congrArg (Sigma.mk q) ((U.leaf q).injective h)
    have hFG : ∀ q z,
        (⟨D.permutation (D.permutation.symm q),
          F (D.permutation.symm q) (G q z)⟩ : (q : Q) × L q) = ⟨q, z⟩ := by
      intro q z
      apply hinj
      change inclusion (D.permutation (D.permutation.symm q))
        (F (D.permutation.symm q) (G q z)) = inclusion q z
      rw [show inclusion (D.permutation (D.permutation.symm q))
        (F (D.permutation.symm q) (G q z)) =
          f (inclusion (D.permutation.symm q) (G q z)) from
            D.intertwining (D.permutation.symm q) (G q z), hG, f.apply_symm_apply]
    have hcoords (k : Fin n) (q : Q) (x : L q)
        (hx : inclusion q x ∈ (c k).source) :=
      jetFlowboxScalar_local inclusion hinj (c k) (T k) (label k) (branch k)
        (parametrization k) (htarget k) (hslice k) q x hx
    have hforward_cont := leafFamilyJetEquiv_continuous inclusion c hcover
      D.permutation F f f.continuous D.intertwining hcoords
      (fun k l p hp hfp ↦ jetFlowboxTransport_slice inclusion D.permutation F f
        D.intertwining (c k) (c l) (T k) (label k) (branch k) (parametrization k)
        (htarget k) (hslice k) (fun q x hx ↦ (hcoords l q x hx).1) p hp hfp)
    have hbackward_cont := leafFamilyJetEquiv_continuous inclusion c hcover
      D.permutation.symm G f.symm f.symm.continuous hG hcoords
      (fun k l p hp hfp ↦ jetFlowboxTransport_slice inclusion D.permutation.symm G f.symm
        hG (c k) (c l) (T k) (label k) (branch k) (parametrization k)
        (htarget k) (hslice k) (fun q x hx ↦ (hcoords l q x hx).1) p hp hfp)
    have hsymm := familyJetEquiv_symm_of_inverse D.permutation F G hFG
    have htotal := jet_dynamics_total_maps
      (σ := D.permutation) F G f inclusion D.intertwining hFG
      hforward_cont.1 (by rw [hsymm.1]; exact hbackward_cont.1)
      hforward_cont.2 (by rw [hsymm.2]; exact hbackward_cont.2)
      (leafFamilyJet1Base L inclusion) (leafFamilyJet2Base L inclusion)
      (leafFamilyJetTruncation L) (leafFamilyJet1Source L) (leafFamilyJet2Source L)
      (by intro j; rfl) (by intro j; rfl) (by intro j; rfl)
      (by intro omega μ j; rfl) (by intro omega μ j; rfl)
    rcases htotal with ⟨Φ₁, Φ₂, hforward', hbackward', hbase', htrunc',
      hsource₁', hsource₂'⟩
    let jetChart1 : ∀ q, ChartedSpace (ℂ × ℂ) (CurveJet1 (L q)) :=
      fun q ↦ (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose
    let jetChart2 : ∀ q, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L q)) :=
      fun q ↦ (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose
    let := jetChart1
    let := jetChart2
    have hjetManifold :
        (∀ q, IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L q)) ∧
          IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L q))) := by
      intro q
      have h := (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose_spec
      rcases h with ⟨_, _, _, _, hm1, hm2, _, _, _, _, _, _, _, _⟩
      exact ⟨hm1, hm2⟩
    let : ∀ q, IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L q)) :=
      fun q ↦ (hjetManifold q).1
    let : ∀ q, IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L q)) :=
      fun q ↦ (hjetManifold q).2
    have hjetCharts :
        (∀ q (b : LeafChart (L q)),
          ∃ (e₁ : OpenPartialHomeomorph (CurveJet1 (L q)) (ℂ × ℂ))
            (e₂ : OpenPartialHomeomorph (CurveJet2 (L q)) ((ℂ × ℂ) × ℂ)),
            e₁ ∈ atlas (ℂ × ℂ) (CurveJet1 (L q)) ∧
            e₂ ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 (L q)) ∧
            e₁.source = curveJet1Base (L q) ⁻¹' b.val.source ∧
            e₂.source = curveJet2Base (L q) ⁻¹' b.val.source ∧
            e₁.target = curveJet1Target (L q) b ∧
            e₂.target = curveJet2Target (L q) b ∧
            EqOn e₁ (curveJet1Coeff (L q) b) e₁.source ∧
            EqOn e₂ (curveJet2Coeff (L q) b) e₂.source) := by
      intro q b
      have h := (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose_spec
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hcharts, _, _⟩
      rcases hcharts b with
        ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, ht₁, ht₂, hc₁, hc₂, _, _, _, _⟩
      exact ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, ht₁, ht₂, hc₁, hc₂⟩
    have hAtlases : ∀ q, CurveJetCoefficientAtlases (L q)
        (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 (L q)))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L q))) := by
      intro q
      have h := (leaf_jet_complex_manifold (L := L q)).2.2.2.2.choose_spec.choose_spec
      rcases h with ⟨_, _, _, _, hm1, hm2, _, _, _, _, _, hcharts, hall₁, hall₂⟩
      exact ⟨hm1, hm2, hcharts, hall₁, hall₂⟩
    have hleaf : ∀ q, ∃ (e₁ : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
        (CurveJet1 (L q)) (CurveJet1 (L (D.permutation q))) ∞)
      (e₂ : Diffeomorph 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ)
        (CurveJet2 (L q)) (CurveJet2 (L (D.permutation q))) ∞),
      (∀ j, Φ₁ ⟨q, j⟩ = ⟨D.permutation q, e₁ j⟩) ∧
      (∀ j, Φ₂ ⟨q, j⟩ = ⟨D.permutation q, e₂ j⟩) := by
      intro q
      obtain ⟨e₁, e₂, he₁, he₂⟩ := curve_postcompose_jet_diffeomorph_smooth
        ⟨hAtlases q, hAtlases (D.permutation q)⟩ (F q)
      refine ⟨e₁, e₂, ?_, ?_⟩
      · intro j
        refine Quotient.inductionOn j ?_
        intro γ
        obtain ⟨δ, hδ, h₁, h₂⟩ := hforward' q γ
        have hδ' : δ = curveParamGermPostcompose (F q) γ := Subtype.ext hδ
        change Φ₁ ⟨q, curveJet1Class (L q) γ⟩ =
          ⟨D.permutation q, e₁ (curveJet1Class (L q) γ)⟩
        rw [he₁ γ, ← hδ']
        exact h₁
      · intro j
        refine Quotient.inductionOn j ?_
        intro γ
        obtain ⟨δ, hδ, h₁, h₂⟩ := hforward' q γ
        have hδ' : δ = curveParamGermPostcompose (F q) γ := Subtype.ext hδ
        change Φ₂ ⟨q, curveJet2Class (L q) γ⟩ =
          ⟨D.permutation q, e₂ (curveJet2Class (L q) γ)⟩
        rw [he₂ γ, ← hδ']
        exact h₂
    refine ⟨Φ₁, Φ₂, hforward', hbackward', hbase', htrunc', hsource₁', hsource₂',
      jetChart1, jetChart2, hjetManifold, hjetCharts, ?_⟩
    exact hleaf

end OriginalDynamics

end HolomorphicAnosov.Ghys


