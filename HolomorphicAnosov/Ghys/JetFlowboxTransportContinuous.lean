import HolomorphicAnosov.Ghys.CurveScalarGermChainRule
import HolomorphicAnosov.Ghys.LeafFamilyJet
import HolomorphicAnosov.Ghys.JetDynamicsTotalMaps
import HolomorphicAnosov.Ghys.CurveJetPostcomposeScalar
import HolomorphicAnosov.Ghys.JetFlowboxTransportRegularity

/-! Continuity of flowbox-generated jet transports. Source: Ghys p.591–592. -/

namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
universe u v w z r

/-- Postcomposition is continuous for the actual flowbox-generated jet topology. Source: Ghys p.591–592. -/
theorem leafFamilyJetEquiv_continuous
    {M : Type u} [TopologicalSpace M] {Q : Type v} {L : Q → Type v}
    [∀ q, TopologicalSpace (L q)] [∀ q, ChartedSpace ℂ (L q)]
    [∀ q, IsManifold 𝓘(ℂ) ∞ (L q)]
    {T : Type z} [TopologicalSpace T] {ι : Type r}
    (inclusion : ∀ q, L q → M) (c : ι → OpenPartialHomeomorph M (ℂ × T))
    (hcover : ∀ x, ∃ k, x ∈ (c k).source)
    (σ : Q ≃ Q) (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (f : M → M) (hf : Continuous f)
    (hF : ∀ q x, inclusion (σ q) (F q x) = f (inclusion q x))
    (hlocal : ∀ k q x, inclusion q x ∈ (c k).source →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun y ↦ (c k (inclusion q y)).1) x ∧
      ∀ᶠ y in 𝓝 x, inclusion q y =
        (c k).symm ((c k (inclusion q y)).1, (c k (inclusion q x)).2))
    (hslice : ∀ k l p, p ∈ (c k).target → f ((c k).symm p) ∈ (c l).source →
      ContDiffAt ℂ ∞ (fun z ↦ (c l (f ((c k).symm (z, p.2)))).1) p.1) :
    @Continuous (LeafFamilyJet1 L) (LeafFamilyJet1 L)
      (leafFamilyJet1Topology L inclusion (range c))
      (leafFamilyJet1Topology L inclusion (range c)) (familyJet1Equiv σ F) ∧
    @Continuous (LeafFamilyJet2 L) (LeafFamilyJet2 L)
      (leafFamilyJet2Topology L inclusion (range c))
      (leafFamilyJet2Topology L inclusion (range c)) (familyJet2Equiv σ F) := by
  classical
  let E1 := familyJet1Equiv σ F
  let E2 := familyJet2Equiv σ F
  let e1 := fun q ↦ (curve_postcompose_jet_equivalences (F q)).choose
  let e2 := fun q ↦ (curve_postcompose_jet_equivalences (F q)).choose_spec.choose
  have he1 q := (curve_postcompose_jet_equivalences (F q)).choose_spec.choose_spec.1
  have he2 q := (curve_postcompose_jet_equivalences (F q)).choose_spec.choose_spec.2
  have hb1 (j : LeafFamilyJet1 L) :
      leafFamilyJet1Base L inclusion (E1 j) = f (leafFamilyJet1Base L inclusion j) := by
    rcases j with ⟨q,j⟩
    change inclusion (σ q) (curveJet1Base _ (e1 q j)) = _
    rw [(curveJet1_postcompose_scalar (F q) (e1 q) (he1 q) j
      (fun _ ↦ 0) contMDiffAt_const).1]
    exact hF q _
  have hb2 (j : LeafFamilyJet2 L) :
      leafFamilyJet2Base L inclusion (E2 j) = f (leafFamilyJet2Base L inclusion j) := by
    rcases j with ⟨q,j⟩
    change inclusion (σ q) (curveJet2Base _ (e2 q j)) = _
    rw [(curveJet2_postcompose_scalar (F q) (e2 q) (he2 q) j
      (fun _ ↦ 0) contMDiffAt_const).1]
    exact hF q _
  have formula1 (k l : ι) (j : LeafFamilyJet1 L)
      (hj : leafFamilyJet1Base L inclusion j ∈ (c k).source)
      (hfj : f (leafFamilyJet1Base L inclusion j) ∈ (c l).source) :
      leafFamilyJet1Coeff L inclusion (c l) (E1 j) =
        (c l (f (leafFamilyJet1Base L inclusion j)),
          deriv (fun z ↦ (c l (f ((c k).symm
            (z, (c k (leafFamilyJet1Base L inclusion j)).2)))).1)
            (c k (leafFamilyJet1Base L inclusion j)).1 *
              (leafFamilyJet1Coeff L inclusion (c k) j).2) := by
    rcases j with ⟨q,j⟩
    let x := curveJet1Base (L q) j
    let ψ := fun y ↦ (c k (inclusion q y)).1
    let φ := fun y ↦ (c l (inclusion (σ q) y)).1
    let H := fun z ↦ (c l (f ((c k).symm (z, (c k (inclusion q x)).2)))).1
    have hloc := hlocal k q x hj
    have hφ := (hlocal l (σ q) (F q x) (by rw [hF]; exact hfj)).1
    have hpost := (curveJet1_postcompose_scalar (F q) (e1 q) (he1 q) j φ hφ).2
    have hH : ContDiffAt ℂ 2 H (ψ x) :=
      (hslice k l (c k (inclusion q x)) ((c k).map_source hj)
        (by rw [(c k).left_inv (show inclusion q x ∈ (c k).source from hj)]; exact hfj)).of_le (by simp)
    have hevent : (φ ∘ F q) =ᶠ[𝓝 x] H ∘ ψ := by
      filter_upwards [hloc.2] with y hy
      dsimp [φ, H, ψ, Function.comp_def]
      rw [hF, ← hy]
    have hchain := (curveParamGerm_scalar_chain j.out ψ H hloc.1 hH).1
    rw [← curveParamGerm_map_congr j.out _ _ hevent] at hchain
    apply Prod.ext
    · exact congrArg (c l) (hb1 ⟨q,j⟩)
    · exact hpost.trans hchain
  have formula2 (k l : ι) (j : LeafFamilyJet2 L)
      (hj : leafFamilyJet2Base L inclusion j ∈ (c k).source)
      (hfj : f (leafFamilyJet2Base L inclusion j) ∈ (c l).source) :
      leafFamilyJet2Coeff L inclusion (c l) (E2 j) =
        ((c l (f (leafFamilyJet2Base L inclusion j)),
          deriv (fun z ↦ (c l (f ((c k).symm
            (z, (c k (leafFamilyJet2Base L inclusion j)).2)))).1)
            (c k (leafFamilyJet2Base L inclusion j)).1 *
              (leafFamilyJet2Coeff L inclusion (c k) j).1.2),
          deriv (fun z ↦ (c l (f ((c k).symm
            (z, (c k (leafFamilyJet2Base L inclusion j)).2)))).1)
            (c k (leafFamilyJet2Base L inclusion j)).1 *
              (leafFamilyJet2Coeff L inclusion (c k) j).2 +
          (iteratedDeriv 2 (fun z ↦ (c l (f ((c k).symm
            (z, (c k (leafFamilyJet2Base L inclusion j)).2)))).1)
            (c k (leafFamilyJet2Base L inclusion j)).1 / 2) *
              (leafFamilyJet2Coeff L inclusion (c k) j).1.2 ^ 2) := by
    rcases j with ⟨q,j⟩
    let x := curveJet2Base (L q) j
    let ψ := fun y ↦ (c k (inclusion q y)).1
    let φ := fun y ↦ (c l (inclusion (σ q) y)).1
    let H := fun z ↦ (c l (f ((c k).symm (z, (c k (inclusion q x)).2)))).1
    have hloc := hlocal k q x hj
    have hφ := (hlocal l (σ q) (F q x) (by rw [hF]; exact hfj)).1
    have hpost := (curveJet2_postcompose_scalar (F q) (e2 q) (he2 q) j φ hφ).2
    have hH : ContDiffAt ℂ 2 H (ψ x) :=
      (hslice k l (c k (inclusion q x)) ((c k).map_source hj)
        (by rw [(c k).left_inv (show inclusion q x ∈ (c k).source from hj)]; exact hfj)).of_le (by simp)
    have hevent : (φ ∘ F q) =ᶠ[𝓝 x] H ∘ ψ := by
      filter_upwards [hloc.2] with y hy
      dsimp [φ, H, ψ, Function.comp_def]
      rw [hF, ← hy]
    have hchain := curveParamGerm_scalar_chain j.out ψ H hloc.1 hH
    rw [← curveParamGerm_map_congr j.out _ _ hevent] at hchain
    exact Prod.ext (Prod.ext (congrArg (c l) (hb2 ⟨q,j⟩)) (hpost.1.trans hchain.1))
      (hpost.2.trans hchain.2)
  have hder k l := jetFlowboxTransport_derivatives (c k) (c l) f hf
    (fun p hp ↦ hslice k l p hp.1 hp.2)
  let := leafFamilyJet1Topology L inclusion (range c)
  let := leafFamilyJet2Topology L inclusion (range c)
  have h1 : ∀ k, IsOpen {j | leafFamilyJet1Base L inclusion j ∈ (c k).source} ∧
      ContinuousOn (leafFamilyJet1Coeff L inclusion (c k))
        {j | leafFamilyJet1Base L inclusion j ∈ (c k).source} := by
    intro k
    have hopen : IsOpen {j | leafFamilyJet1Base L inclusion j ∈ (c k).source} :=
      isOpen_generateFrom_of_mem ⟨c k, mem_range_self k, Set.univ, isOpen_univ,
        by ext j; simp⟩
    refine ⟨hopen, (continuousOn_open_iff hopen).mpr ?_⟩
    intro O hO
    exact isOpen_generateFrom_of_mem ⟨c k, mem_range_self k, O, hO, rfl⟩
  have h2 : ∀ k, IsOpen {j | leafFamilyJet2Base L inclusion j ∈ (c k).source} ∧
      ContinuousOn (leafFamilyJet2Coeff L inclusion (c k))
        {j | leafFamilyJet2Base L inclusion j ∈ (c k).source} := by
    intro k
    have hopen : IsOpen {j | leafFamilyJet2Base L inclusion j ∈ (c k).source} :=
      isOpen_generateFrom_of_mem ⟨c k, mem_range_self k, Set.univ, isOpen_univ,
        by ext j; simp⟩
    refine ⟨hopen, (continuousOn_open_iff hopen).mpr ?_⟩
    intro O hO
    exact isOpen_generateFrom_of_mem ⟨c k, mem_range_self k, O, hO, rfl⟩
  have hbase1 : Continuous (leafFamilyJet1Base L inclusion) := by
    rw [continuous_iff_continuousAt]
    intro j
    obtain ⟨k,hj⟩ := hcover (leafFamilyJet1Base L inclusion j)
    have hc := ((h1 k).2.continuousAt ((h1 k).1.mem_nhds hj)).fst
    apply (((c k).continuousAt_symm ((c k).map_source hj)).comp (x := j) hc).congr
    filter_upwards [(h1 k).1.mem_nhds hj] with j' hj'
    exact (c k).left_inv hj'
  have hbase2 : Continuous (leafFamilyJet2Base L inclusion) := by
    rw [continuous_iff_continuousAt]
    intro j
    obtain ⟨k,hj⟩ := hcover (leafFamilyJet2Base L inclusion j)
    have hc := ((h2 k).2.continuousAt ((h2 k).1.mem_nhds hj)).fst.fst
    apply (((c k).continuousAt_symm ((c k).map_source hj)).comp (x := j) hc).congr
    filter_upwards [(h2 k).1.mem_nhds hj] with j' hj'
    exact (c k).left_inv hj'
  have hd1 l : IsOpen {j | f (leafFamilyJet1Base L inclusion j) ∈ (c l).source} :=
    (c l).open_source.preimage (hf.comp hbase1)
  have hd2 l : IsOpen {j | f (leafFamilyJet2Base L inclusion j) ∈ (c l).source} :=
    (c l).open_source.preimage (hf.comp hbase2)
  have hcont1 l : ContinuousOn (fun j ↦ leafFamilyJet1Coeff L inclusion (c l) (E1 j))
      {j | f (leafFamilyJet1Base L inclusion j) ∈ (c l).source} := by
    intro j hj
    obtain ⟨k,hk⟩ := hcover (leafFamilyJet1Base L inclusion j)
    have hc := (h1 k).2.continuousAt ((h1 k).1.mem_nhds hk)
    have hp : c k (leafFamilyJet1Base L inclusion j) ∈
        (c k).target ∩ (f ∘ (c k).symm) ⁻¹' (c l).source :=
      ⟨(c k).map_source hk, by change f ((c k).symm (c k (leafFamilyJet1Base L inclusion j))) ∈ (c l).source; rw [(c k).left_inv hk]; exact hj⟩
    have h0 := ((hder k l).2.1.continuousAt ((hder k l).1.mem_nhds hp)).comp (x := j) hc.fst
    have ha := ((hder k l).2.2.1.continuousAt ((hder k l).1.mem_nhds hp)).comp (x := j) hc.fst
    apply ContinuousAt.continuousWithinAt
    apply (h0.prodMk (ha.mul hc.snd)).congr
    filter_upwards [((h1 k).1.inter (hd1 l)).mem_nhds ⟨hk,hj⟩]
      with j' hj'
    simpa only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply, leafFamilyJet1Coeff, (c k).left_inv hj'.1]
      using (formula1 k l j' hj'.1 hj'.2).symm
  have hcont2 l : ContinuousOn (fun j ↦ leafFamilyJet2Coeff L inclusion (c l) (E2 j))
      {j | f (leafFamilyJet2Base L inclusion j) ∈ (c l).source} := by
    intro j hj
    obtain ⟨k,hk⟩ := hcover (leafFamilyJet2Base L inclusion j)
    have hc := (h2 k).2.continuousAt ((h2 k).1.mem_nhds hk)
    have hp : c k (leafFamilyJet2Base L inclusion j) ∈
        (c k).target ∩ (f ∘ (c k).symm) ⁻¹' (c l).source :=
      ⟨(c k).map_source hk, by change f ((c k).symm (c k (leafFamilyJet2Base L inclusion j))) ∈ (c l).source; rw [(c k).left_inv hk]; exact hj⟩
    have h0 := ((hder k l).2.1.continuousAt ((hder k l).1.mem_nhds hp)).comp (x := j) hc.fst.fst
    have ha := ((hder k l).2.2.1.continuousAt ((hder k l).1.mem_nhds hp)).comp (x := j) hc.fst.fst
    have hb := ((hder k l).2.2.2.continuousAt ((hder k l).1.mem_nhds hp)).comp (x := j) hc.fst.fst
    apply ContinuousAt.continuousWithinAt
    apply ((h0.prodMk (ha.mul hc.fst.snd)).prodMk
      ((ha.mul hc.snd).add ((hb.div_const 2).mul (hc.fst.snd.pow 2)))).congr
    filter_upwards [((h2 k).1.inter (hd2 l)).mem_nhds ⟨hk,hj⟩]
      with j' hj'
    simpa only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply, leafFamilyJet2Coeff, (c k).left_inv hj'.1]
      using (formula2 k l j' hj'.1 hj'.2).symm
  constructor
  · apply continuous_generateFrom_iff.mpr
    rintro S ⟨_,⟨l,rfl⟩,O,hO,rfl⟩
    have hopen := (hcont1 l).isOpen_inter_preimage (hd1 l) hO
    convert hopen using 1
    ext j
    change (leafFamilyJet1Base L inclusion (E1 j) ∈ (c l).source ∧
      leafFamilyJet1Coeff L inclusion (c l) (E1 j) ∈ O) ↔ _
    rw [hb1]
    rfl
  · apply continuous_generateFrom_iff.mpr
    rintro S ⟨_,⟨l,rfl⟩,O,hO,rfl⟩
    have hopen := (hcont2 l).isOpen_inter_preimage (hd2 l) hO
    convert hopen using 1
    ext j
    change (leafFamilyJet2Base L inclusion (E2 j) ∈ (c l).source ∧
      leafFamilyJet2Coeff L inclusion (c l) (E2 j) ∈ O) ↔ _
    rw [hb2]
    rfl

end HolomorphicAnosov.Ghys
