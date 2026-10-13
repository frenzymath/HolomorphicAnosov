import HolomorphicAnosov.Ghys.NativeFlowboxJetChartsG13
import HolomorphicAnosov.Ghys.CurveJetLocalZeroSection

/-! Affine-germ homogeneous local sections of the native two-jet truncation. -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter TopologicalSpace
open scoped _root_.Topology Manifold ContDiff
universe u
variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
variable [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real Classical.propDecidable
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable {D : RealTangentDistribution (realModel d) M}
variable (U : HPS.LeafPartition D ι L (fun _ ↦ 2))

variable [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]

variable {n s : ℕ} (T : Fin n → Opens (Fin s → ℝ))
variable (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
variable (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
variable (parametrization : ∀ i (t : T i), Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  (⟨{z | (z, t.val) ∈ (c i).target},
    (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
  (branch i t) ∞)
variable (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
variable (hparam : ∀ i t z, (c i).symm (z.val, t.val) =
  (U.leaf (label i t)).inclusion (parametrization i t z).val)

include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- The zero quadratic coefficient in each full flowbox chart defines a continuous homogeneous section of native truncation on the corresponding open base domain. (Ghys, §3) -/
theorem native_flowbox_zero_sections :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∀ (E1 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet1 L)
          ((ℂ × (Fin s → ℝ)) × ℂ))
      (E2 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet2 L)
          (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ)),
    (∀ k, (E1 k).source = (nativeLeafwiseJet1Base L U) ⁻¹' (c k).source ∧
      (E1 k).target = {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} ∧
      (E1 k : NativeLeafwiseJet1 L → _) = nativeLeafwiseJet1Coeff L U (c k) ∧
      (E2 k).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c k).source ∧
      (E2 k).target = {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} ∧
      (E2 k : NativeLeafwiseJet2 L → _) = nativeLeafwiseJet2Coeff L U (c k)) →
    ∃ localSection : ∀ k, {j : NativeLeafwiseJet1 L |
        nativeLeafwiseJet1Base L U j ∈ (c k).source} → NativeLeafwiseJet2 L,
      (∀ k, Continuous (localSection k)) ∧
      (∀ k j, nativeLeafwiseJetTruncation L (localSection k j) = j.val ∧
        nativeLeafwiseJet2Coeff L U (c k) (localSection k j) =
          (nativeLeafwiseJet1Coeff L U (c k) j.val, 0)) ∧
      (∀ k (omega : ℂˣ) j j', j'.val = nativeLeafwiseJet1Scale L omega j.val →
        localSection k j' = nativeLeafwiseJet2Reparametrize L (.scale omega)
          (localSection k j)) := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  intro E1 E2 hE
  let localSection (k : Fin n) (j : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source}) := (E2 k).symm ((E1 k) j, 0)
  have htarget' (k : Fin n) (j : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source}) : ((E1 k) j, (0 : ℂ)) ∈ (E2 k).target := by
    rw [(hE k).2.2.2.2.1]
    have hj := (E1 k).map_source (show j.val ∈ (E1 k).source by
      rw [(hE k).1]; exact j.property)
    rwa [(hE k).2.1] at hj
  have hsource (k : Fin n) (j : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source}) :
      nativeLeafwiseJet2Base L U (localSection k j) ∈ (c k).source := by
    have hj := (E2 k).map_target (htarget' k j)
    rwa [(hE k).2.2.2.1] at hj
  have hcoeff (k : Fin n) (j : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source}) :
      nativeLeafwiseJet2Coeff L U (c k) (localSection k j) =
        (nativeLeafwiseJet1Coeff L U (c k) j.val, 0) := by
    rw [← (hE k).2.2.2.2.2, ← (hE k).2.2.1]
    exact (E2 k).right_inv (htarget' k j)
  have htrunc (k : Fin n) (j : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source}) :
      nativeLeafwiseJetTruncation L (localSection k j) = j.val := by
    have ht := native_flowbox_truncation_coeff L U T c label branch parametrization
      htarget hparam k (localSection k j) (hsource k j)
    apply (E1 k).injOn
    · rw [(hE k).1]
      change nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L (localSection k j)) ∈ (c k).source
      rw [ht.1]
      exact hsource k j
    · rw [(hE k).1]
      exact j.property
    · rw [(hE k).2.2.1, ht.2, hcoeff]
  refine ⟨localSection, ?_, (fun k j ↦ ⟨htrunc k j, hcoeff k j⟩), ?_⟩
  · intro k
    have h1 : Continuous (fun j : {j : NativeLeafwiseJet1 L |
        nativeLeafwiseJet1Base L U j ∈ (c k).source} ↦ (E1 k) j.val) :=
      (E1 k).continuousOn.comp_continuous continuous_subtype_val
        (by intro j; rw [(hE k).1]; exact j.property)
    exact (E2 k).symm.continuousOn.comp_continuous
      (h1.prodMk continuous_const) (htarget' k)
  · intro k omega j j' he
    have hs1 := (native_flowbox_scale_coeff L U T c label branch parametrization
      htarget hparam k omega).1 j.val j.property
    have hs2 := (native_flowbox_scale_coeff L U T c label branch parametrization
      htarget hparam k omega).2 (localSection k j) (hsource k j)
    apply (E2 k).injOn
    · rw [(hE k).2.2.2.1]
      exact hsource k j'
    · rw [(hE k).2.2.2.1]
      change nativeLeafwiseJet2Base L U (nativeLeafwiseJet2Reparametrize L (.scale omega)
        (localSection k j)) ∈ (c k).source
      rw [hs2.1]
      exact hsource k j
    · rw [(hE k).2.2.2.2.2, hcoeff k j', he, hs1.2, hs2.2, hcoeff k j]
      simp



include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- The native quadratic-zero jet over a first jet is represented by the actual inverse-flowbox affine germ. (Ghys, §3) -/
theorem native_flowbox_affine_germ (k : Fin n) (j : NativeLeafwiseJet1 L)
    (hj : nativeLeafwiseJet1Base L U j ∈ (c k).source) :
    ∃ gamma : CurveParamGerm (L j.1),
      nativeLeafwiseJetTruncation L ⟨j.1, curveJet2Class (L j.1) gamma⟩ = j ∧
      nativeLeafwiseJet2Coeff L U (c k) ⟨j.1, curveJet2Class (L j.1) gamma⟩ =
        (nativeLeafwiseJet1Coeff L U (c k) j, 0) ∧
      gamma.1.map (U.leaf j.1).inclusion =
        (((fun v : ℂ ↦ (c k).symm
          ((nativeLeafwiseJet1Coeff L U (c k) j).1.1 +
            (nativeLeafwiseJet1Coeff L U (c k) j).2 * v,
            (nativeLeafwiseJet1Coeff L U (c k) j).1.2)) : ℂ → M) : Germ (𝓝 (0 : ℂ)) M) := by
  let x := curveJet1Base (L j.1) j.2
  obtain ⟨q, hq, hqt, hqc, hqm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
    (label k) (branch k) (parametrization k) (htarget k) (hparam k) j.1 x hj
  let w := nativeLeafwiseJet1Coeff L U (c k) j
  have hw : w.1 ∈ (c k).target ∧ w.2 ≠ 0 :=
    (native_flowbox_jet1_bijOn L U (T k) (c k) (label k) (branch k)
      (parametrization k) (htarget k) (hparam k)).mapsTo hj
  have hz : w.1.1 = q.1 x := congrArg Prod.fst (hqc x hq).2
  let P : ℂ → ℂ := fun v ↦ w.1.1 + w.2 * v
  have hP : ContDiff ℂ ∞ P := by dsimp [P]; fun_prop
  have hPd (v : ℂ) : HasDerivAt P w.2 v := by
    simpa only [P, Pi.add_def, id_eq, mul_one, zero_add] using
      (hasDerivAt_const v w.1.1).add ((hasDerivAt_id v).const_mul w.2)
  have hP0 : P 0 = w.1.1 := by simp [P]
  have hPP : iteratedDeriv 2 P 0 / 2 = 0 := by
    have hd : deriv P = fun _ ↦ w.2 := funext (fun v ↦ (hPd v).deriv)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd, deriv_const, zero_div]
  obtain ⟨e, he0, he, hesmooth, heinv⟩ := scalar_local_biholomorph P hP
    (by rw [(hPd 0).deriv]; exact hw.2)
  let g := e.trans q.1.symm
  have hg0 : 0 ∈ g.source := by
    change 0 ∈ e.source ∧ e 0 ∈ q.1.target
    refine ⟨he0, ?_⟩
    rw [he, hP0, hz]
    exact q.1.map_source hq
  have hgsmooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas q.2).comp' hesmooth.contMDiffOn
  have hginv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target :=
    heinv.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas q.2)
  let gamma : CurveParamGerm (L j.1) :=
    ⟨((g : ℂ → L j.1) : CurveGerm (L j.1)), g, hg0, hgsmooth, hginv, rfl⟩
  have hbase : curveGermBase (L j.1) gamma.1 = x := by
    change q.1.symm (e 0) = x
    rw [he, hP0, hz, q.1.left_inv hq]
  have hgq : (q.1 ∘ g) =ᶠ[𝓝 (0 : ℂ)] P := by
    filter_upwards [g.open_source.mem_nhds hg0] with v hv
    change q.1 (q.1.symm (e v)) = P v
    rw [q.1.right_inv (show e v ∈ q.1.target from hv.2), he]
  have hfirst : curveGermFirst (L j.1) q gamma = w.2 := by
    change deriv (q.1 ∘ g) 0 = w.2
    exact hgq.deriv_eq.trans (hPd 0).deriv
  have hsecond : curveGermSecond (L j.1) q gamma = 0 := by
    change iteratedDeriv 2 (q.1 ∘ g) 0 / 2 = 0
    rw [hgq.iteratedDeriv_eq, hPP]
  have hclass := (leaf_jet_complex_manifold (L j.1)).2.1 gamma
  have hj2 : curveJet2Base (L j.1) (curveJet2Class (L j.1) gamma) = x :=
    hclass.2.1.trans hbase
  have hj2q : curveJet2Base (L j.1) (curveJet2Class (L j.1) gamma) ∈ q.1.source :=
    hj2.symm ▸ hq
  have hcoeff : nativeLeafwiseJet2Coeff L U (c k)
      ⟨j.1, curveJet2Class (L j.1) gamma⟩ = (w, 0) := by
    have hintrinsic := (hclass.2.2.2 q (hbase.symm ▸ hq)).2.2
    have hfirst' := congrArg (fun w ↦ w.1.2) hintrinsic
    have hsecond' := congrArg Prod.snd hintrinsic
    apply Prod.ext
    · apply Prod.ext
      · change (c k) ((U.leaf j.1).inclusion
          (curveJet2Base (L j.1) (curveJet2Class (L j.1) gamma))) = w.1
        rw [hj2]
        rfl
      · change germFirst ((curveJet2Class (L j.1) gamma).out.1.map
          (nativeLeafFlowboxScalar L U (c k) j.1)) = w.2
        rw [hqm _ hj2q]
        exact hfirst'.trans hfirst
    · change germSecond ((curveJet2Class (L j.1) gamma).out.1.map
        (nativeLeafFlowboxScalar L U (c k) j.1)) = 0
      rw [hqm _ hj2q]
      exact hsecond'.trans hsecond
  refine ⟨gamma, ?_, hcoeff, ?_⟩
  · have hj2src : nativeLeafwiseJet2Base L U ⟨j.1, curveJet2Class (L j.1) gamma⟩ ∈
        (c k).source := by change (U.leaf j.1).inclusion _ ∈ _; rwa [hj2]
    have ht := native_flowbox_truncation_coeff L U T c label branch parametrization
      htarget hparam k ⟨j.1, curveJet2Class (L j.1) gamma⟩ hj2src
    apply (native_flowbox_jet1_bijOn L U (T k) (c k) (label k) (branch k)
      (parametrization k) (htarget k) (hparam k)).injOn
    · change nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L _) ∈ (c k).source
      rw [ht.1]
      exact hj2src
    · exact hj
    · rw [ht.2, hcoeff]
  · apply Germ.coe_eq.mpr
    filter_upwards [g.open_source.mem_nhds hg0] with v hv
    have hqv : g v ∈ q.1.source := q.1.map_target hv.2
    have hc := hqc (g v) hqv
    have hscalar : q.1 (g v) = P v := by
      change q.1 (q.1.symm (e v)) = P v
      rw [q.1.right_inv (show e v ∈ q.1.target from hv.2), he]
    change (U.leaf j.1).inclusion (g v) = (c k).symm (P v, w.1.2)
    have heq : (c k) ((U.leaf j.1).inclusion (g v)) = (P v, w.1.2) := by
      rw [hscalar] at hc
      exact hc.2
    rw [← heq, (c k).left_inv hc.1]


include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- A native quadratic-zero section restricts to a holomorphic section on each original intrinsic leaf over the flowbox. (Ghys, §3) -/
theorem native_flowbox_zero_section_leafwise (k : Fin n)
    (localSection : {j : NativeLeafwiseJet1 L |
      nativeLeafwiseJet1Base L U j ∈ (c k).source} → NativeLeafwiseJet2 L)
    (htrunc : ∀ j, nativeLeafwiseJetTruncation L (localSection j) = j.val)
    (hzero : ∀ j, (nativeLeafwiseJet2Coeff L U (c k) (localSection j)).2 = 0)
    (ell : ι) :
    letI := nativeLeafJet1Charts L ell
    letI := nativeLeafJet2Charts L ell
    ∃ sigma : CurveJet1 (L ell) → CurveJet2 (L ell),
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ sigma
        {j | nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source} ∧
      ∀ j (hj : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source),
        localSection ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ =
          nativeLeafwiseJet2Inclusion L ell (sigma j) := by
  let := nativeLeafJet1Charts L ell
  let := nativeLeafJet2Charts L ell
  have hex (j : CurveJet1 (L ell)) : ∃ q : CurveJet2 (L ell),
      ∀ hj : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source,
        localSection ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ =
          nativeLeafwiseJet2Inclusion L ell q := by
    by_cases hj : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source
    · cases hv : localSection ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ with
      | mk ell' q =>
        have ht := htrunc ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩
        rw [hv] at ht
        have hl : ell' = ell := congrArg Sigma.fst ht
        subst ell'
        exact ⟨q, fun _ ↦ hv⟩
    · exact ⟨curveJet2Class (L ell) j.out, fun h ↦ (hj h).elim⟩
  choose sigma hsigma using hex
  refine ⟨sigma, ?_, hsigma⟩
  intro j hj
  obtain ⟨q, hq, _, hqc, hqm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
    (label k) (branch k) (parametrization k) (htarget k) (hparam k) ell
      (curveJet1Base (L ell) j) hj
  have hA : CurveJetCoefficientAtlases (L ell)
      (nativeLeafJet1Charts L ell) (nativeLeafJet2Charts L ell) := by
    obtain ⟨_, _, _, _, h1, h2, _, _, _, _, _, hc, hsource1, hsource2⟩ :=
      (leaf_jet_complex_manifold (L ell)).2.2.2.2.choose_spec.choose_spec
    exact ⟨h1, h2, hc, hsource1, hsource2⟩
  obtain ⟨sigma0, hsmooth, hcoeff, _⟩ := curve_jet_local_zero_section
    (L ell) _ _ hA q
  have hopen : IsOpen ((curveJet1Base (L ell)) ⁻¹' q.1.source) := by
    obtain ⟨e1, e2, _, _, hs1, _⟩ := hA.2.2.1 q
    rw [← hs1]
    exact e1.open_source
  have heq : sigma =ᶠ[𝓝 j] sigma0 := by
    filter_upwards [hopen.mem_nhds hq] with v hv
    have hsrc : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell v) ∈
        (c k).source := (hqc (curveJet1Base (L ell) v) hv).1
    have hlocal := hsigma v hsrc
    have htlocal := htrunc ⟨nativeLeafwiseJet1Inclusion L ell v, hsrc⟩
    rw [hlocal] at htlocal
    have htsigma : curveJetTruncation (L ell) (sigma v) = v := by
      exact eq_of_heq (Sigma.mk.inj htlocal).2
    have hbaseSigma : curveJet2Base (L ell) (sigma v) = curveJet1Base (L ell) v := by
      rw [← curve_jet_truncation_base, htsigma]
    have hbase0 : curveJet2Base (L ell) (sigma0 v) = curveJet1Base (L ell) v := by
      rw [← curve_jet_truncation_base, (hcoeff v hv).1]
    have hqsigma : curveJet2Base (L ell) (sigma v) ∈ q.1.source := hbaseSigma.symm ▸ hv
    have hq0 : curveJet2Base (L ell) (sigma0 v) ∈ q.1.source := hbase0.symm ▸ hv
    apply ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).2.1.injOn hqsigma hq0
    apply Prod.ext
    · have hts := ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).2.2 (sigma v) hqsigma
      rw [← hts.2, htsigma, (hcoeff v hv).2]
    · have hz := hzero ⟨nativeLeafwiseJet1Inclusion L ell v, hsrc⟩
      rw [hlocal] at hz
      change germSecond ((sigma v).out.1.map (nativeLeafFlowboxScalar L U (c k) ell)) = 0 at hz
      rw [hqm _ hqsigma] at hz
      rw [(hcoeff v hv).2]
      exact hz
  exact ((hsmooth.contMDiffAt (hopen.mem_nhds hq)).congr_of_eventuallyEq heq).contMDiffWithinAt


include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- The local native zero sections have all their geometric characterizations: continuity transversely, holomorphy intrinsically, and representatives equal to the actual affine inverse-flowbox germs. (Ghys, §3) -/
theorem native_flowbox_zero_sections_full :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∀ (E1 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet1 L)
          ((ℂ × (Fin s → ℝ)) × ℂ))
      (E2 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet2 L)
          (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ)),
    (∀ k, (E1 k).source = (nativeLeafwiseJet1Base L U) ⁻¹' (c k).source ∧
      (E1 k).target = {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} ∧
      (E1 k : NativeLeafwiseJet1 L → _) = nativeLeafwiseJet1Coeff L U (c k) ∧
      (E2 k).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c k).source ∧
      (E2 k).target = {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} ∧
      (E2 k : NativeLeafwiseJet2 L → _) = nativeLeafwiseJet2Coeff L U (c k)) →
    ∃ localSection : ∀ k, {j : NativeLeafwiseJet1 L |
        nativeLeafwiseJet1Base L U j ∈ (c k).source} → NativeLeafwiseJet2 L,
      (∀ k, Continuous (localSection k)) ∧
      (∀ k j, nativeLeafwiseJetTruncation L (localSection k j) = j.val ∧
        nativeLeafwiseJet2Coeff L U (c k) (localSection k j) =
          (nativeLeafwiseJet1Coeff L U (c k) j.val, 0)) ∧
      (∀ k j, ∃ gamma : CurveParamGerm (L j.val.1),
        localSection k j = ⟨j.val.1, curveJet2Class (L j.val.1) gamma⟩ ∧
        gamma.1.map (U.leaf j.val.1).inclusion =
          (((fun v : ℂ ↦ (c k).symm
            ((nativeLeafwiseJet1Coeff L U (c k) j.val).1.1 +
              (nativeLeafwiseJet1Coeff L U (c k) j.val).2 * v,
              (nativeLeafwiseJet1Coeff L U (c k) j.val).1.2)) : ℂ → M) : Germ (𝓝 (0 : ℂ)) M)) ∧
      (∀ k ell,
        letI := nativeLeafJet1Charts L ell
        letI := nativeLeafJet2Charts L ell
        ∃ sigma : CurveJet1 (L ell) → CurveJet2 (L ell),
          ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ sigma
            {j | nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source} ∧
          ∀ j (hj : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Inclusion L ell j) ∈ (c k).source),
            localSection k ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ =
              nativeLeafwiseJet2Inclusion L ell (sigma j)) ∧
      (∀ k (omega : ℂˣ) j j', j'.val = nativeLeafwiseJet1Scale L omega j.val →
        localSection k j' = nativeLeafwiseJet2Reparametrize L (.scale omega)
          (localSection k j)) := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  intro E1 E2 hE
  obtain ⟨localSection, hcont, hcoeff, hscale⟩ := native_flowbox_zero_sections
    L U T c label branch parametrization htarget hparam E1 E2 hE
  refine ⟨localSection, hcont, hcoeff, ?_, ?_, hscale⟩
  · intro k j
    obtain ⟨gamma, htrunc, hc, hg⟩ := native_flowbox_affine_germ
      L U T c label branch parametrization htarget hparam k j.val j.property
    refine ⟨gamma, ?_, hg⟩
    have hbase (q : NativeLeafwiseJet2 L) :
        nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L q) =
          nativeLeafwiseJet2Base L U q :=
      congrArg (U.leaf q.1).inclusion (curve_jet_truncation_base (L q.1) q.2)
    apply (E2 k).injOn
    · rw [(hE k).2.2.2.1]
      change nativeLeafwiseJet2Base L U (localSection k j) ∈ (c k).source
      rw [← hbase, (hcoeff k j).1]
      exact j.property
    · rw [(hE k).2.2.2.1]
      change nativeLeafwiseJet2Base L U ⟨j.val.1, curveJet2Class (L j.val.1) gamma⟩ ∈ (c k).source
      rw [← hbase, htrunc]
      exact j.property
    · rw [(hE k).2.2.2.2.2, (hcoeff k j).2, hc]
  · intro k ell
    exact native_flowbox_zero_section_leafwise L U T c label branch parametrization
      htarget hparam k (localSection k) (fun j ↦ (hcoeff k j).1)
      (fun j ↦ congrArg Prod.snd (hcoeff k j).2) ell


end HolomorphicAnosov.Ghys
