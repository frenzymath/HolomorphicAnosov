import HolomorphicAnosov.Ghys.NativeFlowboxRealCharts
import HolomorphicAnosov.Ghys.NativeFirstTangentHomeomorph
import HolomorphicAnosov.Ghys.NativeFlowboxScalarDerivative

/-! The continuous coordinate-unit first jet on a native flowbox (Ghys, §3) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology Bundle
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
  (G : NativeInvariantJetAffineLeafFamily f a L U)

/-- Every point of a native box target has a first jet with that ambient base and unit scalar coefficient. (Ghys, §3) -/
theorem native_flowbox_unit_jet_exists (k : Fin G.boxCount)
    (p : (G.box k).target) :
    ∃ q : NativeLeafwiseJet1 L,
      nativeLeafwiseJet1Base L U q = (G.box k).symm p.val ∧
      nativeLeafwiseJet1Coeff L U (G.box k) q = (p.val, 1) := by
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let t : G.transverse k := ⟨p.val.2, G.transverse_contains k p.val p.property⟩
  let z : nativeAffineFlowboxSlice (G.box k) t.val := ⟨p.val.1, p.property⟩
  obtain ⟨c, hc, hs, ht, hf, hi, _, _⟩ := native_flowbox_real_chart f a L U G k t z
  let chart : LeafChart (L (G.label k t)) := ⟨c, hc⟩
  obtain ⟨q, hq, hcoeff⟩ := ((leaf_jet_complex_manifold (L (G.label k t))).2.2.2.1 chart).1.surjOn
    (show (p.val.1, (1 : ℂ)) ∈ curveJet1Target (L (G.label k t)) chart from
      ⟨by change p.val.1 ∈ c.target; rw [ht]; exact p.property, one_ne_zero⟩)
  have hbase : curveJet1Base (L (G.label k t)) q = c.symm p.val.1 := by
    rw [← congrArg Prod.fst hcoeff]
    exact (c.left_inv hq).symm
  have hb : nativeLeafwiseJet1Base L U ⟨G.label k t, q⟩ = (G.box k).symm p.val := by
    change (U.leaf (G.label k t)).inclusion (curveJet1Base (L (G.label k t)) q) = _
    rw [hbase, hi z]
    exact (G.parametrization_inclusion k t z).symm
  refine ⟨⟨G.label k t, q⟩, hb, Prod.ext ?_ ?_⟩
  · change (G.box k) (nativeLeafwiseJet1Base L U ⟨G.label k t, q⟩) = p.val
    rw [hb, (G.box k).right_inv p.property]
  · change germFirst (q.out.val.map (nativeLeafFlowboxScalar L U (G.box k) (G.label k t))) = 1
    have hγ := (mdifferentiableAt_of_mfderiv_injective
      (curveParamGerm_mfderiv_bijective q.out).injective).continuousAt
    have hb0 : q.out.val.out 0 = curveJet1Base (L (G.label k t)) q := by
      change q.out.val.out 0 = curveGermBase (L (G.label k t)) q.out.val
      conv_rhs => rw [← Quotient.out_eq q.out.val]
      rfl
    have heq : (nativeLeafFlowboxScalar L U (G.box k) (G.label k t) ∘ q.out.val.out) =ᶠ[𝓝 0]
        c ∘ q.out.val.out := by
      filter_upwards [hγ.preimage_mem_nhds (c.open_source.mem_nhds (hb0 ▸ hq))] with w hw
      exact (hf _ hw).symm
    have hgerm : q.out.val.map (nativeLeafFlowboxScalar L U (G.box k) (G.label k t)) =
        q.out.val.map (c : L (G.label k t) → ℂ) := by
      conv_lhs => rw [← Quotient.out_eq q.out.val]
      conv_rhs => rw [← Quotient.out_eq q.out.val]
      exact Quotient.sound heq
    rw [hgerm]
    exact congrArg Prod.snd hcoeff

set_option maxHeartbeats 600000 in
/-- The unit-coordinate first jet can be chosen continuously on the whole native box target. (Ghys, §3) -/
theorem native_flowbox_unit_jet_continuous (k : Fin G.boxCount) :
    letI := nativeLeafwiseJet1Topology L U G.box
    ∃ q : (G.box k).target → NativeLeafwiseJet1 L,
      Continuous q ∧
      (∀ p, nativeLeafwiseJet1Base L U (q p) = (G.box k).symm p.val) ∧
      ∀ p, nativeLeafwiseJet1Coeff L U (G.box k) (q p) = (p.val, 1) := by
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let K := fun x : M ↦ (G.rankOne x).choose
  let E := fun x : M ↦ ↥(K x)
  let lineInclusion : TotalSpace ℂ E → TangentBundle (complexModel d) M :=
    fun v ↦ ⟨v.proj, v.snd.val⟩
  let : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced lineInclusion inferInstance
  let P := {v : TotalSpace ℂ E // v.snd ≠ 0}
  let := nativeLeafwiseJet1Topology L U G.box
  obtain ⟨e, hbase, _, _, hcoord, hframe⟩ := native_first_tangent_homeomorph_coordinates L
    G.rankOne U G.holomorphic_inclusion G.transverse G.box G.label G.branch
    G.parametrization G.box_cover G.transverse_contains G.parametrization_inclusion
  choose q hb hc using native_flowbox_unit_jet_exists L f a U G k
  let ambient : (G.box k).target → TangentBundle (complexModel d) M :=
    fun p ↦ lineInclusion (e (q p)).val
  have hproj (p : (G.box k).target) : (ambient p).proj = (G.box k).symm p.val :=
    (hbase (q p)).trans (hb p)
  have hboxCont : Continuous (fun p : (G.box k).target ↦ (G.box k).symm p.val) :=
    (G.box k).symm.continuousOn.domRestrict
  have hcont : Continuous ambient := by
    rw [continuous_iff_continuousAt]
    intro p
    apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) ambient).mpr
    refine ⟨hboxCont.continuousAt.congr (Filter.Eventually.of_forall (fun v ↦ (hproj v).symm)), ?_⟩
    let x := (ambient p).proj
    let ψ := chartAt (ComplexModel d) x
    have hxp : (G.box k).symm p.val ∈ ψ.source := by
      rw [← hproj]
      exact mem_chart_source _ _
    have hΩ : IsOpen ((G.box k).target ∩ (G.box k).symm ⁻¹' ψ.source) :=
      (G.box k).symm.continuousOn.isOpen_inter_preimage (G.box k).open_target ψ.open_source
    have hfr := ((hframe k ψ (IsManifold.chart_mem_maximalAtlas x)).continuousAt
      (hΩ.mem_nhds ⟨p.property, hxp⟩)).comp (x := p) continuous_subtype_val.continuousAt
    apply hfr.congr
    filter_upwards [hboxCont.continuousAt.preimage_mem_nhds (ψ.open_source.mem_nhds hxp)] with v hv
    have hz : nativeLeafwiseJet1Base L U (q v) ∈ (G.box k).source := by
      rw [hb]
      exact (G.box k).map_target v.property
    have hx : nativeLeafwiseJet1Base L U (q v) ∈ ψ.source := by rwa [hb]
    have h := hcoord k x (q v) hz hx
    rw [hc v, hb v, (G.box k).right_inv v.property] at h
    simpa only [Prod.snd, Prod.fst, one_smul, ψ, x, ambient, lineInclusion, Function.comp_apply] using h.symm
  have heq : Continuous (fun p ↦ e (q p)) := by
    apply Continuous.subtype_mk
    exact continuous_induced_rng.mpr hcont
  refine ⟨q, ?_, hb, hc⟩
  exact e.symm.continuous.comp heq |>.congr (fun p ↦ e.symm_apply_apply (q p))

/-- Reading the second coefficient of the continuous invariant section on the coordinate-unit jet gives a jointly continuous scalar function on the actual flowbox target. (Ghys, §3) -/
theorem native_flowbox_section_unit_coefficient (k : Fin G.boxCount) :
    letI := nativeLeafwiseJet1Topology L U G.box
    ∃ q : (G.box k).target → NativeLeafwiseJet1 L,
      Continuous q ∧
      (∀ p, nativeLeafwiseJet1Base L U (q p) = (G.box k).symm p.val) ∧
      (∀ p, nativeLeafwiseJet1Coeff L U (G.box k) (q p) = (p.val, 1)) ∧
      Continuous (fun p ↦ (nativeLeafwiseJet2Coeff L U (G.box k) (G.jetSection (q p))).2) := by
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let := nativeLeafwiseJet1Topology L U G.box
  let := nativeLeafwiseJet2Topology L U G.box
  obtain ⟨q, hq, hb, hc⟩ := native_flowbox_unit_jet_continuous L f a U G k
  have hbase (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet2Base L U (G.jetSection j) = nativeLeafwiseJet1Base L U j := by
    calc
      nativeLeafwiseJet2Base L U (G.jetSection j) =
          nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L (G.jetSection j)) := by
        exact congrArg (U.leaf (G.jetSection j).1).inclusion
          (curve_jet_truncation_base (L (G.jetSection j).1) (G.jetSection j).2).symm
      _ = nativeLeafwiseJet1Base L U j := congrArg (nativeLeafwiseJet1Base L U)
        (G.section_truncation j)
  refine ⟨q, hq, hb, hc, ?_⟩
  have hflow := nativeLeafwiseJet_flowbox_continuity L U G.box
  exact ((hflow.2.1 k).2.snd).comp_continuous (G.section_continuous.comp hq) (fun p ↦ by
    change nativeLeafwiseJet2Base L U (G.jetSection (q p)) ∈ (G.box k).source
    rw [hbase, hb]
    exact (G.box k).map_target p.property)

/-- Local equality on an open neighborhood of an admissible curve germ's base persists after composition with that germ. (Ghys, §3) -/
theorem curveParamGerm_map_eq_of_eqOn {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ∞ N]
    (γ : CurveParamGerm N) {Y : Type*} {φ ψ : N → Y} {S : Set N}
    (hS : IsOpen S) (hb : curveGermBase N γ.val ∈ S) (h : EqOn φ ψ S) :
    γ.val.map φ = γ.val.map ψ := by
  have hγ := (mdifferentiableAt_of_mfderiv_injective
    (curveParamGerm_mfderiv_bijective γ).injective).continuousAt
  have hb0 : γ.val.out 0 = curveGermBase N γ.val := by
    conv_rhs => rw [← Quotient.out_eq γ.val]
    rfl
  have heq : (φ ∘ γ.val.out) =ᶠ[𝓝 0] ψ ∘ γ.val.out := by
    filter_upwards [hγ.preimage_mem_nhds (hS.mem_nhds (hb0 ▸ hb))] with z hz
    exact h hz
  conv_lhs => rw [← Quotient.out_eq γ.val]
  conv_rhs => rw [← Quotient.out_eq γ.val]
  exact Quotient.sound heq

/-- The continuous native section restricts to the homogeneous holomorphic section on each original leaf with precisely the chosen native jet atlases. (Ghys, §3) -/
theorem native_leaf_homogeneous_section (i : ι) :
    letI : ∀ k, T2Space (L k) := fun k ↦ (U.leaf k).hausdorff
    letI : ∀ k, SecondCountableTopology (L k) := fun k ↦ (U.leaf k).countable
    ∃ σ : HomogeneousCurveJetSection (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i),
      ∀ q, G.jetSection (nativeLeafwiseJet1Inclusion L i q) =
        nativeLeafwiseJet2Inclusion L i (σ.val q) := by
  let : ∀ k, T2Space (L k) := fun k ↦ (U.leaf k).hausdorff
  let : ∀ k, SecondCountableTopology (L k) := fun k ↦ (U.leaf k).countable
  obtain ⟨τ, hτ, hsmooth⟩ := G.leaf_holomorphic i
  have htrunc (q : CurveJet1 (L i)) : curveJetTruncation (L i) (τ q) = q := by
    have h := G.section_truncation (nativeLeafwiseJet1Inclusion L i q)
    rw [hτ] at h
    exact Sigma.mk.inj h |>.2 |> eq_of_heq
  have hscale (omega : ℂˣ) (q : CurveJet1 (L i)) :
      τ (curveJet1Scale (L i) omega q) = curveJet2Reparametrize (L i) (.scale omega) (τ q) := by
    have h := G.section_homogeneous omega (nativeLeafwiseJet1Inclusion L i q)
    change G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Scale (L i) omega q)) = _ at h
    rw [hτ, hτ] at h
    exact Sigma.mk.inj h |>.2 |> eq_of_heq
  exact ⟨⟨τ, htrunc, hsmooth, hscale⟩, hτ⟩

/-- The native choices retain all coefficient-chart atlas laws of the original fixed-leaf theorem; these are the very atlases used by leaf holomorphy. (Ghys, §3) -/
theorem native_leaf_coefficient_atlases (i : ι) :
    letI : ∀ k, T2Space (L k) := fun k ↦ (U.leaf k).hausdorff
    letI : ∀ k, SecondCountableTopology (L k) := fun k ↦ (U.leaf k).countable
    CurveJetCoefficientAtlases (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i) := by
  let : ∀ k, T2Space (L k) := fun k ↦ (U.leaf k).hausdorff
  let : ∀ k, SecondCountableTopology (L k) := fun k ↦ (U.leaf k).countable
  have h := (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec
  rcases h with ⟨_, _, _, _, hM1, hM2, _, _, _, _, _, hcharts, ha1, ha2⟩
  exact ⟨hM1, hM2, hcharts, ha1, ha2⟩

/-- Equality of the guarded full coefficients in one genuine flowbox implies equality of native first jets. (Ghys, §3) -/
theorem native_flowbox_jet1_coeff_injective (k : Fin G.boxCount)
    {q r : NativeLeafwiseJet1 L}
    (hq : nativeLeafwiseJet1Base L U q ∈ (G.box k).source)
    (hr : nativeLeafwiseJet1Base L U r ∈ (G.box k).source)
    (h : nativeLeafwiseJet1Coeff L U (G.box k) q = nativeLeafwiseJet1Coeff L U (G.box k) r) :
    q = r := by
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let K := fun x : M ↦ (G.rankOne x).choose
  let E := fun x : M ↦ ↥(K x)
  let : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
    (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let := nativeLeafwiseJet1Topology L U G.box
  obtain ⟨e, hb, _, _, hc, _⟩ := native_first_tangent_homeomorph_coordinates L
    G.rankOne U G.holomorphic_inclusion G.transverse G.box G.label G.branch
    G.parametrization G.box_cover G.transverse_contains G.parametrization_inclusion
  have hbase : nativeLeafwiseJet1Base L U q = nativeLeafwiseJet1Base L U r :=
    (G.box k).injOn hq hr (congrArg Prod.fst h)
  let x := nativeLeafwiseJet1Base L U q
  have hxq : nativeLeafwiseJet1Base L U q ∈ (chartAt (ComplexModel d) x).source :=
    mem_chart_source _ _
  have hxr : nativeLeafwiseJet1Base L U r ∈ (chartAt (ComplexModel d) x).source :=
    hbase ▸ hxq
  let eq : TangentBundle (complexModel d) M := ⟨(e q).val.proj, (e q).val.snd.val⟩
  let er : TangentBundle (complexModel d) M := ⟨(e r).val.proj, (e r).val.snd.val⟩
  let tr := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  have heq : eq ∈ tr.source := by change (e q).val.proj ∈ (chartAt (ComplexModel d) x).source; rw [hb]; exact hxq
  have her : er ∈ tr.source := by change (e r).val.proj ∈ (chartAt (ComplexModel d) x).source; rw [hb]; exact hxr
  have he : eq = er := by
    apply tr.toPartialEquiv.injOn heq her
    apply Prod.ext
    · change (e q).val.proj = (e r).val.proj
      rw [hb, hb, hbase]
    · change (tr eq).2 = (tr er).2
      rw [hc k x q hq hxq, hc k x r hr hxr, h, hbase]
  apply e.toEquiv.injective
  apply Subtype.ext
  rcases heq' : (e q).val with ⟨b, v⟩
  rcases her' : (e r).val with ⟨c, w⟩
  change (⟨(e q).val.proj, (e q).val.snd.val⟩ : TangentBundle (complexModel d) M) =
    ⟨(e r).val.proj, (e r).val.snd.val⟩ at he
  rw [heq', her'] at he
  have hbc : b = c := congrArg TotalSpace.proj he
  subst c
  have hvw : v.val = w.val := TotalSpace.mk_injective b he
  have hvw' : v = w := Subtype.ext hvw
  exact congrArg (TotalSpace.mk b) hvw'

end HolomorphicAnosov.Ghys

