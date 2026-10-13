import HolomorphicAnosov.Ghys.NativeLeafwiseJetFlowboxContinuity
import HolomorphicAnosov.Ghys.NativeFlowboxUnitJet
import HolomorphicAnosov.Ghys.CurveJetHomogeneousLocalCoordinates
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous

/-! Jointly continuous holomorphic connection coefficients in native flowboxes. Source: Ghys Lemmas 3.2–3.3. -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The quadratic coefficient formula of a homogeneous section characterizes its fixed parametrization jets. -/
theorem homogeneous_section_fixed_iff_coefficient
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    {A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 N)}
    {A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 N)}
    (σ : HomogeneousCurveJetSection N A1 A2) (c : LeafChart N) (B : ℂ → ℂ)
    (hB : ∀ j, curveJet1Base N j ∈ c.val.source →
      (curveJet2Coeff N c (σ.val j)).2 =
        B (curveJet1Coeff N c j).1 * (curveJet1Coeff N c j).2 ^ 2)
    (γ : CurveParamGerm N) (hγ : curveGermBase N γ.val ∈ c.val.source) :
    σ.val (curveJet1Class N γ) = curveJet2Class N γ ↔
      curveGermSecond N c γ = B (c.val (curveGermBase N γ.val)) * curveGermFirst N c γ ^ 2 := by
  have hd := (leaf_jet_complex_manifold N).2.1 γ
  have hj : curveJet1Base N (curveJet1Class N γ) ∈ c.val.source := hd.1 ▸ hγ
  have hq : curveJet2Base N (curveJet2Class N γ) ∈ c.val.source := hd.2.1 ▸ hγ
  have hs : curveJet2Base N (σ.val (curveJet1Class N γ)) ∈ c.val.source := by
    rw [← curve_jet_truncation_base N _, σ.property.1]
    exact hj
  have hquad := hB (curveJet1Class N γ) hj
  rw [(hd.2.2.2 c hγ).2.1] at hquad
  constructor
  · intro h
    rw [h, (hd.2.2.2 c hγ).2.2] at hquad
    exact hquad
  · intro h
    apply ((leaf_jet_complex_manifold N).2.2.2.1 c).2.1.injOn hs hq
    apply Prod.ext
    · have hf := ((leaf_jet_complex_manifold N).2.2.2.1 c).2.2 _ hs |>.2
      rw [σ.property.1] at hf
      rw [← hf, (hd.2.2.2 c hγ).2.1, (hd.2.2.2 c hγ).2.2]
    · rw [hquad, (hd.2.2.2 c hγ).2.2]
      exact h.symm

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
  (G : NativeInvariantJetAffineLeafFamily f a L U)

/-- Identify the scalar connection coefficient of any leafwise homogeneous section by evaluation on the native unit jets. -/
theorem native_flowbox_section_coefficient_identification_g1
    (k : Fin G.boxCount)
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hleaf : letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
      letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
      ∀ i, ∃ σ : HomogeneousCurveJetSection (L i)
          (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i),
        ∀ j, τ (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (σ.val j))
    (q : (G.box k).target → NativeLeafwiseJet1 L)
    (hqb : ∀ p, nativeLeafwiseJet1Base L U (q p) = (G.box k).symm p.val)
    (hqc : ∀ p, nativeLeafwiseJet1Coeff L U (G.box k) (q p) = (p.val, 1))
    (A : ℂ × (Fin (2*d-2) → ℝ) → ℂ)
    (hAval : ∀ p : (G.box k).target,
      A p.val = (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q p))).2) :
    ∀ (t : G.transverse k) (c : LeafChart (L (G.label k t))),
        c.val.target = (nativeAffineFlowboxSlice (G.box k) t.val : Set ℂ) →
        (∀ z : nativeAffineFlowboxSlice (G.box k) t.val,
          c.val.symm z = (G.parametrization k t z).val) →
        (∀ y ∈ c.val.source, c.val y = nativeLeafFlowboxScalar L U (G.box k) (G.label k t) y) →
        ∃ B : ℂ → ℂ, DifferentiableOn ℂ B c.val.target ∧
          (∀ z ∈ c.val.target, B z = A (z, t.val)) ∧
          (∀ j : CurveJet1 (L (G.label k t)), curveJet1Base _ j ∈ c.val.source →
            (nativeLeafwiseJet2Coeff L U (G.box k)
              (τ (nativeLeafwiseJet1Inclusion L (G.label k t) j))).2 =
              B (curveJet1Coeff _ c j).1 * (curveJet1Coeff _ c j).2 ^ 2) ∧
          ∀ γ : CurveParamGerm (L (G.label k t)), curveGermBase _ γ.val ∈ c.val.source →
            (τ (nativeLeafwiseJet1Inclusion L (G.label k t) (curveJet1Class _ γ)) =
              nativeLeafwiseJet2Inclusion L (G.label k t) (curveJet2Class _ γ) ↔
              curveGermSecond _ c γ = B (c.val (curveGermBase _ γ.val)) * curveGermFirst _ c γ ^ 2) := by
  classical
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  intro t c ht hi hf
  obtain ⟨σ, hσ⟩ := hleaf (G.label k t)
  obtain ⟨⟨B, hBhol, hBquad, _⟩, _⟩ := homogeneous_curve_jet_section_local_coordinates
    (L (G.label k t)) _ _ (native_leaf_coefficient_atlases L f a U (G.label k t)) σ
  have hrawquad (j : CurveJet1 (L (G.label k t))) (hj : curveJet1Base _ j ∈ c.val.source) :
      (nativeLeafwiseJet2Coeff L U (G.box k)
        (τ (nativeLeafwiseJet1Inclusion L (G.label k t) j))).2 =
        B c (curveJet1Coeff _ c j).1 * (curveJet1Coeff _ c j).2 ^ 2 := by
    have hσbase : curveJet2Base (L (G.label k t)) (σ.val j) ∈ c.val.source := by
      rw [← curve_jet_truncation_base _ _, σ.property.1]
      exact hj
    have hgerm := curveParamGerm_map_eq_of_eqOn (σ.val j).out c.val.open_source hσbase
      (fun y hy ↦ (hf y hy).symm)
    rw [hσ j]
    change germSecond ((σ.val j).out.val.map
      (nativeLeafFlowboxScalar L U (G.box k) (G.label k t))) = _
    rw [hgerm]
    exact hBquad c j hj
  refine ⟨B c, hBhol c, ?_, hrawquad, ?_⟩
  · intro z hz
    let v : nativeAffineFlowboxSlice (G.box k) t.val := ⟨z, by change z ∈ (nativeAffineFlowboxSlice (G.box k) t.val : Set ℂ); rwa [← ht]⟩
    let p : (G.box k).target := ⟨(z, t.val), v.property⟩
    obtain ⟨j, hj, hjcoef⟩ := ((leaf_jet_complex_manifold (L (G.label k t))).2.2.2.1 c).1.surjOn
      (show (z, (1 : ℂ)) ∈ curveJet1Target _ c from ⟨hz, one_ne_zero⟩)
    let jn := nativeLeafwiseJet1Inclusion L (G.label k t) j
    have hjbase : curveJet1Base (L (G.label k t)) j = c.val.symm z := by
      have hzEq : c.val (curveJet1Base (L (G.label k t)) j) = z := congrArg Prod.fst hjcoef
      rw [← hzEq]
      exact (c.val.left_inv hj).symm
    have hjb : nativeLeafwiseJet1Base L U jn = (G.box k).symm p.val := by
      change (U.leaf (G.label k t)).inclusion (curveJet1Base (L (G.label k t)) j) = _
      rw [hjbase, hi v]
      exact (G.parametrization_inclusion k t v).symm
    have hjc : nativeLeafwiseJet1Coeff L U (G.box k) jn = (p.val, 1) := by
      apply Prod.ext
      · change (G.box k) (nativeLeafwiseJet1Base L U jn) = p.val
        rw [hjb, (G.box k).right_inv p.property]
      · change germFirst (j.out.val.map (nativeLeafFlowboxScalar L U (G.box k) (G.label k t))) = 1
        rw [curveParamGerm_map_eq_of_eqOn j.out c.val.open_source hj (fun y hy ↦ (hf y hy).symm)]
        exact congrArg Prod.snd hjcoef
    have hqj : q p = jn := native_flowbox_jet1_coeff_injective L f a U G k
      (by rw [hqb]; exact (G.box k).map_target p.property)
      (by rw [hjb]; exact (G.box k).map_target p.property)
      ((hqc p).trans hjc.symm)
    change B c z = A p.val
    rw [hAval p, hqj, hrawquad j hj, hjcoef]
    simp
  · intro γ hγ
    rw [hσ (curveJet1Class _ γ)]
    have h := homogeneous_section_fixed_iff_coefficient σ c (B c) (hBquad c) γ hγ
    constructor
    · intro he
      exact h.mp (eq_of_heq (Sigma.mk.inj he).2)
    · intro he
      exact congrArg (nativeLeafwiseJet2Inclusion L (G.label k t)) (h.mpr he)

/-- The value of a homogeneous section on a native unit jet, expressed in any intrinsic holomorphic chart. -/
theorem native_unit_section_coefficient_in_chart_g1
    (k : Fin G.boxCount) (i : ι)
    (σ : letI : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
      letI : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
      HomogeneousCurveJetSection (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i))
    (c : LeafChart (L i)) (Q : ℂ → ℂ)
    (hQ : ∀ j, curveJet1Base (L i) j ∈ c.val.source →
      (curveJet2Coeff (L i) c (σ.val j)).2 =
        Q (curveJet1Coeff (L i) c j).1 * (curveJet1Coeff (L i) c j).2 ^ 2)
    (j : CurveJet1 (L i))
    (hjc : curveJet1Base (L i) j ∈ c.val.source)
    (hjb : (U.leaf i).inclusion (curveJet1Base (L i) j) ∈ (G.box k).source)
    (hjunit : (nativeLeafwiseJet1Coeff L U (G.box k)
      (nativeLeafwiseJet1Inclusion L i j)).2 = 1) :
    let H := nativeLeafFlowboxScalar L U (G.box k) i ∘ c.val.symm
    let z := c.val (curveJet1Base (L i) j)
    DifferentiableAt ℂ H z ∧ deriv H z ≠ 0 ∧
      (nativeLeafwiseJet2Coeff L U (G.box k)
        (nativeLeafwiseJet2Inclusion L i (σ.val j))).2 * deriv H z ^ 2 =
          deriv H z * Q z + deriv (deriv H) z / 2 := by
  classical
  let : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
  let : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
  intro H z
  let t : G.transverse k := ⟨(G.box k ((U.leaf i).inclusion (curveJet1Base (L i) j))).2,
    G.transverse_contains k _ ((G.box k).map_source hjb)⟩
  let v : nativeAffineFlowboxSlice (G.box k) t.val :=
    ⟨(G.box k ((U.leaf i).inclusion (curveJet1Base (L i) j))).1,
      (G.box k).map_source hjb⟩
  have hinc : (U.leaf (G.label k t)).inclusion (G.parametrization k t v).val =
      (U.leaf i).inclusion (curveJet1Base (L i) j) := by
    rw [← G.parametrization_inclusion]
    exact (G.box k).left_inv hjb
  have hlabel := U.disjoint _ _ _ _ hinc
  clear_value v t
  cases hlabel
  have hpoint : (G.parametrization k t v).val = curveJet1Base (L (G.label k t)) j :=
    (U.leaf _).injective hinc
  obtain ⟨d,hd,hs,ht,hf,hi,_,_⟩ := native_flowbox_real_chart f a L U G k t v
  let cd : LeafChart (L (G.label k t)) := ⟨d,hd⟩
  have hjd : curveJet1Base _ j ∈ d.source := by
    rw [hs,← hpoint]
    exact (G.parametrization k t v).property
  have hσd : curveJet2Base _ (σ.val j) ∈ d.source := by
    rw [← curve_jet_truncation_base _ _,σ.property.1]
    exact hjd
  have hσc : curveJet2Base _ (σ.val j) ∈ c.val.source := by
    rw [← curve_jet_truncation_base _ _,σ.property.1]
    exact hjc
  have hraw1 : (curveJet1Coeff _ cd j).2 = 1 := by
    change germFirst (j.out.val.map d) = 1
    rw [curveParamGerm_map_eq_of_eqOn j.out d.open_source hjd hf]
    exact hjunit
  have hraw2 : (nativeLeafwiseJet2Coeff L U (G.box k)
      (nativeLeafwiseJet2Inclusion L (G.label k t) (σ.val j))).2 =
        (curveJet2Coeff _ cd (σ.val j)).2 := by
    change germSecond ((σ.val j).out.val.map (nativeLeafFlowboxScalar L U (G.box k) _)) = _
    rw [curveParamGerm_map_eq_of_eqOn (σ.val j).out d.open_source hσd
      (fun y hy ↦ (hf y hy).symm)]
    rfl
  have hgerm : H =ᶠ[𝓝 z] (d ∘ c.val.symm) := by
    filter_upwards [(c.val.symm.trans d).open_source.mem_nhds
      ⟨c.val.map_source hjc,by
        change c.val.symm (c.val (curveJet1Base _ j)) ∈ d.source
        rw [c.val.left_inv hjc]
        exact hjd⟩] with w hw
    exact (hf _ hw.2).symm
  have hfirst := congrArg Prod.snd (((leaf_jet_complex_manifold _).2.2.1 c cd).1 j ⟨hjc,hjd⟩)
  have hfirstσ := ((leaf_jet_complex_manifold _).2.2.2.1 c).2.2 (σ.val j) hσc |>.2
  rw [σ.property.1] at hfirstσ
  have hsecond := congrArg Prod.snd (((leaf_jet_complex_manifold _).2.2.1 c cd).2
    (σ.val j) ⟨hσc,hσd⟩)
  dsimp only [curveJet1Transition] at hfirst
  rw [hraw1] at hfirst
  have hfirst' : deriv H z * (curveJet1Coeff _ c j).2 = 1 := by
    rw [hgerm.deriv_eq]
    exact hfirst.symm
  have hne : deriv H z ≠ 0 := by
    intro h
    rw [h,zero_mul] at hfirst'
    exact zero_ne_one hfirst'
  have hdH : DifferentiableAt ℂ H z := by
    have hh : ContDiffOn ℂ ∞ (d ∘ c.val.symm) (c.val.symm.trans d).source :=
      ((contMDiffOn_of_mem_maximalAtlas hd).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas c.property)).contDiffOn
    have hzmem : z ∈ (c.val.symm.trans d).source := by
      refine ⟨c.val.map_source hjc,?_⟩
      change c.val.symm (c.val (curveJet1Base _ j)) ∈ d.source
      rwa [c.val.left_inv hjc]
    exact ((hh.differentiableOn (by simp) z hzmem).differentiableAt
      ((c.val.symm.trans d).open_source.mem_nhds hzmem)).congr_of_eventuallyEq hgerm
  refine ⟨hdH,hne,?_⟩
  rw [hraw2,hsecond]
  dsimp only [curveJet2Transition]
  rw [← hfirstσ,hQ j hjc]
  change (deriv (d ∘ c.val.symm) z * (Q z * (curveJet1Coeff _ c j).2 ^ 2) +
    iteratedDeriv 2 (d ∘ c.val.symm) z * (curveJet1Coeff _ c j).2 ^ 2 / 2) *
    deriv H z ^ 2 = _
  rw [← hgerm.deriv_eq]
  have hsecondH : iteratedDeriv 2 (d ∘ c.val.symm) z = deriv (deriv H) z := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hgerm.deriv.deriv_eq.symm
  rw [hsecondH]
  calc
    _ = (deriv H z * Q z + deriv (deriv H) z / 2) *
        (deriv H z * (curveJet1Coeff _ c j).2) ^ 2 := by ring
    _ = _ := by rw [hfirst']; ring

/-- The intrinsic coefficient formula applies to any supplied native unit jet at the marked point: the leaf partition identifies its actual carrier. -/
theorem native_unit_section_coefficient_at_point_g1
    (k : Fin G.boxCount) (i : ι)
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (σ : letI : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
      letI : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
      HomogeneousCurveJetSection (L i) (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i))
    (hτ : ∀ j, τ (nativeLeafwiseJet1Inclusion L i j) =
      nativeLeafwiseJet2Inclusion L i (σ.val j))
    (c : LeafChart (L i)) (Q : ℂ → ℂ)
    (hQ : ∀ j, curveJet1Base (L i) j ∈ c.val.source →
      (curveJet2Coeff (L i) c (σ.val j)).2 =
        Q (curveJet1Coeff (L i) c j).1 * (curveJet1Coeff (L i) c j).2 ^ 2)
    (x : L i) (hxc : x ∈ c.val.source)
    (hxb : (U.leaf i).inclusion x ∈ (G.box k).source)
    (j : NativeLeafwiseJet1 L) (hjb : nativeLeafwiseJet1Base L U j = (U.leaf i).inclusion x)
    (hjunit : (nativeLeafwiseJet1Coeff L U (G.box k) j).2 = 1) :
    let H := nativeLeafFlowboxScalar L U (G.box k) i ∘ c.val.symm
    let z := c.val x
    DifferentiableAt ℂ H z ∧ deriv H z ≠ 0 ∧
      (nativeLeafwiseJet2Coeff L U (G.box k) (τ j)).2 * deriv H z ^ 2 =
        deriv H z * Q z + deriv (deriv H) z / 2 := by
  classical
  let : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
  let : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
  rcases j with ⟨l,j⟩
  have hlabel : l = i := U.disjoint _ _ _ _ hjb
  subst l
  have hjx : curveJet1Base (L i) j = x := (U.leaf i).injective hjb
  have h := native_unit_section_coefficient_in_chart_g1 L f a U G k i σ c Q hQ
    j (hjx ▸ hxc) (hjx ▸ hxb) hjunit
  change _ ∧ _ ∧ (nativeLeafwiseJet2Coeff L U (G.box k)
    (τ (nativeLeafwiseJet1Inclusion L i j))).2 * _ = _
  rw [hτ]
  simpa only [hjx] using h

/-- Continuous intrinsic connection coefficients in a continuously evaluated family of holomorphic plaque charts give continuous native unit coefficients. -/
theorem native_unit_coefficient_continuous_in_plaque_charts_g1
    (k : Fin G.boxCount) {R : Type*} [TopologicalSpace R] (label : R → ι)
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (σ : letI : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
      letI : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
      ∀ r, HomogeneousCurveJetSection (L (label r))
        (nativeLeafJet1Charts L (label r)) (nativeLeafJet2Charts L (label r)))
    (hτ : ∀ r j, τ (nativeLeafwiseJet1Inclusion L (label r) j) =
      nativeLeafwiseJet2Inclusion L (label r) ((σ r).val j))
    (c : ∀ r, LeafChart (L (label r))) (Q : R → ℂ → ℂ)
    (hQ : ∀ r j, curveJet1Base (L (label r)) j ∈ (c r).val.source →
      (curveJet2Coeff (L (label r)) (c r) ((σ r).val j)).2 =
        Q r (curveJet1Coeff (L (label r)) (c r) j).1 *
          (curveJet1Coeff (L (label r)) (c r) j).2 ^ 2)
    (Ω : Set (ℂ × R)) (hΩ : IsOpen Ω)
    (hc : ∀ p ∈ Ω, p.1 ∈ (c p.2).val.target)
    (hE : ContinuousOn (fun p : ℂ × R ↦
      (U.leaf (label p.2)).inclusion ((c p.2).val.symm p.1)) Ω)
    (hQc : ContinuousOn (fun p : ℂ × R ↦ Q p.2 p.1) Ω)
    (q : (G.box k).target → NativeLeafwiseJet1 L)
    (hqb : ∀ p, nativeLeafwiseJet1Base L U (q p) = (G.box k).symm p.val)
    (hqu : ∀ p, (nativeLeafwiseJet1Coeff L U (G.box k) (q p)).2 = 1)
    (A : M → ℂ)
    (hA : ∀ x (hx : x ∈ (G.box k).source), A x =
      (nativeLeafwiseJet2Coeff L U (G.box k)
        (τ (q ⟨G.box k x,(G.box k).map_source hx⟩))).2) :
    ContinuousOn (fun p : ℂ × R ↦
      A ((U.leaf (label p.2)).inclusion ((c p.2).val.symm p.1)))
      (Ω ∩ {p | (U.leaf (label p.2)).inclusion ((c p.2).val.symm p.1) ∈ (G.box k).source}) := by
  classical
  let : ∀ l, T2Space (L l) := fun l ↦ (U.leaf l).hausdorff
  let : ∀ l, SecondCountableTopology (L l) := fun l ↦ (U.leaf l).countable
  let E (p : ℂ × R) := (U.leaf (label p.2)).inclusion ((c p.2).val.symm p.1)
  let V := Ω ∩ E ⁻¹' (G.box k).source
  have hV : IsOpen V := hE.isOpen_inter_preimage hΩ (G.box k).open_source
  let H (p : ℂ × R) := (G.box k (E p)).1
  have hH : ContinuousOn H V :=
    continuous_fst.comp_continuousOn ((G.box k).continuousOn.comp
      (hE.mono inter_subset_left) (fun p hp ↦ hp.2))
  have hformula (p : ℂ × R) (hp : p ∈ V) :
      DifferentiableAt ℂ (fun z ↦ H (z,p.2)) p.1 ∧
      deriv (fun z ↦ H (z,p.2)) p.1 ≠ 0 ∧
      A (E p) * deriv (fun z ↦ H (z,p.2)) p.1 ^ 2 =
        deriv (fun z ↦ H (z,p.2)) p.1 * Q p.2 p.1 +
          deriv (deriv (fun z ↦ H (z,p.2))) p.1 / 2 := by
    let pt : (G.box k).target := ⟨G.box k (E p),(G.box k).map_source hp.2⟩
    have hbase : nativeLeafwiseJet1Base L U (q pt) = E p := by
      rw [hqb]
      exact (G.box k).left_inv hp.2
    have h := native_unit_section_coefficient_at_point_g1 L f a U G k (label p.2)
      τ (σ p.2) (hτ p.2) (c p.2) (Q p.2) (hQ p.2) ((c p.2).val.symm p.1)
      ((c p.2).val.map_target (hc p hp.1)) hp.2 (q pt) hbase (hqu pt)
    dsimp only at h
    rw [(c p.2).val.right_inv (hc p hp.1)] at h
    change DifferentiableAt ℂ (fun z ↦ H (z,p.2)) p.1 ∧
      deriv (fun z ↦ H (z,p.2)) p.1 ≠ 0 ∧
      (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q pt))).2 * _ = _ at h
    rw [hA (E p) hp.2]
    exact h
  have hhol (r : R) : DifferentiableOn ℂ (fun z ↦ H (z,r)) {z | (z,r) ∈ V} :=
    fun z hz ↦ (hformula (z,r) hz).1.differentiableWithinAt
  have h1 := SliceDerivativePreparation.joint_deriv_continuousOn_open V hV H hH hhol
  have h2 := SliceDerivativePreparation.joint_deriv_continuousOn_open V hV
    (fun p ↦ deriv (fun z ↦ H (z,p.2)) p.1) h1
    (fun r ↦ (hhol r).deriv (hV.preimage (continuous_id.prodMk continuous_const)))
  have hcont := ((h1.mul (hQc.mono inter_subset_left)).add (h2.div_const (2 : ℂ))).div
    (h1.pow 2) (fun p hp ↦ pow_ne_zero _ (hformula p hp).2.1)
  apply hcont.congr
  intro p hp
  exact (eq_div_iff (pow_ne_zero _ (hformula p hp).2.1)).mpr (hformula p hp).2.2

/-- Continuity of the scalar coefficient on native unit jets suffices for continuity of any leafwise homogeneous section. -/
theorem native_homogeneous_section_continuous_of_unit_evaluation_g1
    (τ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (htrunc : ∀ j, nativeLeafwiseJetTruncation L (τ j) = j)
    (hleaf : letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
      letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
      ∀ i, ∃ σ : HomogeneousCurveJetSection (L i)
          (nativeLeafJet1Charts L i) (nativeLeafJet2Charts L i),
        ∀ j, τ (nativeLeafwiseJet1Inclusion L i j) = nativeLeafwiseJet2Inclusion L i (σ.val j))
    (hunit : ∀ (k : Fin G.boxCount) (q : (G.box k).target → NativeLeafwiseJet1 L),
      (∀ p, nativeLeafwiseJet1Base L U (q p) = (G.box k).symm p.val) →
      (∀ p, nativeLeafwiseJet1Coeff L U (G.box k) (q p) = (p.val,1)) →
      Continuous (fun p ↦ (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q p))).2)) :
    letI := nativeLeafwiseJet1Topology L U G.box
    letI := nativeLeafwiseJet2Topology L U G.box
    Continuous τ := by
  classical
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let := nativeLeafwiseJet1Topology L U G.box
  let := nativeLeafwiseJet2Topology L U G.box
  have hbase (j : NativeLeafwiseJet1 L) :
      nativeLeafwiseJet2Base L U (τ j) = nativeLeafwiseJet1Base L U j := by
    calc
      nativeLeafwiseJet2Base L U (τ j) =
          nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L (τ j)) :=
        congrArg (U.leaf (τ j).1).inclusion (curve_jet_truncation_base _ _).symm
      _ = _ := congrArg (nativeLeafwiseJet1Base L U) (htrunc j)
  choose q _ hqb hqc using (fun k ↦ native_flowbox_unit_jet_continuous L f a U G k)
  let A (k : Fin G.boxCount) (p : ℂ × (Fin (2*d-2) → ℝ)) : ℂ :=
    if hp : p ∈ (G.box k).target then
      (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q k ⟨p,hp⟩))).2 else 0
  have hAval (k : Fin G.boxCount) (p : (G.box k).target) :
      A k p.val = (nativeLeafwiseJet2Coeff L U (G.box k) (τ (q k p))).2 := by
    simp only [A, dite_eq_left p.property]
  have hA (k : Fin G.boxCount) : ContinuousOn (A k) (G.box k).target :=
    continuousOn_iff_continuous_domRestrict.mpr
      ((hunit k (q k) (hqb k) (hqc k)).congr (fun p ↦ (hAval k p).symm))
  apply nativeLeafwiseJetSection_continuous_of_quadratic_coeff L U G.box G.box_cover τ hbase
    (fun k x ↦ A k (G.box k x))
    (fun k ↦ (hA k).comp (G.box k).continuousOn (G.box k).mapsTo)
  intro k j hj
  rcases j with ⟨i,j⟩
  let t : G.transverse k := ⟨(G.box k (nativeLeafwiseJet1Base L U ⟨i,j⟩)).2,
    G.transverse_contains k _ ((G.box k).map_source hj)⟩
  let v : nativeAffineFlowboxSlice (G.box k) t.val :=
    ⟨(G.box k (nativeLeafwiseJet1Base L U ⟨i,j⟩)).1, (G.box k).map_source hj⟩
  have hinc : (U.leaf (G.label k t)).inclusion (G.parametrization k t v).val =
      (U.leaf i).inclusion (curveJet1Base (L i) j) := by
    rw [← G.parametrization_inclusion]
    exact (G.box k).left_inv hj
  have hlabel := U.disjoint _ _ _ _ hinc
  clear_value v t
  cases hlabel
  have hpoint : (G.parametrization k t v).val = curveJet1Base (L (G.label k t)) j :=
    (U.leaf _).injective hinc
  obtain ⟨c, hc, hs, ht, hf, hi, _, _⟩ := native_flowbox_real_chart f a L U G k t v
  let ch : LeafChart (L (G.label k t)) := ⟨c,hc⟩
  have hjc : curveJet1Base (L (G.label k t)) j ∈ c.source := by
    rw [hs, ← hpoint]
    exact (G.parametrization k t v).property
  have hpair : c (curveJet1Base (L (G.label k t)) j) = v.val ∧
      G.box k (nativeLeafwiseJet1Base L U ⟨G.label k t,j⟩) = (v.val,t.val) := by
    have hz : v.val ∈ c.target := by rw [ht]; exact v.property
    constructor
    · rw [← hpoint, ← hi v, c.right_inv hz]
    · change G.box k ((U.leaf (G.label k t)).inclusion (curveJet1Base _ j)) = _
      rw [← hpoint, ← G.parametrization_inclusion, (G.box k).right_inv v.property]
  obtain ⟨σ,hσ⟩ := hleaf (G.label k t)
  have hσbase : curveJet2Base _ (σ.val j) ∈ c.source := by
    rw [← curve_jet_truncation_base _ _, σ.property.1]
    exact hjc
  have hg1 := curveParamGerm_map_eq_of_eqOn j.out c.open_source hjc (fun y hy ↦ (hf y hy).symm)
  have hg2 := curveParamGerm_map_eq_of_eqOn (σ.val j).out c.open_source hσbase (fun y hy ↦ (hf y hy).symm)
  have hfirst : (curveJet2Coeff _ ch (σ.val j)).1 = curveJet1Coeff _ ch j := by
    have hh := ((leaf_jet_complex_manifold (L (G.label k t))).2.2.2.1 ch).2.2 (σ.val j) hσbase |>.2
    simpa only [σ.property.1] using hh.symm
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (G.box k) (hbase ⟨G.label k t,j⟩)
    · change (nativeLeafwiseJet2Coeff L U (G.box k) (τ (nativeLeafwiseJet1Inclusion L (G.label k t) j))).1.2 = _
      rw [hσ j]
      change germFirst ((σ.val j).out.val.map (nativeLeafFlowboxScalar L U (G.box k) (G.label k t))) =
        germFirst (j.out.val.map (nativeLeafFlowboxScalar L U (G.box k) (G.label k t)))
      rw [hg1, hg2]
      exact congrArg Prod.snd hfirst
  · obtain ⟨B,hhol,hBeq,hquad,_⟩ := native_flowbox_section_coefficient_identification_g1
      L f a U G k τ hleaf (q k) (hqb k) (hqc k) (A k) (hAval k) t ch ht hi hf
    change (nativeLeafwiseJet2Coeff L U (G.box k) (τ (nativeLeafwiseJet1Inclusion L (G.label k t) j))).2 = _
    rw [hquad j hjc]
    change B (c (curveJet1Base _ j)) * (curveJet1Coeff _ ch j).2 ^ 2 = _
    rw [hBeq _ (c.map_source hjc)]
    change A k (c (curveJet1Base _ j),t.val) * (curveJet1Coeff _ ch j).2 ^ 2 =
      A k (G.box k (nativeLeafwiseJet1Base L U ⟨G.label k t,j⟩)) *
        germFirst (j.out.val.map _) ^ 2
    rw [hpair.1, hpair.2, hg1]
    rfl

/-- The native homogeneous section has a jointly continuous connection coefficient on each actual box target. -/
theorem native_flowbox_connection_coefficient (k : Fin G.boxCount) :
    ∃ A : ℂ × (Fin (2*d-2) → ℝ) → ℂ,
      ContinuousOn A (G.box k).target ∧
      ∀ (t : G.transverse k) (c : LeafChart (L (G.label k t))),
        c.val.target = (nativeAffineFlowboxSlice (G.box k) t.val : Set ℂ) →
        (∀ z : nativeAffineFlowboxSlice (G.box k) t.val,
          c.val.symm z = (G.parametrization k t z).val) →
        (∀ y ∈ c.val.source, c.val y = nativeLeafFlowboxScalar L U (G.box k) (G.label k t) y) →
        ∃ B : ℂ → ℂ, DifferentiableOn ℂ B c.val.target ∧
          (∀ z ∈ c.val.target, B z = A (z, t.val)) ∧
          ∀ γ : CurveParamGerm (L (G.label k t)), curveGermBase _ γ.val ∈ c.val.source →
            (G.jetSection (nativeLeafwiseJet1Inclusion L (G.label k t) (curveJet1Class _ γ)) =
              nativeLeafwiseJet2Inclusion L (G.label k t) (curveJet2Class _ γ) ↔
              curveGermSecond _ c γ = B (c.val (curveGermBase _ γ.val)) * curveGermFirst _ c γ ^ 2) := by
  classical
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  let := nativeLeafwiseJet1Topology L U G.box
  obtain ⟨q, _, hqb, hqc, hA⟩ := native_flowbox_section_unit_coefficient L f a U G k
  let A : ℂ × (Fin (2*d-2) → ℝ) → ℂ := fun p ↦
    if hp : p ∈ (G.box k).target then
      (nativeLeafwiseJet2Coeff L U (G.box k) (G.jetSection (q ⟨p, hp⟩))).2 else 0
  have hAval (p : (G.box k).target) :
      A p.val = (nativeLeafwiseJet2Coeff L U (G.box k) (G.jetSection (q p))).2 := by
    dsimp [A]
    rw [dite_eq_left p.property]
  refine ⟨A, ?_, ?_⟩
  · exact continuousOn_iff_continuous_domRestrict.mpr
      (hA.congr (fun p ↦ (hAval p).symm))
  intro t c ht hi hf
  obtain ⟨B, hhol, heq, _, hgraph⟩ := native_flowbox_section_coefficient_identification_g1
    L f a U G k G.jetSection (fun i ↦ native_leaf_homogeneous_section L f a U G i)
    q hqb hqc A hAval t c ht hi hf
  exact ⟨B, hhol, heq, hgraph⟩

/-- Solving the flat-coordinate ODE in an exact scalar chart produces a chart of the original section-induced maximal affine atlas. -/
theorem native_connection_ode_chart_affine (i : ι) (c : LeafChart (L i)) (B : ℂ → ℂ)
    (hgraph : ∀ γ : CurveParamGerm (L i), curveGermBase (L i) γ.val ∈ c.val.source →
      (G.jetSection (nativeLeafwiseJet1Inclusion L i (curveJet1Class (L i) γ)) =
        nativeLeafwiseJet2Inclusion L i (curveJet2Class (L i) γ) ↔
        curveGermSecond (L i) c γ = B (c.val (curveGermBase (L i) γ.val)) *
          curveGermFirst (L i) c γ ^ 2))
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℂ ∞ e e.source) (hei : ContDiffOn ℂ ∞ e.symm e.target)
    (hODE : ∀ z ∈ e.source, deriv e z ≠ 0 ∧
      deriv (deriv e) z = (-2 : ℂ) * B z * deriv e z) :
    c.val.trans e ∈ ComplexAffineStructure.maximalAtlas (L i) (Quotient.mk (complexAffineAtlasSetoid (L i)) (G.affineAtlas i)) := by
  let : T2Space (L i) := (U.leaf i).hausdorff
  let : SecondCountableTopology (L i) := (U.leaf i).countable
  have hdmax : c.val.trans e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ (L i) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact he.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas c.property)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas c.property).comp' hei.contMDiffOn
  let d : LeafChart (L i) := ⟨c.val.trans e, hdmax⟩
  apply (G.flat_chart_iff i (c.val.trans e)).mpr
  refine ⟨(isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas (L i) _).mpr hdmax, ?_⟩
  intro γ hγ
  have hγc : curveGermBase (L i) γ.val ∈ c.val.source := hγ.1
  let z := c.val (curveGermBase (L i) γ.val)
  have hzt : z ∈ c.val.target := c.val.map_source hγc
  have hze : z ∈ e.source := hγ.2
  have heq : (d.val ∘ c.val.symm) =ᶠ[𝓝 z] (e : ℂ → ℂ) := by
    filter_upwards [c.val.open_target.mem_nhds hzt] with w hw
    simp only [d, OpenPartialHomeomorph.coe_trans, Function.comp_apply, c.val.right_inv hw]
  have hrep := (leaf_jet_complex_manifold (L i)).2.1 γ
  have hsecond := congrArg Prod.snd
    (((leaf_jet_complex_manifold (L i)).2.2.1 c d).2 (curveJet2Class (L i) γ)
      ⟨hrep.2.1 ▸ hγc, hrep.2.1 ▸ hγ⟩)
  rw [(hrep.2.2.2 c hγc).2.2, (hrep.2.2.2 d hγ).2.2] at hsecond
  change curveGermSecond (L i) d γ =
    deriv (d.val ∘ c.val.symm) z * curveGermSecond (L i) c γ +
      iteratedDeriv 2 (d.val ∘ c.val.symm) z * curveGermFirst (L i) c γ ^ 2 / 2 at hsecond
  rw [heq.deriv_eq, heq.iteratedDeriv_eq 2] at hsecond
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hsecond
  rw [(hODE z hze).2] at hsecond
  have hfactor : curveGermSecond (L i) d γ = deriv e z *
      (curveGermSecond (L i) c γ - B z * curveGermFirst (L i) c γ ^ 2) := by
    rw [hsecond]
    ring
  rw [hgraph γ hγc]
  change curveGermSecond (L i) c γ = B z * curveGermFirst (L i) c γ ^ 2 ↔
    curveGermSecond (L i) d γ = 0
  rw [hfactor]
  constructor
  · intro h
    rw [h, sub_self, mul_zero]
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (hODE z hze).1)

end HolomorphicAnosov.Ghys


