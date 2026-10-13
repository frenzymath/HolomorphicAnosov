import HolomorphicAnosov.Ghys.CurveJetAffineData
import HolomorphicAnosov.Ghys.CurveJetHomogeneousLocalCoordinates
import HolomorphicAnosov.Analysis.Complex.AffineRatioJetCoefficientContinuityG1
import HolomorphicAnosov.Analysis.Complex.HolomorphicAffineOfSecondDerivZero

/-! Local flat jet coordinates and their gluing into the affine correspondence. (Ghys, Lemma 3.2) -/

open Filter Set
open scoped _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
attribute [local instance] curveScalarToProductChartedSpace

/-- Every marked point has a centered holomorphic leaf chart whose inverse unit disk lies in a
prescribed open neighborhood. -/
theorem centered_leaf_chart_in_open_g1 (x : L) (V : Set L) (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ c : LeafChart L, x ∈ c.val.source ∧ c.val x = 0 ∧
      Metric.ball (0 : ℂ) 1 ⊆ c.val.target ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, c.val.symm z ∈ V := by
  let e := chartAt ℂ x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  have hemax : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ L := IsManifold.chart_mem_maximalAtlas x
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) :=
    e.symm.continuousOn.isOpen_inter_preimage e.open_target hV
  have hxO : e x ∈ e.target ∩ e.symm ⁻¹' V :=
    ⟨e.map_source hxe,by simpa only [mem_preimage,e.left_inv hxe] using hxV⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hO (e x) hxO
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  let B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ∞ := {
    toFun := fun z ↦ (z-e x)/(r : ℂ)
    invFun := fun z ↦ (r : ℂ)*z+e x
    left_inv := fun z ↦ by field_simp; ring
    right_inv := fun z ↦ by field_simp; ring
    contMDiff_toFun := (contMDiff_id.sub contMDiff_const).div_const _
    contMDiff_invFun := (contMDiff_const.mul contMDiff_id).add contMDiff_const }
  let c := e.trans B.toHomeomorph.toOpenPartialHomeomorph
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ L := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    exact ⟨B.contMDiff.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas hemax),
      (contMDiffOn_symm_of_mem_maximalAtlas hemax).comp' B.symm.contMDiff.contMDiffOn⟩
  have hsmall (z : ℂ) (hz : z ∈ Metric.ball 0 1) : B.symm z ∈ e.target ∩ e.symm ⁻¹' V := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    change ‖(r : ℂ)*z+e x-e x‖ < r
    rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    nlinarith
  refine ⟨⟨c,hc⟩,⟨hxe,mem_univ _⟩,?_,?_,?_⟩
  · change (e x-e x)/(r : ℂ) = 0
    simp
  · intro z hz
    exact ⟨mem_univ _,(hsmall z hz).1⟩
  · intro z hz
    exact (hsmall z hz).2

/-- A parametrization whose second jet lies on the section graph has zero second coefficient in a
flat chart. -/
theorem curve_jet_section_flat_coeff_of_graph
    [T2Space L] [SecondCountableTopology L]
    {A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L)}
    {A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)}
    (σ : HomogeneousCurveJetSection L A1 A2) (c : LeafChart L)
    (hg : ∀ γ : CurveParamGerm L, curveGermBase L γ.1 ∈ c.1.source →
      (σ.1 (curveJet1Class L γ) = curveJet2Class L γ →
        germSecond (γ.1.map (c.1 : L → ℂ)) = 0))
    (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.1.source) :
    (curveJet2Coeff L c (σ.1 j)).2 = 0 := by
  let γ := (σ.1 j).out
  have hq : curveJet2Class L γ = σ.1 j := Quotient.out_eq _
  have hγj : curveJet1Class L γ = j := by
    rw [← ((leaf_jet_complex_manifold L).2.1 γ).2.2.1, hq, σ.2.1 j]
  have hγ : curveGermBase L γ.1 ∈ c.1.source := by
    change curveJet2Base L (σ.1 j) ∈ c.1.source
    rwa [← curve_jet_truncation_base L (σ.1 j), σ.2.1 j]
  exact hg γ hγ (by rw [hγj, hq])

/-- In a leaf coordinate, a section flat in another chart has quadratic coefficient `-h''/(2h')`,
where `h` is the transition to the flat chart. (Ghys, Lemma 3.2) -/
theorem curve_jet_section_coeff_of_flat_chart
    [T2Space L] [SecondCountableTopology L]
    {A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L)}
    {A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)}
    (σ : HomogeneousCurveJetSection L A1 A2) (c d : LeafChart L)
    (hdflat : ∀ j, curveJet1Base L j ∈ d.1.source →
      (curveJet2Coeff L d (σ.1 j)).2 = 0)
    (j : CurveJet1 L) (hjc : curveJet1Base L j ∈ c.1.source)
    (hjd : curveJet1Base L j ∈ d.1.source) :
    (curveJet2Coeff L c (σ.1 j)).2 =
      -(deriv (deriv (d.1 ∘ c.1.symm)) (curveJet1Coeff L c j).1 /
        (2 * deriv (d.1 ∘ c.1.symm) (curveJet1Coeff L c j).1)) *
          (curveJet1Coeff L c j).2 ^ 2 := by
  have hbase : curveJet2Base L (σ.1 j) = curveJet1Base L j := by
    rw [← curve_jet_truncation_base L (σ.1 j), σ.2.1 j]
  have hfirst : (curveJet2Coeff L c (σ.1 j)).1 = curveJet1Coeff L c j := by
    have h := (((leaf_jet_complex_manifold L).2.2.2.1 c).2.2
      (σ.1 j) (hbase ▸ hjc)).2
    simpa only [σ.2.1 j] using h.symm
  have htransition := (leaf_jet_complex_manifold L).2.2.1 c d
  have hvelocity := ((leaf_jet_complex_manifold L).2.2.2.1 d).1.mapsTo hjd
  have hchange := htransition.1 j ⟨hjc, hjd⟩
  have hnonzero : deriv (d.1 ∘ c.1.symm) (curveJet1Coeff L c j).1 ≠ 0 := by
    have h := hvelocity.2
    rw [hchange] at h
    exact left_ne_zero_of_mul h
  have hsecond := congrArg Prod.snd
    (htransition.2 (σ.1 j) ⟨hbase ▸ hjc, hbase ▸ hjd⟩)
  dsimp only [curveJet2Transition] at hsecond
  rw [hfirst, hdflat j hjd] at hsecond
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hsecond
  field_simp
  linear_combination -2 * hsecond

/-- The scalar coefficient of a homogeneous section equals the flat-chart logarithmic derivative as
a germ at each common coordinate point. -/
theorem curve_jet_section_coefficient_germ_of_flat_chart_g1
    [T2Space L] [SecondCountableTopology L]
    {A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L)}
    {A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)}
    (σ : HomogeneousCurveJetSection L A1 A2) (c d : LeafChart L)
    (A : ℂ → ℂ)
    (hc : ∀ j, curveJet1Base L j ∈ c.1.source →
      (curveJet2Coeff L c (σ.1 j)).2 =
        A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2)
    (hd : ∀ j, curveJet1Base L j ∈ d.1.source →
      (curveJet2Coeff L d (σ.1 j)).2 = 0)
    (z : ℂ) (hz : z ∈ c.1.target) (hzd : c.1.symm z ∈ d.1.source) :
    A =ᶠ[𝓝 z] fun w ↦ -(deriv (deriv (d.1 ∘ c.1.symm)) w /
      (2 * deriv (d.1 ∘ c.1.symm) w)) := by
  filter_upwards [(c.1.symm.trans d.1).open_source.mem_nhds ⟨hz,hzd⟩] with w hw
  obtain ⟨j,hjc,hjcoeff⟩ := ((leaf_jet_complex_manifold L).2.2.2.1 c).1.surjOn
    (show (w,(1 : ℂ)) ∈ curveJet1Target L c from ⟨hw.1,one_ne_zero⟩)
  have hjbase : curveJet1Base L j = c.1.symm w := by
    calc
      curveJet1Base L j = c.1.symm (c.1 (curveJet1Base L j)) := (c.1.left_inv hjc).symm
      _ = c.1.symm w := congrArg c.1.symm (congrArg Prod.fst hjcoeff)
  have he := curve_jet_section_coeff_of_flat_chart L σ c d hd j hjc (hjbase ▸ hw.2)
  rw [hc j hjc,hjcoeff] at he
  simpa only [one_pow,mul_one] using he

/-- A family of homogeneous sections has continuous scalar coefficients when its flat-chart germs
admit univalent disk representatives with continuous affine ratios. (Ghys, Prop. 3.1(ii),
pp.590–593) -/
theorem curve_jet_section_coefficients_continuous_of_affine_ratios_g1
    (hcompact : IsCompact {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g})
    {T : Type*} [MetricSpace T] (Y : T → Type*)
    [∀ t, TopologicalSpace (Y t)] [∀ t, ChartedSpace ℂ (Y t)]
    [∀ t, IsManifold 𝓘(ℂ) ∞ (Y t)]
    [∀ t, T2Space (Y t)] [∀ t, SecondCountableTopology (Y t)]
    (A1 : ∀ t, ChartedSpace (ℂ × ℂ) (CurveJet1 (Y t)))
    (A2 : ∀ t, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (Y t)))
    (hAtlases : ∀ t, CurveJetCoefficientAtlases (Y t) (A1 t) (A2 t))
    (σ : ∀ t, HomogeneousCurveJetSection (Y t) (A1 t) (A2 t))
    (c d : ∀ t, LeafChart (Y t))
    (hc : ∀ t, Metric.ball (0 : ℂ) 1 ⊆ (c t).1.target)
    (hd : ∀ t j, curveJet1Base (Y t) j ∈ (d t).1.source →
      (curveJet2Coeff (Y t) (d t) ((σ t).1 j)).2 = 0)
    (hcd : ∀ t, (c t).1.symm 0 ∈ (d t).1.source)
    (F : T → C(Complex.UnitDisc, ℂ)) (b : Complex.UnitDisc) (hb : b ≠ 0)
    (hF : ∀ t, DifferentiableOn ℂ (unitDiscExtension (F t)) (Metric.ball 0 1) ∧
      Function.Injective (F t) ∧ ∀ z : Complex.UnitDisc,
        deriv (unitDiscExtension (F t)) z.val ≠ 0)
    (hratio : ∀ z : Complex.UnitDisc, z ≠ 0 → z ≠ b →
      Continuous (fun t ↦ (F t 0 - F t z) / (F t 0 - F t b)))
    (hgerm : ∀ t, ((d t).1 ∘ (c t).1.symm) =ᶠ[𝓝 0] unitDiscExtension (F t)) :
    ∃ Q : T → ℂ → ℂ,
      (∀ t, DifferentiableOn ℂ (Q t) (c t).1.target) ∧
      (∀ t j, curveJet1Base (Y t) j ∈ (c t).1.source →
        (curveJet2Coeff (Y t) (c t) ((σ t).1 j)).2 =
          Q t (curveJet1Coeff (Y t) (c t) j).1 * (curveJet1Coeff (Y t) (c t) j).2 ^ 2) ∧
      Continuous (fun p : Complex.UnitDisc × T ↦ Q p.2 p.1.val) := by
  classical
  have hex (t : T) := (homogeneous_curve_jet_section_local_coordinates (Y t)
    (A1 t) (A2 t) (hAtlases t) (σ t)).1
  choose Q hQhol hQquad hQtrans using hex
  refine ⟨fun t ↦ Q t (c t),fun t ↦ hQhol t (c t),fun t ↦ hQquad t (c t),?_⟩
  apply continuous_affine_ratio_coefficient_of_germs_g1 hcompact F b hb hF hratio
    (fun t ↦ Q t (c t)) (fun t ↦ (hQhol t (c t)).mono (hc t))
  intro t
  have hcoeff := curve_jet_section_coefficient_germ_of_flat_chart_g1 (Y t) (σ t)
    (c t) (d t) (Q t (c t)) (hQquad t (c t)) (hd t) 0
    (hc t (Metric.mem_ball_self (by norm_num))) (hcd t)
  filter_upwards [hcoeff,(hgerm t).deriv,(hgerm t).deriv.deriv] with z hz h1 h2
  simpa only [h1,h2] using hz

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- A family of homogeneous sections has continuous scalar coefficients when representatives of its
flat-chart germs have continuous affine ratios. -/
theorem curve_jet_coefficients_continuous_of_holonomy_germs_g1
    (hcompact : IsCompact {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g})
    {R : Type*} [MetricSpace R] (Y : R → Type*)
    [∀ r, TopologicalSpace (Y r)] [∀ r, ChartedSpace ℂ (Y r)]
    [∀ r, IsManifold 𝓘(ℂ) ∞ (Y r)] [∀ r, T2Space (Y r)]
    [∀ r, SecondCountableTopology (Y r)]
    (A1 : ∀ r, ChartedSpace (ℂ × ℂ) (CurveJet1 (Y r)))
    (A2 : ∀ r, ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (Y r)))
    (hAtlases : ∀ r, CurveJetCoefficientAtlases (Y r) (A1 r) (A2 r))
    (σ : ∀ r, HomogeneousCurveJetSection (Y r) (A1 r) (A2 r))
    (e h : ∀ r, OpenPartialHomeomorph L (Y r))
    (he : ∀ r, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (e r) (e r).source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (e r).symm (e r).target)
    (hh : ∀ r, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (h r) (h r).source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (h r).symm (h r).target)
    (c₀ : LeafChart L) (d : ∀ r, LeafChart (Y r))
    (hc₀ : Metric.ball (0 : ℂ) 1 ⊆ c₀.val.target)
    (hsource : ∀ r z, z ∈ Metric.ball (0 : ℂ) 1 →
      c₀.val.symm z ∈ (e r).source ∧ c₀.val.symm z ∈ (h r).source ∧
        (h r) (c₀.val.symm z) ∈ (d r).val.source)
    (hgerm : ∀ r, (e r : L → Y r) =ᶠ[𝓝 (c₀.val.symm 0)] h r)
    (hd : ∀ r j, curveJet1Base (Y r) j ∈ (d r).val.source →
      (curveJet2Coeff (Y r) (d r) ((σ r).val j)).2 = 0)
    (b : Complex.UnitDisc) (hb : b ≠ 0)
    (hratio : ∀ z : Complex.UnitDisc, z ≠ 0 → z ≠ b →
      Continuous (fun r ↦
        ((d r).val ((h r) (c₀.val.symm 0)) - (d r).val ((h r) (c₀.val.symm z.val))) /
        ((d r).val ((h r) (c₀.val.symm 0)) - (d r).val ((h r) (c₀.val.symm b.val))))) :
    ∃ c : ∀ r, LeafChart (Y r),
      (∀ r, (c r).val = (e r).symm.trans c₀.val) ∧
      ∃ Q : R → ℂ → ℂ,
        (∀ r, DifferentiableOn ℂ (Q r) (c r).val.target) ∧
        (∀ r j, curveJet1Base (Y r) j ∈ (c r).val.source →
          (curveJet2Coeff (Y r) (c r) ((σ r).val j)).2 =
            Q r (curveJet1Coeff (Y r) (c r) j).1 * (curveJet1Coeff (Y r) (c r) j).2 ^ 2) ∧
        Continuous (fun p : Complex.UnitDisc × R ↦ Q p.2 p.1.val) := by
  classical
  have hc (r : R) : (e r).symm.trans c₀.val ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ (Y r) := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    exact ⟨(contMDiffOn_of_mem_maximalAtlas c₀.property).comp' (he r).2,
      (he r).1.comp' (contMDiffOn_symm_of_mem_maximalAtlas c₀.property)⟩
  let c (r : R) : LeafChart (Y r) := ⟨(e r).symm.trans c₀.val,hc r⟩
  let E (r : R) := c₀.val.symm.trans ((h r).trans (d r).val)
  have hEs (r : R) : Metric.ball (0 : ℂ) 1 ⊆ (E r).source :=
    fun z hz ↦ ⟨hc₀ hz,(hsource r z hz).2⟩
  have hEh (r : R) : DifferentiableOn ℂ (E r) (E r).source :=
    (((contMDiffOn_of_mem_maximalAtlas (d r).property).comp' (hh r).1).comp'
      (contMDiffOn_symm_of_mem_maximalAtlas c₀.property)).contDiffOn.differentiableOn (by simp)
  have hEi (r : R) : DifferentiableOn ℂ (E r).symm (E r).target :=
    ((contMDiffOn_of_mem_maximalAtlas c₀.property).comp'
      ((hh r).2.comp' (contMDiffOn_symm_of_mem_maximalAtlas (d r).property))).contDiffOn.differentiableOn (by simp)
  choose F hFval hFhol hFinj hFder using fun r ↦
    holomorphic_chart_unitDisc_map_g1 (E r) (hEs r) (hEh r) (hEi r)
  refine ⟨c,fun _ ↦ rfl,?_⟩
  apply curve_jet_section_coefficients_continuous_of_affine_ratios_g1
    hcompact Y A1 A2 hAtlases σ c d
    (fun r z hz ↦ ⟨hc₀ hz,(hsource r z hz).1⟩) hd ?_ F b hb
    (fun r ↦ ⟨hFhol r,hFinj r,hFder r⟩) ?_ ?_
  · intro r
    change (e r) (c₀.val.symm 0) ∈ (d r).val.source
    rw [(hgerm r).eq_of_nhds]
    exact (hsource r 0 (Metric.mem_ball_self (by norm_num))).2.2
  · intro z hz hzb
    apply (hratio z hz hzb).congr
    intro r
    simp only [hFval]
    rfl
  · intro r
    have hnear := (hgerm r).comp_tendsto
      (c₀.val.symm.continuousAt (hc₀ (Metric.mem_ball_self (by norm_num)))).tendsto
    filter_upwards [hnear,Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))]
      with z hz hzdisc
    change (d r).val ((e r) (c₀.val.symm z)) = unitDiscExtension (F r) z
    dsimp only [Function.comp_apply] at hz
    rw [hz]
    simp only [unitDiscExtension,dite_eq_left hzdisc]
    exact (hFval r ⟨z,hzdisc⟩).symm

/-- Local biholomorphic solutions of the homogeneous section equation give a correspondence between
complex affine structures and homogeneous holomorphic jet sections. (Ghys, Lemma 3.2) -/
theorem curve_jet_affine_correspondence_of_local_coordinates
    [T2Space L] [SecondCountableTopology L]
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
    (hAtlases : CurveJetCoefficientAtlases L A1 A2)
    (hcoordinates : ∀ (σ : HomogeneousCurveJetSection L A1 A2)
      (c : LeafChart L) (z : ℂ), z ∈ c.1.target →
      ∃ (A : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ),
        z ∈ e.source ∧ e.source ⊆ c.1.target ∧
        ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target ∧
        (∀ j : CurveJet1 L, curveJet1Base L j ∈ c.1.source →
          (curveJet2Coeff L c (σ.1 j)).2 =
            A (curveJet1Coeff L c j).1 * (curveJet1Coeff L c j).2 ^ 2) ∧
        ∀ w ∈ e.source,
          deriv e w ≠ 0 ∧ deriv (deriv e) w = (-2 : ℂ) * A w * deriv e w ) :
    Nonempty (CurveJetAffineCorrespondence L A1 A2) := by
  have hbase (σ : HomogeneousCurveJetSection L A1 A2) (j : CurveJet1 L) :
      curveJet2Base L (σ.1 j) = curveJet1Base L j := by
    rw [← curve_jet_truncation_base L (σ.1 j), σ.2.1 j]
  have hfirst (σ : HomogeneousCurveJetSection L A1 A2) (c : LeafChart L)
      (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.1.source) :
      (curveJet2Coeff L c (σ.1 j)).1 = curveJet1Coeff L c j := by
    have h := (((leaf_jet_complex_manifold L).2.2.2.1 c).2.2
      (σ.1 j) (hbase σ j ▸ hj)).2
    simpa only [σ.2.1 j] using h.symm
  have hflatCompatible (σ : HomogeneousCurveJetSection L A1 A2) (c d : LeafChart L)
      (hcflat : ∀ j, curveJet1Base L j ∈ c.1.source →
        (curveJet2Coeff L c (σ.1 j)).2 = 0)
      (hdflat : ∀ j, curveJet1Base L j ∈ d.1.source →
        (curveJet2Coeff L d (σ.1 j)).2 = 0) :
      AffineChartsCompatible L c.1 d.1 := by
    let k := c.1.symm.trans d.1
    have hk : ContDiffOn ℂ ∞ k k.source :=
      ((contMDiffOn_of_mem_maximalAtlas d.2).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas c.2)).contDiffOn
    have hderiv (w : ℂ) (hw : w ∈ k.source) :
        deriv k w ≠ 0 ∧ deriv (deriv k) w = 0 := by
      have hcoeff := (leaf_jet_complex_manifold L).2.2.2.1
      obtain ⟨j, hjc, hjcoeff⟩ := (hcoeff c).1.surjOn
        (show (w, (1 : ℂ)) ∈ curveJet1Target L c from ⟨hw.1, one_ne_zero⟩)
      have hjbase : curveJet1Base L j = c.1.symm w := by
        calc
          curveJet1Base L j = c.1.symm (c.1 (curveJet1Base L j)) :=
            (c.1.left_inv hjc).symm
          _ = c.1.symm w := congrArg c.1.symm (congrArg Prod.fst hjcoeff)
      have hjd : curveJet1Base L j ∈ d.1.source := hjbase ▸ hw.2
      have htransition := (leaf_jet_complex_manifold L).2.2.1 c d
      have hvelocity := (hcoeff d).1.mapsTo hjd
      have hchange := htransition.1 j ⟨hjc, hjd⟩
      have hnonzero : deriv k w ≠ 0 := by
        have h := hvelocity.2
        rw [hchange, hjcoeff] at h
        simpa only [k, OpenPartialHomeomorph.coe_trans, curveJet1Transition, mul_one] using h
      refine ⟨hnonzero, ?_⟩
      have hsecond := congrArg Prod.snd
        (htransition.2 (σ.1 j) ⟨hbase σ j ▸ hjc, hbase σ j ▸ hjd⟩)
      dsimp only [curveJet2Transition] at hsecond
      rw [hfirst σ c j hjc, hjcoeff, hcflat j hjc, hdflat j hjd] at hsecond
      have hzero : iteratedDeriv 2 (d.1 ∘ c.1.symm) w = 0 := by
        have hdiv : iteratedDeriv 2 (d.1 ∘ c.1.symm) w / 2 = 0 := by
          simpa only [mul_zero, zero_add, one_pow, mul_one] using hsecond.symm
        exact (div_eq_zero_iff.mp hdiv).resolve_right (by norm_num)
      simpa only [k, OpenPartialHomeomorph.coe_trans, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero] using hzero
    intro x hx
    have hxk : c.1 x ∈ k.source := by
      change c.1 x ∈ c.1.target ∧ c.1.symm (c.1 x) ∈ d.1.source
      exact ⟨c.1.map_source hx.1, by simpa only [c.1.left_inv hx.1] using hx.2⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp k.open_source (c.1 x) hxk
    obtain ⟨a, b, ha, hab⟩ := holomorphic_affine_of_second_deriv_zero
      Metric.isOpen_ball ((convex_ball (c.1 x) r).isConnected
        ⟨c.1 x, Metric.mem_ball_self hr⟩)
      ((hk.differentiableOn (by simp)).mono hball)
      (fun w hw ↦ (hderiv w (hball hw)).2) (fun w hw ↦ (hderiv w (hball hw)).1)
    refine ⟨⟨a, ha, b⟩, ?_⟩
    have hnear := (c.1.continuousAt hx.1).preimage_mem_nhds
      (Metric.ball_mem_nhds (c.1 x) hr)
    filter_upwards [hnear, c.1.open_source.mem_nhds hx.1] with y hy hys
    have h := hab (c.1 y) hy
    simpa only [k, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, c.1.left_inv hys, ComplexAffineTransformation.apply] using h
  have hflatCover (σ : HomogeneousCurveJetSection L A1 A2) (x : L) :
      ∃ d : LeafChart L, x ∈ d.1.source ∧
        ∀ j : CurveJet1 L, curveJet1Base L j ∈ d.1.source →
          (curveJet2Coeff L d (σ.1 j)).2 = 0 := by
    let c : LeafChart L := ⟨chartAt ℂ x, IsManifold.chart_mem_maximalAtlas x⟩
    have hxc : x ∈ c.1.source := mem_chart_source ℂ x
    obtain ⟨A, H, hzH, hHsource, hH, hHinv, hquad, hODE⟩ :=
      hcoordinates σ c (c.1 x) (c.1.map_source hxc)
    have hdmax : c.1.trans H ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L := by
      apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · exact hH.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas c.2)
      · exact (contMDiffOn_symm_of_mem_maximalAtlas c.2).comp' hHinv.contMDiffOn
    let d : LeafChart L := ⟨c.1.trans H, hdmax⟩
    refine ⟨d, ⟨hxc, hzH⟩, ?_⟩
    intro j hj
    have hjc : curveJet1Base L j ∈ c.1.source := hj.1
    let w := (curveJet1Coeff L c j).1
    have hw : w ∈ c.1.target := c.1.map_source hjc
    have hwH : w ∈ H.source := hj.2
    have heq : (d.1 ∘ c.1.symm) =ᶠ[𝓝 w] (H : ℂ → ℂ) := by
      filter_upwards [c.1.open_target.mem_nhds hw] with z hz
      simp only [d, OpenPartialHomeomorph.coe_trans, Function.comp_apply, c.1.right_inv hz]
    have hsecond := congrArg Prod.snd
      (((leaf_jet_complex_manifold L).2.2.1 c d).2 (σ.1 j)
        ⟨hbase σ j ▸ hjc, hbase σ j ▸ hj⟩)
    dsimp only [curveJet2Transition] at hsecond
    rw [hfirst σ c j hjc, hquad j hjc] at hsecond
    change (curveJet2Coeff L d (σ.1 j)).2 =
      deriv (d.1 ∘ c.1.symm) w * (A w * (curveJet1Coeff L c j).2 ^ 2) +
      iteratedDeriv 2 (d.1 ∘ c.1.symm) w * (curveJet1Coeff L c j).2 ^ 2 / 2 at hsecond
    rw [heq.deriv_eq, heq.iteratedDeriv_eq 2] at hsecond
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hsecond
    rw [(hODE w hwH).2] at hsecond
    convert hsecond using 1
    ring
  have hcompatibleSecond (c d : LeafChart L) (hcd : AffineChartsCompatible L c.1 d.1)
      (q : CurveJet2 L) (hq : curveJet2Base L q ∈ c.1.source ∩ d.1.source) :
      ∃ a : ComplexAffineTransformation,
        (curveJet2Coeff L d q).2 = a.slope * (curveJet2Coeff L c q).2 := by
    let x := curveJet2Base L q
    let w := c.1 x
    obtain ⟨a, ha⟩ := hcd x hq
    have hi : ContinuousAt c.1.symm w := c.1.continuousAt_symm (c.1.map_source hq.1)
    have hleft : c.1.symm w = x := c.1.left_inv hq.1
    have hnear : ∀ᶠ z in 𝓝 w, d.1 (c.1.symm z) = a.apply (c.1 (c.1.symm z)) := by
      exact hi.tendsto.eventually (show ∀ᶠ y in 𝓝 (c.1.symm w),
        d.1 y = a.apply (c.1 y) from by
          simpa only [hleft] using ha)
    have heq : (d.1 ∘ c.1.symm) =ᶠ[𝓝 w] (fun z ↦ a.slope * z + a.translation) := by
      filter_upwards [hnear, c.1.open_target.mem_nhds (c.1.map_source hq.1)] with z hz hzt
      simpa only [Function.comp_apply, c.1.right_inv hzt,
        ComplexAffineTransformation.apply] using hz
    have hderiv : deriv (fun z : ℂ ↦ a.slope * z + a.translation) = fun _ ↦ a.slope := by
      funext z
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id z).const_mul a.slope).add_const a.translation).deriv
    have hsecond := congrArg Prod.snd (((leaf_jet_complex_manifold L).2.2.1 c d).2 q hq)
    dsimp only [curveJet2Transition] at hsecond
    change (curveJet2Coeff L d q).2 = deriv (d.1 ∘ c.1.symm) w *
      (curveJet2Coeff L c q).2 + iteratedDeriv 2 (d.1 ∘ c.1.symm) w *
        (curveJet2Coeff L c q).1.2 ^ 2 / 2 at hsecond
    rw [heq.deriv_eq, heq.iteratedDeriv_eq 2] at hsecond
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hderiv, deriv_const,
      zero_mul, zero_div, add_zero] at hsecond
    exact ⟨a, hsecond⟩
  let flatAtlas (σ : HomogeneousCurveJetSection L A1 A2) : ComplexAffineAtlas L :=
    { charts := {c | ∃ hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L,
          ∀ j, curveJet1Base L j ∈ c.source → (curveJet2Coeff L ⟨c, hc⟩ (σ.1 j)).2 = 0}
      cover := by
        intro x
        obtain ⟨d, hxd, hd⟩ := hflatCover σ x
        exact ⟨d.1, ⟨d.2, hd⟩, hxd⟩
      holomorphic := by
        rintro c ⟨hc, _⟩
        exact (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas L c).mpr hc
      compatible := by
        rintro c ⟨hc, hcflat⟩ d ⟨hd, hdflat⟩
        exact hflatCompatible σ ⟨c, hc⟩ ⟨d, hd⟩ hcflat hdflat }
  let inverse (σ : HomogeneousCurveJetSection L A1 A2) : ComplexAffineStructure L :=
    Quotient.mk (complexAffineAtlasSetoid L) (flatAtlas σ)
  have hmaxFlat (σ : HomogeneousCurveJetSection L A1 A2)
      (c : OpenPartialHomeomorph L ℂ) :
      c ∈ ComplexAffineStructure.maximalAtlas L (inverse σ) ↔ c ∈ (flatAtlas σ).charts := by
    rw [show inverse σ = Quotient.mk (complexAffineAtlasSetoid L) (flatAtlas σ) from rfl,
      ComplexAffineStructure.maximalAtlas_eq_of_representative]
    constructor
    · rintro ⟨hc, hcompat⟩
      have hcmax := (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas L c).mp hc
      refine ⟨hcmax, ?_⟩
      intro j hj
      obtain ⟨d, hd, hjd⟩ := (flatAtlas σ).cover (curveJet1Base L j)
      obtain ⟨hdmax, hdflat⟩ := hd
      obtain ⟨a, ha⟩ := hcompatibleSecond ⟨d, hdmax⟩ ⟨c, hcmax⟩
        (hcompat d ⟨hdmax, hdflat⟩) (σ.1 j) ⟨hbase σ j ▸ hjd, hbase σ j ▸ hj⟩
      simpa only [hdflat j hjd, mul_zero] using ha
    · intro hc
      exact ⟨(flatAtlas σ).holomorphic c hc,
        fun d hd ↦ (flatAtlas σ).compatible d hd c hc⟩
  have hinjective : Function.Injective inverse := by
    intro σ τ hστ
    apply Subtype.ext
    funext j
    obtain ⟨c, hc, hjc⟩ := (flatAtlas σ).cover (curveJet1Base L j)
    have hτ : c ∈ (flatAtlas τ).charts :=
      (hmaxFlat τ c).mp (hστ ▸ (hmaxFlat σ c).mpr hc)
    obtain ⟨hcmax, hcflat⟩ := hc
    obtain ⟨_, hτflat⟩ := hτ
    apply ((leaf_jet_complex_manifold L).2.2.2.1 ⟨c, hcmax⟩).2.1.injOn
      (show curveJet2Base L (σ.1 j) ∈ c.source from hbase σ j ▸ hjc)
      (show curveJet2Base L (τ.1 j) ∈ c.source from hbase τ j ▸ hjc)
    exact Prod.ext ((hfirst σ ⟨c, hcmax⟩ j hjc).trans (hfirst τ ⟨c, hcmax⟩ j hjc).symm)
      ((hcflat j hjc).trans (hτflat j hjc).symm)
  have hgraph (σ : HomogeneousCurveJetSection L A1 A2)
      (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ (flatAtlas σ).charts)
      (γ : CurveParamGerm L) (hγ : curveGermBase L γ.1 ∈ c.source) :
      σ.1 (curveJet1Class L γ) = curveJet2Class L γ ↔
        germSecond (γ.1.map (c : L → ℂ)) = 0 := by
    obtain ⟨hcmax, hcflat⟩ := hc
    let d : LeafChart L := ⟨c, hcmax⟩
    have hγdata := (leaf_jet_complex_manifold L).2.1 γ
    have hj : curveJet1Base L (curveJet1Class L γ) ∈ c.source := hγdata.1 ▸ hγ
    have hq : curveJet2Base L (curveJet2Class L γ) ∈ c.source := hγdata.2.1 ▸ hγ
    have hcoeff := (hγdata.2.2.2 d hγ).2.2
    constructor
    · intro heq
      have hzero := hcflat (curveJet1Class L γ) hj
      rw [heq, hcoeff] at hzero
      exact hzero
    · intro hzero
      apply ((leaf_jet_complex_manifold L).2.2.2.1 d).2.1.injOn
        (show curveJet2Base L (σ.1 (curveJet1Class L γ)) ∈ c.source from
          hbase σ _ ▸ hj) hq
      apply Prod.ext
      · rw [hfirst σ d _ hj, hcoeff, (hγdata.2.2.2 d hγ).2.1]
      · rw [hcflat _ hj, hcoeff]
        exact hzero.symm
  have hgraphIff (σ : HomogeneousCurveJetSection L A1 A2)
      (c : OpenPartialHomeomorph L ℂ) :
      c ∈ ComplexAffineStructure.maximalAtlas L (inverse σ) ↔
        IsHolomorphicScalarChart L c ∧ ∀ γ : CurveParamGerm L,
          curveGermBase L γ.1 ∈ c.source →
          (σ.1 (curveJet1Class L γ) = curveJet2Class L γ ↔
            germSecond (γ.1.map (c : L → ℂ)) = 0) := by
    rw [hmaxFlat]
    constructor
    · intro hc
      exact ⟨(flatAtlas σ).holomorphic c hc, hgraph σ c hc⟩
    · rintro ⟨hc, hg⟩
      have hcmax := (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas L c).mp hc
      refine ⟨hcmax, ?_⟩
      exact curve_jet_section_flat_coeff_of_graph L σ ⟨c, hcmax⟩
        (fun γ hγ ↦ (hg γ hγ).mp)
  suffices hsurjective : Function.Surjective inverse by
    classical
    let E := (Equiv.ofBijective inverse ⟨hinjective, hsurjective⟩).symm
    have hE (F : ComplexAffineStructure L) : inverse (E F) = F :=
      (Equiv.ofBijective inverse ⟨hinjective, hsurjective⟩).apply_symm_apply F
    refine ⟨{ equiv := E, affine_parametrization := ?_, flat_chart_iff := ?_ }⟩
    · intro F c hc
      apply hgraph (E F) c
      exact (hmaxFlat (E F) c).mp (by rwa [hE F])
    · intro F c
      simpa only [hE F] using hgraphIff (E F) c
  classical
  intro F
  have hFchart (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ F.out.charts) :
      c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L :=
    (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas L c).mp (F.out.holomorphic c hc)
  have hex (j : CurveJet1 L) : ∃ q : CurveJet2 L,
      curveJet2Base L q = curveJet1Base L j ∧ curveJetTruncation L q = j ∧
      ∀ (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ F.out.charts),
        curveJet1Base L j ∈ c.source →
          (curveJet2Coeff L ⟨c, hFchart c hc⟩ q).2 = 0 := by
    obtain ⟨c, hc, hjc⟩ := F.out.cover (curveJet1Base L j)
    let d : LeafChart L := ⟨c, hFchart c hc⟩
    have hjtarget := ((leaf_jet_complex_manifold L).2.2.2.1 d).1.mapsTo hjc
    obtain ⟨q, hqc, hcoeff⟩ := ((leaf_jet_complex_manifold L).2.2.2.1 d).2.1.surjOn
      (show (curveJet1Coeff L d j, (0 : ℂ)) ∈ curveJet2Target L d from hjtarget)
    have hqbase : curveJet2Base L q = curveJet1Base L j := by
      apply c.injOn hqc hjc
      exact congrArg (fun w : (ℂ × ℂ) × ℂ ↦ w.1.1) hcoeff
    have htrunc : curveJetTruncation L q = j := by
      have ht := ((leaf_jet_complex_manifold L).2.2.2.1 d).2.2 q hqc
      apply ((leaf_jet_complex_manifold L).2.2.2.1 d).1.injOn
        (show curveJet1Base L (curveJetTruncation L q) ∈ c.source from ht.1 ▸ hqc) hjc
      exact ht.2.trans (congrArg Prod.fst hcoeff)
    refine ⟨q, hqbase, htrunc, ?_⟩
    intro e he hje
    obtain ⟨a, ha⟩ := hcompatibleSecond d ⟨e, hFchart e he⟩
      (F.out.compatible c hc e he) q ⟨hqc, hqbase ▸ hje⟩
    simpa only [hcoeff, mul_zero] using ha
  let s : CurveJet1 L → CurveJet2 L := fun j ↦ Classical.choose (hex j)
  have hs (j : CurveJet1 L) := Classical.choose_spec (hex j)
  have hsbase (j : CurveJet1 L) : curveJet2Base L (s j) = curveJet1Base L j := (hs j).1
  have hstrunc (j : CurveJet1 L) : curveJetTruncation L (s j) = j := (hs j).2.1
  have hsflat (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ F.out.charts)
      (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.source) :
      (curveJet2Coeff L ⟨c, hFchart c hc⟩ (s j)).2 = 0 := (hs j).2.2 c hc hj
  have hscoeff (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ F.out.charts)
      (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.source) :
      curveJet2Coeff L ⟨c, hFchart c hc⟩ (s j) =
        (curveJet1Coeff L ⟨c, hFchart c hc⟩ j, 0) := by
    apply Prod.ext
    · have h := (((leaf_jet_complex_manifold L).2.2.2.1 ⟨c, hFchart c hc⟩).2.2
        (s j) (hsbase j ▸ hj)).2
      simpa only [hstrunc j] using h.symm
    · exact hsflat c hc j hj
  let : ChartedSpace (ℂ × ℂ) (CurveJet1 L) := A1
  let : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L) := A2
  have hssmooth : ContMDiff (modelWithCornersSelf ℂ (ℂ × ℂ))
      (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ s := by
    intro j
    obtain ⟨c, hc, hjc⟩ := F.out.cover (curveJet1Base L j)
    let d : LeafChart L := ⟨c, hFchart c hc⟩
    obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2,
      he1smooth, _, _, he2inv⟩ := hAtlases.2.2.1 d
    have hj1 : j ∈ e1.source := by rw [hs1]; exact hjc
    have htarget : (e1 j, (0 : ℂ)) ∈ e2.target := by
      rw [ht2]
      have h := e1.map_source hj1
      rw [ht1] at h
      exact h
    have heq : s =ᶠ[𝓝 j] (fun k ↦ e2.symm (e1 k, (0 : ℂ))) := by
      filter_upwards [e1.open_source.mem_nhds hj1] with k hk
      have hkc : curveJet1Base L k ∈ c.source := by rw [hs1] at hk; exact hk
      have hsk : s k ∈ e2.source := by
        rw [hs2]
        change curveJet2Base L (s k) ∈ c.source
        exact hsbase k ▸ hkc
      have hcoord : e2 (s k) = (e1 k, (0 : ℂ)) := by
        rw [he2 hsk, hscoeff c hc k hkc, he1 hk]
      rw [← hcoord, e2.left_inv hsk]
    have h1 := (he1smooth j hj1).contMDiffAt (e1.open_source.mem_nhds hj1)
    have h2 := (he2inv (e1 j, (0 : ℂ)) htarget).contMDiffAt
      (e2.open_target.mem_nhds htarget)
    have hembed : ContMDiff (modelWithCornersSelf ℂ (ℂ × ℂ))
        (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (fun w : ℂ × ℂ ↦ (w, (0 : ℂ))) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    exact (h2.comp j (hembed.contMDiffAt.comp j h1)).congr_of_eventuallyEq heq
  have hsscale (omega : ℂˣ) (j : CurveJet1 L) :
      s (curveJet1Scale L omega j) = curveJet2Reparametrize L (.scale omega) (s j) := by
    obtain ⟨c, hc, hjc⟩ := F.out.cover (curveJet1Base L j)
    let d : LeafChart L := ⟨c, hFchart c hc⟩
    have hscale1 := (curve_jet_reparametrization L).2.2.2.1 omega j
    have hscale2 := (curve_jet_reparametrization L).2.2.1 (.scale omega) (s j)
    have hjscale : curveJet1Base L (curveJet1Scale L omega j) ∈ c.source := hscale1.1 ▸ hjc
    have hsj : curveJet2Base L (s j) ∈ c.source := hsbase j ▸ hjc
    apply ((leaf_jet_complex_manifold L).2.2.2.1 d).2.1.injOn
      (show curveJet2Base L (s (curveJet1Scale L omega j)) ∈ c.source from hsbase _ ▸ hjscale)
      (show curveJet2Base L (curveJet2Reparametrize L (.scale omega) (s j)) ∈ c.source from
        hscale2.1 ▸ hsj)
    rw [hscoeff c hc _ hjscale, hscale2.2.2 d hsj, hscoeff c hc j hjc,
      hscale1.2 d hjc]
    simp only [CurveJetReparametrization.scale, mul_zero, zero_mul, sub_zero]
    rfl
  let σ : HomogeneousCurveJetSection L A1 A2 := ⟨s, hstrunc, hssmooth, hsscale⟩
  refine ⟨σ, ?_⟩
  apply Eq.trans _ (Quotient.out_eq F)
  apply Quotient.sound
  intro c hc d hd
  exact (flatAtlas σ).compatible c hc d ⟨hFchart d hd, hsflat d hd⟩


end HolomorphicAnosov.Ghys
