import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting
import HolomorphicAnosov.Geometry.UniformExponentialLift.tangent_frame_self
import HolomorphicAnosov.Analysis.CommonBallInverse
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section
set_option maxHeartbeats 1200000
open Set Bundle
open scoped ContDiff Manifold _root_.Topology NNReal
namespace HolomorphicAnosov
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- In a fixed tangent frame, the exponential map has uniformly small two-point error from the
identity near a base point and the zero vector. (Shub, pp. 75–78) -/
theorem local_exponential_frame_approximation
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p₀ : M) (η : ℝ≥0) (hη : 0 < η) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p₀
    let c := chartAt E p₀
    ∃ O : Set M, IsOpen O ∧ p₀ ∈ O ∧ ∃ r : ℝ, 0 < r ∧
      (∀ p ∈ O, p ∈ e.baseSet) ∧
      (∀ p ∈ O, ∀ v ∈ Metric.closedBall (0 : E) r,
        (⟨p, e.symmL ℝ p v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ ExponentialLift.riemannianExpDomain g ∧
        ExponentialLift.riemannianExp g p (e.symmL ℝ p v) ∈ c.source) ∧
      ∀ p ∈ O, ∀ v ∈ Metric.closedBall (0 : E) r,
        ∀ w ∈ Metric.closedBall (0 : E) r,
        ‖c (ExponentialLift.riemannianExp g p (e.symmL ℝ p v)) -
          c (ExponentialLift.riemannianExp g p (e.symmL ℝ p w)) - (v - w)‖ ≤
          η * ‖v - w‖ := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p₀
  let c := chartAt E p₀
  let Z : M × E → TangentBundle 𝓘(ℝ, E) M := fun z ↦ ⟨z.1, e.symmL ℝ z.1 z.2⟩
  let F : M × E → M := fun z ↦ ExponentialLift.riemannianExp g z.1 (e.symmL ℝ z.1 z.2)
  have hpbase : p₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ _
  have hZeq : Z =ᶠ[𝓝 (p₀, (0 : E))] e.toOpenPartialHomeomorph.symm := by
    filter_upwards [(e.open_baseSet.preimage continuous_fst).mem_nhds hpbase] with z hz
    change z.1 ∈ e.baseSet at hz
    rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) z.1 hz]
    simp only [Z, Trivialization.symmL_apply, hz,
      Trivialization.continuousLinearEquivAt_symm_apply]
  have hZ : ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞ Z (p₀, 0) :=
    (e.contMDiffOn_symm.contMDiffAt (e.open_target.mem_nhds (e.mem_target.mpr hpbase))).congr_of_eventuallyEq hZeq
  have hZ0 : Z (p₀, 0) = ⟨p₀, 0⟩ := by simp [Z]
  have hF0 : F (p₀, 0) = p₀ := by
    simpa only [F, map_zero, ExponentialLift.riemannianExp] using (riemannianExponential_zero g p₀).2
  obtain ⟨hD, hExp⟩ := riemannianExponential_open_smooth g
  have hF : ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F (p₀, 0) := by
    have hzD : Z (p₀, 0) ∈ riemannianExponentialDomain g := hZ0 ▸ (riemannianExponential_zero g p₀).1
    exact (hExp.contMDiffAt (hD.mem_nhds hzD)).comp (p₀, 0) hZ
  let q : E × E → E := fun z ↦ c (F (c.symm z.1, z.2))
  have hq : ContDiffAt ℝ ∞ q (c p₀, 0) := by
    have hh := (contMDiffAt_iff.mp hF).2
    simpa only [hF0, extChartAt_prod, extChartAt_model_space_eq_id,
      PartialEquiv.prod_coe_symm, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, PartialEquiv.prod_coe, Function.comp_def, id_eq,
      ModelWithCorners.range_prod, range_id, univ_prod_univ,
      contDiffWithinAt_univ, q, c] using hh
  let D := fderiv ℝ q (c p₀, 0)
  have hstrict : HasStrictFDerivAt q D (c p₀, 0) := hq.hasStrictFDerivAt (by simp)
  let ep : E → M := fun v ↦ riemannianExponential g
    ⟨p₀, (tangentSpaceCastModel 𝓘(ℝ, E) p₀).symm v⟩
  have hep : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 :=
    (riemannianExponential_fibre_contMDiffAt_zero g p₀).mdifferentiableAt (by simp)
  have hep0 : ep 0 = p₀ := by simpa only [ep, map_zero] using (riemannianExponential_zero g p₀).2
  have hdep : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 = ContinuousLinearMap.id ℝ E := by
    ext w
    exact riemannianExponential_vertical_derivative g p₀ hep w
  have hepc : HasFDerivAt (fun v ↦ c (ep v)) (ContinuousLinearMap.id ℝ E) 0 := by
    have hh := hep.hasMFDerivAt.2
    simp only [hep0, hdep, writtenInExtChartAt, extChartAt_model_space_eq_id,
      extChartAt_coe, modelWithCornersSelf_coe, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_def, id_eq, range_id,
      hasFDerivWithinAt_univ] at hh
    exact hh
  have hqbase : (fun v ↦ q (c p₀, v)) = fun v ↦ c (ep v) := by
    funext v
    dsimp only [q, F]
    rw [c.left_inv (mem_chart_source E p₀)]
    rw [show e.symmL ℝ p₀ = (tangentSpaceCastModel 𝓘(ℝ, E) p₀).symm.toContinuousLinearMap
      from (ExponentialLift.tangent_frame_self p₀).1]
    rfl
  have hvertical (v : E) : D (0, v) = v := by
    have hh := hstrict.hasFDerivAt.comp 0
      ((hasFDerivAt_const (c p₀) (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
    change HasFDerivAt (fun v ↦ q (c p₀, v)) _ 0 at hh
    rw [hqbase] at hh
    have he := hh.unique hepc
    exact DFunLike.congr_fun he v
  obtain ⟨A, hA, happ⟩ := hstrict.approximates_deriv_on_nhds (Or.inr hη)
  have hcoord : ContinuousAt (fun z : M × E ↦ (c z.1, z.2)) (p₀, 0) :=
    ((c.continuousAt (mem_chart_source E p₀)).comp continuousAt_fst).prodMk continuousAt_snd
  have hgood : {z : M × E | Z z ∈ riemannianExponentialDomain g ∧ F z ∈ c.source ∧
      z.1 ∈ e.baseSet ∧ z.1 ∈ c.source ∧ (c z.1, z.2) ∈ A} ∈ 𝓝 (p₀, 0) := by
    have hzD : Z (p₀, 0) ∈ riemannianExponentialDomain g := hZ0 ▸ (riemannianExponential_zero g p₀).1
    filter_upwards [hZ.continuousAt.preimage_mem_nhds (hD.mem_nhds hzD),
      hF.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds (by rw [hF0]; exact mem_chart_source E p₀)),
      (e.open_baseSet.preimage continuous_fst).mem_nhds hpbase,
      (c.open_source.preimage continuous_fst).mem_nhds (mem_chart_source E p₀),
      hcoord.preimage_mem_nhds hA] with z hz₁ hz₂ hz₃ hz₄ hz₅
    exact ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨O, hOV, hO, hpO⟩ := mem_nhds_iff.mp hV
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hwW (w : E) (hw : w ∈ Metric.closedBall (0 : E) r) : w ∈ W :=
    hεW ((Metric.closedBall_subset_ball (by dsimp [r]; linarith)) hw)
  have hcontrol (p : M) (hp : p ∈ O) (v : E) (hv : v ∈ Metric.closedBall (0 : E) r) :=
    hVW (a := (p, v)) ⟨hOV hp, hwW v hv⟩
  refine ⟨O, hO, hpO, r, hr, ?_, ?_, ?_⟩
  · intro p hp
    exact (hcontrol p hp 0 (Metric.mem_closedBall_self hr.le)).2.2.1
  · intro p hp v hv
    exact ⟨(hcontrol p hp v hv).1, (hcontrol p hp v hv).2.1⟩
  · intro p hp v hv w hw
    have hv' := hcontrol p hp v hv
    have hw' := hcontrol p hp w hw
    have hh := happ (c p, v) hv'.2.2.2.2 (c p, w) hw'.2.2.2.2
    have hsub : (c p, v) - (c p, w) = ((0 : E), v - w) := by simp
    rw [hsub, hvertical] at hh
    dsimp only [q] at hh
    rw [c.left_inv hv'.2.2.2.1] at hh
    simpa only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), F] using hh

omit [FiniteDimensional ℝ E] in
private theorem composed_graph_error_g9
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j j₀ : V →L[ℝ] E) (q : E → E) (v w : V) (gv gw : E)
    (B δ ε : ℝ) (hε : 0 ≤ ε) (hj : ‖j‖ ≤ B) (hj₀ : ‖j - j₀‖ ≤ δ)
    (hg : ‖gv - gw - j (v - w)‖ ≤ δ * ‖v - w‖)
    (hq : ‖q gv - q gw - (gv - gw)‖ ≤ ε * ‖gv - gw‖)
    (he : ε * (B + δ) ≤ δ) :
    ‖q gv - q gw - j₀ (v - w)‖ ≤ 3 * δ * ‖v - w‖ := by
  have hdiff : ‖gv - gw‖ ≤ (B + δ) * ‖v - w‖ := by
    calc
      _ ≤ ‖gv - gw - j (v - w)‖ + ‖j (v - w)‖ := norm_le_norm_sub_add _ _
      _ ≤ δ * ‖v - w‖ + B * ‖v - w‖ := add_le_add hg
        ((j.le_opNorm _).trans (mul_le_mul_of_nonneg_right hj (norm_nonneg _)))
      _ = _ := by ring
  have hlin : ‖(j - j₀) (v - w)‖ ≤ δ * ‖v - w‖ :=
    ((j - j₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right hj₀ (norm_nonneg _))
  calc
    _ = ‖(q gv - q gw - (gv - gw)) + (gv - gw - j (v - w)) + (j - j₀) (v - w)‖ := by
      congr 1; simp only [sub_apply]; abel
    _ ≤ ‖q gv - q gw - (gv - gw)‖ + ‖gv - gw - j (v - w)‖ + ‖(j - j₀) (v - w)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε * ((B + δ) * ‖v - w‖) + δ * ‖v - w‖ + δ * ‖v - w‖ :=
      add_le_add (add_le_add (hq.trans (mul_le_mul_of_nonneg_left hdiff hε)) hg) hlin
    _ ≤ δ * ‖v - w‖ + δ * ‖v - w‖ + δ * ‖v - w‖ := by
      rw [← mul_assoc]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right he (norm_nonneg (v - w))) le_rfl) le_rfl
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
private theorem linear_graph_perturbation_g9
    {V A U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (s : V →L[ℝ] A) (b : U →L[ℝ] E) (μ : A → U)
    (B δ a r : ℝ) (η : ℝ≥0) (hB : 0 ≤ B) (ha : 0 < a)
    (hb : ‖b‖ ≤ B) (hs : ∀ v, ‖s v‖ ≤ B * B * ‖v‖)
    (har : B * B * a < r) (hη1 : (η : ℝ) ≤ 1)
    (hηδ : B * ((η : ℝ) * (B * B)) ≤ δ)
    (hμ0 : μ 0 = 0) (hμ : LipschitzOnWith η μ (Metric.ball 0 r)) :
    ∀ v ∈ Metric.closedBall (0 : V) a,
      ‖s v‖ < r ∧ ‖s v‖ + ‖μ (s v)‖ ≤ 2 * (B * B) * ‖v‖ ∧
      ∀ w ∈ Metric.closedBall (0 : V) a,
        ‖b (μ (s v)) - b (μ (s w))‖ ≤ δ * ‖v - w‖ := by
  have hsr (v : V) (hv : v ∈ Metric.closedBall (0 : V) a) : ‖s v‖ < r := by
    have hn : ‖v‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    exact (hs v).trans_lt ((mul_le_mul_of_nonneg_left hn (mul_nonneg hB hB)).trans_lt har)
  have hsmem (v : V) (hv : v ∈ Metric.closedBall (0 : V) a) : s v ∈ Metric.ball 0 r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hsr v hv
  intro v hv
  refine ⟨hsr v hv, ?_, ?_⟩
  · have hh := hμ.dist_le_mul (s v) (hsmem v hv) (s 0) (hsmem 0 (Metric.mem_closedBall_self ha.le))
    simp only [map_zero, hμ0, dist_zero_right] at hh
    have hsmall : ‖μ (s v)‖ ≤ ‖s v‖ := hh.trans (by nlinarith only [hη1, norm_nonneg (s v)])
    nlinarith only [hs v, hsmall]
  · intro w hw
    have hh := hμ.dist_le_mul (s v) (hsmem v hv) (s w) (hsmem w hw)
    simp only [dist_eq_norm, ← map_sub] at hh
    calc
      _ = ‖b (μ (s v) - μ (s w))‖ := by rw [map_sub]
      _ ≤ B * ‖μ (s v) - μ (s w)‖ :=
        (b.le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      _ ≤ B * ((η : ℝ) * (B * B * ‖v - w‖)) :=
        mul_le_mul_of_nonneg_left (hh.trans
          (mul_le_mul_of_nonneg_left (hs (v - w)) η.coe_nonneg)) hB
      _ = (B * ((η : ℝ) * (B * B))) * ‖v - w‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hηδ (norm_nonneg _)

/-- Centered native graphs with uniformly vanishing local Lipschitz slopes over complementary
continuous tangent bundles intersect near each diagonal pair. (Shub, pp. 75–78;
Fisher–Hasselblatt, Prop. 12.1.3, pp. 578–579) -/
theorem native_small_graph_intersection
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {Λ : Set M} (S U : ContinuousTangentSubbundleOn (E := E) Λ)
    (hc : ∀ x, IsCompl (S.fibre x) (U.fibre x)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
    ∀ (μs : (x : Λ) → S.fibre x → U.fibre x)
      (μu : (x : Λ) → U.fibre x → S.fibre x),
      (∀ x, μs x 0 = 0) → (∀ x, μu x 0 = 0) →
      (∀ η : ℝ≥0, 0 < η → ∃ r : ℝ, 0 < r ∧
        ∀ x, LipschitzOnWith η (μs x) (Metric.ball 0 r)) →
      (∀ η : ℝ≥0, 0 < η → ∃ r : ℝ, 0 < r ∧
        ∀ x, LipschitzOnWith η (μu x) (Metric.ball 0 r)) →
      ∀ (p₀ : Λ) (ρ : ℝ), 0 < ρ → ∃ O : Set Λ, IsOpen O ∧ p₀ ∈ O ∧
        ∀ x ∈ O, ∀ y ∈ O, ∃ s : S.fibre x, ∃ u : U.fibre y,
          ‖s‖ < ρ ∧ ‖u‖ < ρ ∧
          ‖((s : TangentSpace 𝓘(ℝ, E) x.val) + μs x s)‖ < ρ ∧
          ‖((u : TangentSpace 𝓘(ℝ, E) y.val) + μu y u)‖ < ρ ∧
          riemannianExponential g ⟨x.val, (s : TangentSpace 𝓘(ℝ, E) x.val) + μs x s⟩ =
            riemannianExponential g ⟨y.val, (u : TangentSpace 𝓘(ℝ, E) y.val) + μu y u⟩ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let : (x : M) → NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  let : (x : M) → InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := fun x ↦ inferInstance
  intro μs μu hμs0 hμu0 hμs hμu p₀ ρ hρ
  let : (x : Λ) → NormedAddCommGroup (S.fibre x) := fun x ↦ inferInstance
  let : (x : Λ) → NormedSpace ℝ (S.fibre x) := fun x ↦ inferInstance
  let : (x : Λ) → NormedAddCommGroup (U.fibre x) := fun x ↦ inferInstance
  let : (x : Λ) → NormedSpace ℝ (U.fibre x) := fun x ↦ inferInstance
  obtain ⟨r, Os, hOs, hps, a, hae, ha, hsO, js, hjs, hjsinj, hjsrange⟩ :=
    HirschRestrictedCoordinates.exists_restricted_coordinate_frame S p₀
  obtain ⟨t, Ou, hOu, hpu, b, hbe, hb, huO, ju, hju, hjuinj, hjurange⟩ :=
    HirschRestrictedCoordinates.exists_restricted_coordinate_frame U p₀
  subst a
  subst b
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p₀.val
  let c := chartAt E p₀.val
  let V := Os ∩ Ou
  let p : V := ⟨p₀, hps, hpu⟩
  let fs : V → Os := fun x ↦ ⟨x.val, x.property.1⟩
  let fu : V → Ou := fun x ↦ ⟨x.val, x.property.2⟩
  let js' := js ∘ fs
  let ju' := ju ∘ fu
  have hjs' : Continuous js' := hjs.comp (continuous_subtype_val.subtype_mk _)
  have hju' : Continuous ju' := hju.comp (continuous_subtype_val.subtype_mk _)
  have hcomp : IsCompl (js' p).toLinearMap.range (ju' p).toLinearMap.range := by
    dsimp only [js', ju', Function.comp_apply]
    rw [hjsrange (fs p), hjurange (fu p)]
    exact Submodule.isCompl_map (e.linearEquivAt ℝ p₀.val (hsO p₀ hps)) (hc p₀)
  obtain ⟨L, hL⟩ : ∃ L : ((Fin r → ℝ) × (Fin t → ℝ)) ≃L[ℝ] E,
      ∀ z, L z = js' p z.1 - ju' p z.2 := by
    let L : ((Fin r → ℝ) × (Fin t → ℝ)) ≃L[ℝ] E :=
      (((LinearEquiv.refl ℝ (Fin r → ℝ)).prodCongr (LinearEquiv.neg ℝ)).trans
        (((LinearEquiv.ofInjective (js' p).toLinearMap (hjsinj (fs p))).prodCongr
          (LinearEquiv.ofInjective (ju' p).toLinearMap (hjuinj (fu p)))).trans
            (Submodule.prodEquivOfIsCompl _ _ hcomp))).toContinuousLinearEquiv
    refine ⟨L, ?_⟩
    intro z
    change js' p z.1 + ju' p (-z.2) = _
    rw [map_neg, sub_eq_add_neg]
  obtain ⟨C, hC, hCbound⟩ := eventually_norm_trivializationAt_lt E (TangentSpace 𝓘(ℝ, E)) p₀.val
  obtain ⟨D, hD, hDbound⟩ := eventually_norm_symmL_trivializationAt_lt E (TangentSpace 𝓘(ℝ, E)) p₀.val
  let B := 2 + C + D + ‖js' p‖ + ‖ju' p‖
  have hB : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg (js' p), norm_nonneg (ju' p)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hCB : C ≤ B := by dsimp [B]; linarith [norm_nonneg (js' p), norm_nonneg (ju' p)]
  have hDB : D ≤ B := by dsimp [B]; linarith [norm_nonneg (js' p), norm_nonneg (ju' p)]
  let K := ‖L.symm.toContinuousLinearMap‖
  have hK : 0 ≤ K := norm_nonneg _
  let δ := 1 / (16 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_iff₀ (by positivity)]; nlinarith only [hK]
  let η : ℝ≥0 := ⟨δ / (B * B * B + 1), by positivity⟩
  have hη : 0 < η := by change 0 < δ / (B * B * B + 1); positivity
  have hη1 : (η : ℝ) ≤ 1 := by
    change δ / (B * B * B + 1) ≤ 1
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hδ1, mul_nonneg (mul_nonneg hB0.le hB0.le) hB0.le]
  obtain ⟨rs, hrs, hμsLip⟩ := hμs η hη
  obtain ⟨ru, hru, hμuLip⟩ := hμu η hη
  let ε : ℝ≥0 := ⟨δ / (B + 1), by positivity⟩
  have hε : 0 < ε := by change 0 < δ / (B + 1); positivity
  obtain ⟨N, hN, hpN, R, hR, hNbase, hNdomain, hNapprox⟩ :=
    local_exponential_frame_approximation g p₀.val ε hε
  have hbase (x : V) : x.val.val ∈ e.baseSet := hsO _ x.property.1
  have hsmem (x : V) (v : Fin r → ℝ) :
      e.symmL ℝ x.val.val (js' x v) ∈ S.fibre x.val := by
    have hh : js' x v ∈ (S.fibre x.val).map
        (e.linearEquivAt ℝ x.val.val (hbase x)).toLinearMap := by
      rw [← hjsrange (fs x)]
      exact ⟨v, rfl⟩
    have hh' := (Submodule.mem_map_equiv (S.fibre x.val)).mp hh
    simpa only [Trivialization.linearEquivAt_symm_apply,
      Trivialization.symmL_apply, hbase x] using hh'
  have humem (x : V) (v : Fin t → ℝ) :
      e.symmL ℝ x.val.val (ju' x v) ∈ U.fibre x.val := by
    have hh : ju' x v ∈ (U.fibre x.val).map
        (e.linearEquivAt ℝ x.val.val (hbase x)).toLinearMap := by
      rw [← hjurange (fu x)]
      exact ⟨v, rfl⟩
    have hh' := (Submodule.mem_map_equiv (U.fibre x.val)).mp hh
    simpa only [Trivialization.linearEquivAt_symm_apply,
      Trivialization.symmL_apply, hbase x] using hh'
  obtain ⟨ss, hssval⟩ : ∃ ss : (x : V) → (Fin r → ℝ) →L[ℝ] S.fibre x.val,
      ∀ x v, (ss x v : TangentSpace 𝓘(ℝ, E) x.val.val) = e.symmL ℝ x.val.val (js' x v) := by
    refine ⟨fun x ↦ ((e.symmL ℝ x.val.val).comp (js' x)).codRestrict _ (hsmem x), ?_⟩
    intro x v
    rfl
  obtain ⟨uu, huuval⟩ : ∃ uu : (x : V) → (Fin t → ℝ) →L[ℝ] U.fibre x.val,
      ∀ x v, (uu x v : TangentSpace 𝓘(ℝ, E) x.val.val) = e.symmL ℝ x.val.val (ju' x v) := by
    refine ⟨fun x ↦ ((e.symmL ℝ x.val.val).comp (ju' x)).codRestrict _ (humem x), ?_⟩
    intro x v
    rfl
  have hbcont : Continuous (fun x : V ↦ x.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnear : {x : V | x.val.val ∈ N ∧ ‖e.continuousLinearMapAt ℝ x.val.val‖ ≤ B ∧
      ‖e.symmL ℝ x.val.val‖ ≤ B ∧ ‖js' x - js' p‖ ≤ δ ∧ ‖ju' x - ju' p‖ ≤ δ ∧
      ‖js' x‖ ≤ B ∧ ‖ju' x‖ ≤ B} ∈ 𝓝 p := by
    have hsc : ContinuousAt (fun x : V ↦ ‖js' x - js' p‖) p :=
      (hjs'.continuousAt.sub continuousAt_const).norm
    have huc : ContinuousAt (fun x : V ↦ ‖ju' x - ju' p‖) p :=
      (hju'.continuousAt.sub continuousAt_const).norm
    have hsn := hsc.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))
    have hun := huc.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))
    filter_upwards [hbcont.continuousAt.preimage_mem_nhds (hN.mem_nhds hpN),
      hbcont.continuousAt.tendsto.eventually hCbound,
      hbcont.continuousAt.tendsto.eventually hDbound, hsn, hun] with x hx hxc hxd hxs hxu
    refine ⟨hx, hxc.le.trans hCB, hxd.le.trans hDB, hxs.le, hxu.le, ?_, ?_⟩
    · have hh := norm_le_norm_sub_add (js' x) (js' p)
      dsimp [B]
      linarith [norm_nonneg (ju' p)]
    · have hh := norm_le_norm_sub_add (ju' x) (ju' p)
      dsimp [B]
      linarith [norm_nonneg (js' p)]
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hnear
  let T := B * B + 1
  have hT : 0 < T := by dsimp [T]; positivity
  let a := min (R / (B + 1)) (min (rs / T) (min (ru / T) (ρ / (2 * T)))) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have haR : (B + 1) * a ≤ R := by
    have hh : a < R / (B + 1) := by
      have hi := min_le_left (R / (B + 1)) (min (rs / T) (min (ru / T) (ρ / (2 * T))))
      dsimp [a] at *
      linarith only [ha, hi]
    exact ((lt_div_iff₀' (by positivity)).mp hh).le
  have hars : B * B * a < rs := by
    have hh : a < rs / T := by
      have hi := (min_le_right (R / (B + 1)) (min (rs / T) (min (ru / T) (ρ / (2 * T))))).trans
        (min_le_left _ _)
      dsimp [a] at *
      linarith only [ha, hi]
    have ht := (lt_div_iff₀' hT).mp hh
    dsimp [T] at ht
    nlinarith only [ht, ha]
  have haru : B * B * a < ru := by
    have hh : a < ru / T := by
      have hi := (min_le_right (R / (B + 1)) (min (rs / T) (min (ru / T) (ρ / (2 * T))))).trans
        ((min_le_right _ _).trans (min_le_left _ _))
      dsimp [a] at *
      linarith only [ha, hi]
    have ht := (lt_div_iff₀' hT).mp hh
    dsimp [T] at ht
    nlinarith only [ht, ha]
  have haρ : 2 * (B * B) * a < ρ := by
    have hh : a < ρ / (2 * T) := by
      have hi := (min_le_right (R / (B + 1)) (min (rs / T) (min (ru / T) (ρ / (2 * T))))).trans
        ((min_le_right _ _).trans (min_le_right _ _))
      dsimp [a] at *
      linarith only [ha, hi]
    have ht := (lt_div_iff₀' (by positivity : 0 < 2 * T)).mp hh
    dsimp [T] at ht
    nlinarith only [ht, ha]
  have hηδ : B * ((η : ℝ) * (B * B)) ≤ δ := by
    have he : (η : ℝ) * (B * B * B + 1) = δ :=
      div_mul_cancel₀ δ (by positivity)
    nlinarith only [he, η.coe_nonneg]
  have hεδ : (ε : ℝ) * (B + δ) ≤ δ := by
    have he : (ε : ℝ) * (B + 1) = δ := div_mul_cancel₀ δ (by positivity)
    nlinarith only [he, ε.coe_nonneg, hδ1]
  obtain ⟨bs, hbsval⟩ : ∃ bs : (x : V) → U.fibre x.val →L[ℝ] E,
      ∀ x v, bs x v = e.continuousLinearMapAt ℝ x.val.val v.val := by
    exact ⟨fun x ↦ (e.continuousLinearMapAt ℝ x.val.val).comp (U.fibre x.val).subtypeL,
      fun _ _ ↦ rfl⟩
  obtain ⟨bu, hbuval⟩ : ∃ bu : (x : V) → S.fibre x.val →L[ℝ] E,
      ∀ x v, bu x v = e.continuousLinearMapAt ℝ x.val.val v.val := by
    exact ⟨fun x ↦ (e.continuousLinearMapAt ℝ x.val.val).comp (S.fibre x.val).subtypeL,
      fun _ _ ↦ rfl⟩
  have hbss (x : V) (hx : x ∈ W) : ‖bs x‖ ≤ B := by
    apply (bs x).opNorm_le_bound hB0.le
    intro v
    rw [hbsval]
    exact ((e.continuousLinearMapAt ℝ x.val.val).le_opNorm v.val).trans
      (mul_le_mul_of_nonneg_right (hWsub hx).2.1 (norm_nonneg _))
  have hbuu (x : V) (hx : x ∈ W) : ‖bu x‖ ≤ B := by
    apply (bu x).opNorm_le_bound hB0.le
    intro v
    rw [hbuval]
    exact ((e.continuousLinearMapAt ℝ x.val.val).le_opNorm v.val).trans
      (mul_le_mul_of_nonneg_right (hWsub hx).2.1 (norm_nonneg _))
  have hss (x : V) (hx : x ∈ W) (v : Fin r → ℝ) : ‖ss x v‖ ≤ B * B * ‖v‖ := by
    change ‖(ss x v : TangentSpace 𝓘(ℝ, E) x.val.val)‖ ≤ _
    rw [hssval]
    calc
      _ ≤ B * ‖js' x v‖ := ((e.symmL ℝ x.val.val).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hWsub hx).2.2.1 (norm_nonneg _))
      _ ≤ B * (B * ‖v‖) := mul_le_mul_of_nonneg_left
        (((js' x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hWsub hx).2.2.2.2.2.1 (norm_nonneg _))) hB0.le
      _ = _ := by ring
  have huu (x : V) (hx : x ∈ W) (v : Fin t → ℝ) : ‖uu x v‖ ≤ B * B * ‖v‖ := by
    change ‖(uu x v : TangentSpace 𝓘(ℝ, E) x.val.val)‖ ≤ _
    rw [huuval]
    calc
      _ ≤ B * ‖ju' x v‖ := ((e.symmL ℝ x.val.val).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hWsub hx).2.2.1 (norm_nonneg _))
      _ ≤ B * (B * ‖v‖) := mul_le_mul_of_nonneg_left
        (((ju' x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hWsub hx).2.2.2.2.2.2 (norm_nonneg _))) hB0.le
      _ = _ := by ring
  have hsgraph (x : V) (hx : x ∈ W) := linear_graph_perturbation_g9
    (ss x) (bs x) (μs x.val) B δ a rs η hB0.le ha (hbss x hx) (hss x hx)
      hars hη1 hηδ (hμs0 x.val) (hμsLip x.val)
  have hugraph (x : V) (hx : x ∈ W) := linear_graph_perturbation_g9
    (uu x) (bu x) (μu x.val) B δ a ru η hB0.le ha (hbuu x hx) (huu x hx)
      haru hη1 hηδ (hμu0 x.val) (hμuLip x.val)
  let gs (x : V) (v : Fin r → ℝ) := js' x v + bs x (μs x.val (ss x v))
  let gu (x : V) (v : Fin t → ℝ) := ju' x v + bu x (μu x.val (uu x v))
  have hgs0 (x : V) : gs x 0 = 0 := by simp only [gs, map_zero, hμs0, add_zero]
  have hgu0 (x : V) : gu x 0 = 0 := by simp only [gu, map_zero, hμu0, add_zero]
  have hgsdiff (x : V) (hx : x ∈ W) (v : Fin r → ℝ) (hv : v ∈ Metric.closedBall 0 a)
      (w : Fin r → ℝ) (hw : w ∈ Metric.closedBall 0 a) :
      ‖gs x v - gs x w - js' x (v - w)‖ ≤ δ * ‖v - w‖ := by
    have he : gs x v - gs x w - js' x (v - w) =
        bs x (μs x.val (ss x v)) - bs x (μs x.val (ss x w)) := by
      dsimp [gs]; rw [map_sub]; abel
    rw [he]
    exact (hsgraph x hx v hv).2.2 w hw
  have hgudiff (x : V) (hx : x ∈ W) (v : Fin t → ℝ) (hv : v ∈ Metric.closedBall 0 a)
      (w : Fin t → ℝ) (hw : w ∈ Metric.closedBall 0 a) :
      ‖gu x v - gu x w - ju' x (v - w)‖ ≤ δ * ‖v - w‖ := by
    have he : gu x v - gu x w - ju' x (v - w) =
        bu x (μu x.val (uu x v)) - bu x (μu x.val (uu x w)) := by
      dsimp [gu]; rw [map_sub]; abel
    rw [he]
    exact (hugraph x hx v hv).2.2 w hw
  have hgsnorm (x : V) (hx : x ∈ W) (v : Fin r → ℝ) (hv : v ∈ Metric.closedBall 0 a) :
      ‖gs x v‖ ≤ (B + δ) * ‖v‖ := by
    have hh := hgsdiff x hx v hv 0 (Metric.mem_closedBall_self ha.le)
    rw [hgs0, sub_zero, sub_zero] at hh
    have hj := ((js' x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hWsub hx).2.2.2.2.2.1 (norm_nonneg v))
    have ht := norm_le_norm_sub_add (gs x v) (js' x v)
    nlinarith only [hh, hj, ht]
  have hgunorm (x : V) (hx : x ∈ W) (v : Fin t → ℝ) (hv : v ∈ Metric.closedBall 0 a) :
      ‖gu x v‖ ≤ (B + δ) * ‖v‖ := by
    have hh := hgudiff x hx v hv 0 (Metric.mem_closedBall_self ha.le)
    rw [hgu0, sub_zero, sub_zero] at hh
    have hj := ((ju' x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hWsub hx).2.2.2.2.2.2 (norm_nonneg v))
    have ht := norm_le_norm_sub_add (gu x v) (ju' x v)
    nlinarith only [hh, hj, ht]
  have hgsR (x : V) (hx : x ∈ W) (v : Fin r → ℝ) (hv : v ∈ Metric.closedBall 0 a) :
      gs x v ∈ Metric.closedBall (0 : E) R := by
    have hn : ‖v‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact (hgsnorm x hx v hv).trans
      ((mul_le_mul (by linarith only [hδ1] : B + δ ≤ B + 1) hn
        (norm_nonneg v) (by positivity)).trans haR)
  have hguR (x : V) (hx : x ∈ W) (v : Fin t → ℝ) (hv : v ∈ Metric.closedBall 0 a) :
      gu x v ∈ Metric.closedBall (0 : E) R := by
    have hn : ‖v‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact (hgunorm x hx v hv).trans
      ((mul_le_mul (by linarith only [hδ1] : B + δ ≤ B + 1) hn
        (norm_nonneg v) (by positivity)).trans haR)
  let q (x : V) (v : E) := c (ExponentialLift.riemannianExp g x.val.val (e.symmL ℝ x.val.val v))
  have hqs (x : V) (hx : x ∈ W) (v : Fin r → ℝ) (hv : v ∈ Metric.closedBall 0 a)
      (w : Fin r → ℝ) (hw : w ∈ Metric.closedBall 0 a) :
      ‖q x (gs x v) - q x (gs x w) - js' p (v - w)‖ ≤ 3 * δ * ‖v - w‖ :=
    composed_graph_error_g9 (js' x) (js' p) (q x) v w (gs x v) (gs x w) B δ ε
      ε.coe_nonneg (hWsub hx).2.2.2.2.2.1 (hWsub hx).2.2.2.1 (hgsdiff x hx v hv w hw)
      (hNapprox x.val.val (hWsub hx).1 (gs x v) (hgsR x hx v hv) (gs x w) (hgsR x hx w hw)) hεδ
  have hqu (x : V) (hx : x ∈ W) (v : Fin t → ℝ) (hv : v ∈ Metric.closedBall 0 a)
      (w : Fin t → ℝ) (hw : w ∈ Metric.closedBall 0 a) :
      ‖q x (gu x v) - q x (gu x w) - ju' p (v - w)‖ ≤ 3 * δ * ‖v - w‖ :=
    composed_graph_error_g9 (ju' x) (ju' p) (q x) v w (gu x v) (gu x w) B δ ε
      ε.coe_nonneg (hWsub hx).2.2.2.2.2.2 (hWsub hx).2.2.2.2.1 (hgudiff x hx v hv w hw)
      (hNapprox x.val.val (hWsub hx).1 (gu x v) (hguR x hx v hv) (gu x w) (hguR x hx w hw)) hεδ
  let X := (Fin r → ℝ) × (Fin t → ℝ)
  have hfst (z : X) (hz : z ∈ Metric.closedBall 0 a) : z.1 ∈ Metric.closedBall 0 a := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact (norm_fst_le z).trans hz
  have hsnd (z : X) (hz : z ∈ Metric.closedBall 0 a) : z.2 ∈ Metric.closedBall 0 a := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact (norm_snd_le z).trans hz
  let F (x y : V) (z : X) := q x (gs x z.1) - q y (gu y z.2)
  have hFerror (x : V) (hx : x ∈ W) (y : V) (hy : y ∈ W)
      (v : X) (hv : v ∈ Metric.closedBall 0 a) (w : X) (hw : w ∈ Metric.closedBall 0 a) :
      ‖F x y v - F x y w - L (v - w)‖ ≤ 6 * δ * ‖v - w‖ := by
    have hs := hqs x hx v.1 (hfst v hv) w.1 (hfst w hw)
    have hu := hqu y hy v.2 (hsnd v hv) w.2 (hsnd w hw)
    have he : F x y v - F x y w - L (v - w) =
        (q x (gs x v.1) - q x (gs x w.1) - js' p (v.1 - w.1)) -
        (q y (gu y v.2) - q y (gu y w.2) - ju' p (v.2 - w.2)) := by
      rw [hL]; dsimp only [F, Prod.fst_sub, Prod.snd_sub]; abel
    rw [he]
    calc
      _ ≤ ‖q x (gs x v.1) - q x (gs x w.1) - js' p (v.1 - w.1)‖ +
          ‖q y (gu y v.2) - q y (gu y w.2) - ju' p (v.2 - w.2)‖ := norm_sub_le _ _
      _ ≤ 3 * δ * ‖v.1 - w.1‖ + 3 * δ * ‖v.2 - w.2‖ := add_le_add hs hu
      _ ≤ 3 * δ * ‖v - w‖ + 3 * δ * ‖v - w‖ := add_le_add
        (mul_le_mul_of_nonneg_left (norm_fst_le (v - w)) (by positivity))
        (mul_le_mul_of_nonneg_left (norm_snd_le (v - w)) (by positivity))
      _ = _ := by ring
  have hKδ : K * (6 * δ) ≤ (1 / 2 : ℝ) := by
    have he : δ * (16 * (K + 1)) = 1 := div_mul_cancel₀ 1 (by positivity)
    nlinarith only [he, hδ.le]
  let H (x y : V) (v : X) := L.symm (F x y v)
  have hHerror (x : V) (hx : x ∈ W) (y : V) (hy : y ∈ W)
      (v : X) (hv : v ∈ Metric.closedBall 0 a) (w : X) (hw : w ∈ Metric.closedBall 0 a) :
      ‖H x y v - H x y w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖ := by
    have he : H x y v - H x y w - (v - w) =
        L.symm (F x y v - F x y w - L (v - w)) := by
      simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply, H]
    rw [he]
    calc
      _ ≤ K * ‖F x y v - F x y w - L (v - w)‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K * (6 * δ * ‖v - w‖) := mul_le_mul_of_nonneg_left (hFerror x hx y hy v hv w hw) hK
      _ = (K * (6 * δ)) * ‖v - w‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKδ (norm_nonneg _)
  have hq0 (x : V) : q x 0 = c x.val.val := by
    dsimp only [q]
    rw [map_zero]
    exact congrArg c (riemannianExponential_zero g x.val.val).2
  have hH0 (x y : V) : H x y 0 = L.symm (c x.val.val - c y.val.val) := by
    simp only [H, F, Prod.fst_zero, Prod.snd_zero, hgs0, hgu0, hq0]
  have hcp : ContinuousAt (fun x : V ↦ c x.val.val) p :=
    (c.continuousAt (mem_chart_source E p₀.val)).comp
      (f := fun x : V ↦ x.val.val) (x := p) hbcont.continuousAt
  have hcenter : ContinuousAt (fun z : V × V ↦ L.symm (c z.1.val.val - c z.2.val.val)) (p, p) :=
    L.symm.continuous.continuousAt.comp
      ((hcp.comp (f := fun z : V × V ↦ z.1) (x := (p, p)) continuousAt_fst).sub
        (hcp.comp (f := fun z : V × V ↦ z.2) (x := (p, p)) continuousAt_snd))
  have hcenternear : {z : V × V | ‖L.symm (c z.1.val.val - c z.2.val.val)‖ < a / 8} ∈
      𝓝 (p, p) := hcenter.norm.eventually
        (gt_mem_nhds (by simpa only [sub_self, map_zero, norm_zero] using (by positivity : (0 : ℝ) < a / 8)))
  obtain ⟨N₁, hN₁, N₂, hN₂, hN₁₂⟩ := mem_nhds_prod_iff.mp hcenternear
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hW.mem_nhds hpW) (Filter.inter_mem hN₁ hN₂))
  refine ⟨Subtype.val '' O, (hOs.inter hOu).isOpenMap_subtype_val _ hO, ⟨p, hpO, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxW := (hOsub hx).1
  have hyW := (hOsub hy).1
  have hoff : ‖H x y 0‖ < a / 8 := by
    rw [hH0]
    exact hN₁₂ (a := (x, y)) ⟨(hOsub hx).2.1, (hOsub hy).2.2⟩
  obtain ⟨sol, _, hsol⟩ := Analysis.common_ball_inverse_of_half_identity
    (fun _ : Unit ↦ H x y) a ha (fun _ _ ↦ continuous_const) (fun _ ↦ hoff)
    (fun _ v hv w hw ↦ hHerror x hxW y hyW v hv w hw)
  let z₀ : Unit × Metric.ball (0 : X) (a / 8) :=
    ((), ⟨0, Metric.mem_ball_self (by positivity)⟩)
  let z := sol z₀
  have hzsmall : ‖z‖ < a / 2 := (hsol z₀).1
  have hz : z ∈ Metric.closedBall (0 : X) a := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hzsmall.le.trans (by linarith only [ha])
  have hzeroF : F x y z = 0 := L.symm.injective (by
    simpa only [map_zero] using (hsol z₀).2.1)
  have heq : q x (gs x z.1) = q y (gu y z.2) := sub_eq_zero.mp hzeroF
  have hgsnative : e.symmL ℝ x.val.val (gs x z.1) =
      (ss x z.1 : TangentSpace 𝓘(ℝ, E) x.val.val) + μs x.val (ss x z.1) := by
    dsimp only [gs]
    rw [map_add, ← hssval, hbsval, e.symmL_continuousLinearMapAt (hbase x)]
  have hgunative : e.symmL ℝ y.val.val (gu y z.2) =
      (uu y z.2 : TangentSpace 𝓘(ℝ, E) y.val.val) + μu y.val (uu y z.2) := by
    dsimp only [gu]
    rw [map_add, ← huuval, hbuval, e.symmL_continuousLinearMapAt (hbase y)]
  have hsbound := (hsgraph x hxW z.1 (hfst z hz)).2.1
  have hubound := (hugraph y hyW z.2 (hsnd z hz)).2.1
  have hz₁ : ‖z.1‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hfst z hz
  have hz₂ : ‖z.2‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hsnd z hz
  have hstotal : ‖ss x z.1‖ + ‖μs x.val (ss x z.1)‖ < ρ := hsbound.trans_lt
    ((mul_le_mul_of_nonneg_left hz₁ (by positivity : 0 ≤ 2 * (B * B))).trans_lt haρ)
  have hutotal : ‖uu y z.2‖ + ‖μu y.val (uu y z.2)‖ < ρ := hubound.trans_lt
    ((mul_le_mul_of_nonneg_left hz₂ (by positivity : 0 ≤ 2 * (B * B))).trans_lt haρ)
  refine ⟨ss x z.1, uu y z.2, ?_, ?_, (norm_add_le _ _).trans_lt hstotal,
    (norm_add_le _ _).trans_lt hutotal, ?_⟩
  · linarith only [hstotal, norm_nonneg (μs x.val (ss x z.1))]
  · linarith only [hutotal, norm_nonneg (μu y.val (uu y z.2))]
  · have hsd := (hNdomain x.val.val (hWsub hxW).1 (gs x z.1) (hgsR x hxW z.1 (hfst z hz))).2
    have hud := (hNdomain y.val.val (hWsub hyW).1 (gu y z.2) (hguR y hyW z.2 (hsnd z hz))).2
    have hm := c.injOn hsd hud heq
    change riemannianExponential g ⟨x.val.val, e.symmL ℝ x.val.val (gs x z.1)⟩ =
      riemannianExponential g ⟨y.val.val, e.symmL ℝ y.val.val (gu y z.2)⟩ at hm
    rwa [hgsnative, hgunative] at hm

end HolomorphicAnosov


