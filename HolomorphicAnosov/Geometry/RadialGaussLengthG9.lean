import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_fibre_contMDiffOn
import HolomorphicAnosov.Geometry.Riemannian.GallierQuaintanceGaussLemma
import HolomorphicAnosov.Geometry.Riemannian.Gauss.FibreSmooth
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Geometry.FirstExitTopologicalG18
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

open Set MeasureTheory
noncomputable section
namespace HolomorphicAnosov

/-- The Gauss pairing identity bounds the increase in radial norm by the integral of the receiving
speed. (Andrews, Prop. 11.2.1, pp. 103–104) -/
theorem radial_gauss_length_lower_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {W : ℝ → Type*} [∀ t, NormedAddCommGroup (W t)] [∀ t, InnerProductSpace ℝ (W t)]
    {a b : ℝ} (hab : a ≤ b) (c c' : ℝ → V)
    (hc : ContinuousOn c (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t)
    (L : ∀ t, V →L[ℝ] W t) (speed : ℝ → ℝ)
    (hGauss : ∀ t ∈ Ioo a b, ∀ w : V,
      inner ℝ (L t (c t)) (L t w) = inner ℝ (c t) w)
    (hspeed : ∀ t ∈ Ioo a b, ‖L t (c' t)‖ ≤ speed t)
    (hint : IntegrableOn speed (Icc a b)) :
    ‖c b‖ - ‖c a‖ ≤ ∫ t in a..b, speed t := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let r (t : ℝ) := Real.sqrt (‖c t‖ ^ 2 + ε ^ 2)
  have hrpos (t : ℝ) : 0 < r t := Real.sqrt_pos.mpr (by positivity)
  have hrlower (t : ℝ) : ‖c t‖ ≤ r t := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith only [sq_nonneg ε])
  have hrupper (t : ℝ) : r t ≤ ‖c t‖ + ε := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [mul_nonneg (norm_nonneg (c t)) hε.le]
  have hrcont : ContinuousOn r (Icc a b) := (hc.norm.pow 2 |>.add continuousOn_const).sqrt
  have hdr (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt r (inner ℝ (c t) (c' t) / r t) t := by
    have hh := ((hd t ht).norm_sq.add_const (ε ^ 2)).sqrt
      (by positivity : ‖c t‖ ^ 2 + ε ^ 2 ≠ 0)
    convert hh using 1
    dsimp [r]
    field_simp
  have hradnorm (t : ℝ) (ht : t ∈ Ioo a b) : ‖L t (c t)‖ = ‖c t‖ := by
    have hh := hGauss t ht (c t)
    simp only [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg (L t (c t)), norm_nonneg (c t)]
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) :
      inner ℝ (c t) (c' t) / r t ≤ speed t := by
    apply (div_le_iff₀ (hrpos t)).mpr
    rw [← hGauss t ht (c' t)]
    calc
      _ ≤ ‖L t (c t)‖ * ‖L t (c' t)‖ := real_inner_le_norm _ _
      _ = ‖c t‖ * ‖L t (c' t)‖ := by rw [hradnorm t ht]
      _ ≤ r t * speed t := mul_le_mul (hrlower t) (hspeed t ht) (norm_nonneg _) (hrpos t).le
      _ = speed t * r t := mul_comm _ _
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hrcont
    (fun t ht ↦ (hdr t ht).hasDerivWithinAt) hint hbound
  linarith only [hi, hrlower b, hrupper a]

open Bundle
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false in
/-- The increase in tangent norm along exponential coordinates is bounded by the length of the image
curve. (Andrews, Prop. 11.2.1, pp. 103–104) -/
theorem exponential_radial_path_length_lower_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ (a b : ℝ) (c : ℝ → TangentSpace 𝓘(ℝ, E) p), a ≤ b →
      ContinuousOn c (Icc a b) →
      (∀ t ∈ Ioo a b, DifferentiableAt ℝ c t) →
      (∀ t ∈ Icc a b, (⟨p, c t⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) →
      let γ := fun t ↦ riemannianExponential g ⟨p, c t⟩
      IntegrableOn (fun t ↦ ‖curveVelocity (E := E) γ t‖) (Icc a b) →
      ENNReal.ofReal (‖c b‖ - ‖c a‖) ≤ Manifold.pathELength 𝓘(ℝ, E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro a b c hab hc hd hdom γ hint
  let e := fun v : TangentSpace 𝓘(ℝ, E) p ↦ riemannianExponential g ⟨p, v⟩
  let L (t : ℝ) := (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e (c t)).comp
    (NormedSpace.fromTangentSpace (c t)).symm.toContinuousLinearMap
  have hvel (t : ℝ) (ht : t ∈ Ioo a b) : L t (deriv c t) = curveVelocity (E := E) γ t := by
    have he := (gauss_fibre_smooth g p (c t) (hdom t (Ioo_subset_Icc_self ht))).mdifferentiableAt (by simp)
    have hh := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p)) (I'' := 𝓘(ℝ, E))
      (f := c) (g := e) (x := t) he (hd t ht).mdifferentiableAt (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 =
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e (c t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) c t 1) at hh
    rw [mfderiv_eq_fderiv] at hh
    exact hh.symm
  have hGauss (t : ℝ) (ht : t ∈ Ioo a b) (w : TangentSpace 𝓘(ℝ, E) p) :
      inner ℝ (L t (c t)) (L t w) = inner ℝ (c t) w :=
    (gallier_quaintance_gauss_lemma g).2.2.2.1 p (c t) w (hdom t (Ioo_subset_Icc_self ht))
  have hh := radial_gauss_length_lower_bound hab c (deriv c) hc
    (fun t ht ↦ (hd t ht).hasDerivAt) L (fun t ↦ ‖curveVelocity (E := E) γ t‖)
    hGauss (fun t ht ↦ le_of_eq (congrArg norm (hvel t ht))) hint
  apply (ENNReal.ofReal_le_ofReal hh).trans_eq
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun t ↦ norm_nonneg _)),
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  congr 1
  funext t
  exact ofReal_norm _

/-- The Riemannian distance from the base point to an exponential image is at most the initial
tangent norm. (Andrews, Prop. 11.2.1, pp. 103–104) -/
theorem riemannianEDist_exponential_le_norm
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v : TangentSpace 𝓘(ℝ, E) p,
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g →
      Manifold.riemannianEDist 𝓘(ℝ, E) p (riemannianExponential g ⟨p, v⟩) ≤ ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro v hv
  obtain ⟨J, hJ, hJconn, hseg, hgeod, hdom, hspeed⟩ :=
    (gallier_quaintance_gauss_lemma g).2.2.2.2.1 p v hv
  let γ := fun t : ℝ ↦ riemannianExponential g ⟨p, t • v⟩
  have hzero : γ 0 = p := by simpa only [γ, zero_smul] using (riemannianExponential_zero g p).2
  have hone : γ 1 = riemannianExponential g ⟨p, v⟩ := by simp only [γ, one_smul]
  have hh := Manifold.riemannianEDist_le_pathELength
    ((hgeod.1.mono hseg).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)) hzero hone zero_le_one
  apply hh.trans_eq
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have heq : (∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1‖ₑ) =
      ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖v‖ := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    change ‖curveVelocity (E := E) γ t‖ₑ = ENNReal.ofReal ‖v‖
    exact (ofReal_norm (curveVelocity (E := E) γ t)).symm.trans
      (congrArg ENNReal.ofReal (hspeed t ht))
  rw [heq]
  simp



/-- A radial lower bound for curve prefixes inside a normal chart gives a lower bound for the full
curve length when the endpoint lies in the normal ball. (Andrews, Prop. 11.2.1, pp. 103–104) -/
theorem normal_chart_first_exit_length_lower_bound
    {V X : Type*} [NormedAddCommGroup V] [ProperSpace V]
    [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph V X) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall (0 : V) r ⊆ e.source)
    (γ : ℝ → X) (hγ : ContinuousOn γ (Icc 0 1)) (hstart : γ 0 = e 0)
    (v : V) (hv : ‖v‖ ≤ r) (hend : γ 1 = e v)
    (length : ℝ → ENNReal)
    (hmono : ∀ t ∈ Icc (0 : ℝ) 1, length t ≤ length 1)
    (hradial : ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo γ (Icc 0 t) e.target → ENNReal.ofReal ‖e.symm (γ t)‖ ≤ length t) :
    ENNReal.ofReal ‖v‖ ≤ length 1 := by
  let S := e '' Metric.ball (0 : V) r
  let K := e '' Metric.closedBall (0 : V) r
  have hS : IsOpen S := e.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hsource)
  have hK : IsCompact K := (isCompact_closedBall (0 : V) r).image_of_continuousOn
    (e.continuousOn.mono hsource)
  have hclosure : closure S ⊆ K := closure_minimal (image_mono Metric.ball_subset_closedBall) hK.isClosed
  have hKt : K ⊆ e.target := by
    rintro _ ⟨w, hw, rfl⟩
    exact e.map_source (hsource hw)
  have hSt : S ⊆ e.target := (image_mono Metric.ball_subset_closedBall).trans hKt
  have hstartS : γ 0 ∈ S := by rw [hstart]; exact ⟨0, by simpa using hr, rfl⟩
  by_cases hall : MapsTo γ (Icc (0 : ℝ) 1) S
  · have hh := hradial 1 ⟨zero_le_one, le_rfl⟩ (fun t ht ↦ hSt (hall ht))
    rw [hend, e.left_inv (hsource (by simpa using hv))] at hh
    exact hh
  · have hexit : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∉ S := by
      simpa only [MapsTo, not_forall, exists_prop] using hall
    obtain ⟨t, ht, hout⟩ := hexit
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hout hstartS)
    obtain ⟨τ, hτ, hτpos, hfront, hbefore⟩ :=
      exists_first_exit_time hS htpos (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hstartS hout
    have hτone : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hτK : γ τ ∈ K := hclosure (frontier_subset_closure hfront)
    obtain ⟨w, hw, hew⟩ := hτK
    have hws := hsource hw
    have heinv : e.symm (γ τ) = w := by rw [← hew, e.left_inv hws]
    have hwr : ‖w‖ = r := by
      apply le_antisymm (by simpa using hw)
      by_contra h
      have hm : γ τ ∈ S := ⟨w, by simpa using lt_of_not_ge h, hew⟩
      rw [frontier, hS.interior_eq] at hfront
      exact hfront.2 hm
    have hpref : MapsTo γ (Icc 0 τ) e.target := by
      intro s hs
      by_cases hst : s = τ
      · subst s; exact hKt ⟨w, hw, hew⟩
      · exact hSt (hbefore s hs hst)
    have hh := hradial τ hτone hpref
    rw [heinv, hwr] at hh
    exact (ENNReal.ofReal_le_ofReal hv).trans (hh.trans (hmono τ hτone))

set_option backward.isDefEq.respectTransparency false in
private lemma metric_curve_speed_congr
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {γ η : ℝ → M} {t : ℝ} (heq : γ =ᶠ[𝓝 t] η) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ‖curveVelocity (E := E) γ t‖ = ‖curveVelocity (E := E) η t‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hcast (x y : M) (hxy : x = y) (v : TangentSpace 𝓘(ℝ, E) x) :
      ‖(tangentSpaceCast 𝓘(ℝ, E) x y) v‖ = ‖v‖ := by subst y; rfl
  have hh := DFunLike.congr_fun (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))) 1
  change curveVelocity (E := E) γ t =
    tangentSpaceCast 𝓘(ℝ, E) (η t) (γ t) (curveVelocity (E := E) η t) at hh
  rw [hh]
  exact hcast _ _ heq.eq_of_nhds.symm _

set_option backward.isDefEq.respectTransparency false in
private lemma continuous_metric_curve_speed
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    Continuous (fun t ↦ ‖curveVelocity (E := E) γ t‖) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hk : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  have hv : Continuous (fun t ↦ (⟨γ t, curveVelocity (E := E) γ t⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hk.continuous
  exact Real.continuous_sqrt.comp (hv.inner_bundle hv)

set_option backward.isDefEq.respectTransparency false in
/-- On a closed ball contained in an exponential inverse chart, distance from the base point equals
the tangent norm. (Andrews, Prop. 11.2.1, pp. 103–104) -/
theorem normal_exponential_chart_distance_eq
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ (e : PartialDiffeomorph 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
        (TangentSpace 𝓘(ℝ, E) p) M ∞) (r : ℝ), 0 < r →
      Metric.closedBall (0 : TangentSpace 𝓘(ℝ, E) p) r ⊆ e.source →
      (∀ v ∈ e.source, (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) →
      (∀ v ∈ e.source, e v = riemannianExponential g ⟨p, v⟩) →
      ∀ v : TangentSpace 𝓘(ℝ, E) p, ‖v‖ ≤ r →
        Manifold.riemannianEDist 𝓘(ℝ, E) p (e v) = ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro e r hr hsource hdom hexp v hv
  have h0 : (0 : TangentSpace 𝓘(ℝ, E) p) ∈ e.source := hsource (by simpa using hr.le)
  have hvsource : v ∈ e.source := hsource (by simpa using hv)
  have hezero : e 0 = p := (hexp 0 h0).trans (riemannianExponential_zero g p).2
  apply le_antisymm
  · rw [hexp v hvsource]
    exact riemannianEDist_exponential_le_norm g p v (hdom v hvsource)
  · by_contra hnot
    have hdist : Manifold.riemannianEDist 𝓘(ℝ, E) p (e v) < ENNReal.ofReal ‖v‖ := lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hdist (by norm_num : (0 : ℝ) < 1)
    have hspeed := continuous_metric_curve_speed g hγ
    have hradial (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
        (hpref : MapsTo γ (Icc 0 t) e.target) :
        ENNReal.ofReal ‖e.symm (γ t)‖ ≤ Manifold.pathELength 𝓘(ℝ, E) γ 0 t := by
      let c := e.symm ∘ γ
      let η := fun s : ℝ ↦ riemannianExponential g ⟨p, c s⟩
      have hcs (s : ℝ) (hs : s ∈ Icc 0 t) : c s ∈ e.source := e.map_target (hpref hs)
      have hceq : EqOn η γ (Icc 0 t) := by
        intro s hs
        exact (hexp (c s) (hcs s hs)).symm.trans (e.right_inv (hpref hs))
      have hevent (s : ℝ) (hs : s ∈ Ioo 0 t) : η =ᶠ[𝓝 s] γ :=
        Filter.eventuallyEq_of_mem (Icc_mem_nhds hs.1 hs.2) (fun u hu ↦ hceq hu)
      have hcont : ContinuousOn c (Icc 0 t) :=
        e.toOpenPartialHomeomorph.continuousOn_symm.comp hγ.continuous.continuousOn hpref
      have hdiff (s : ℝ) (hs : s ∈ Ioo 0 t) : DifferentiableAt ℝ c s := by
        have hh := (e.contMDiffOn_invFun.contMDiffAt
          (e.open_target.mem_nhds (hpref (Ioo_subset_Icc_self hs)))).of_le
            (by simp : (1 : WithTop ℕ∞) ≤ ∞)
        exact ((hh.comp s hγ.contMDiffAt).contDiffAt).differentiableAt one_ne_zero
      have hae : (fun s ↦ ‖curveVelocity (E := E) η s‖) =ᵐ[volume.restrict (Icc 0 t)]
          (fun s ↦ ‖curveVelocity (E := E) γ s‖) := by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact metric_curve_speed_congr g (hevent s hs)
      have hint : IntegrableOn (fun s ↦ ‖curveVelocity (E := E) η s‖) (Icc 0 t) :=
        (hspeed.continuousOn.integrableOn_Icc).congr hae.symm
      have hh := exponential_radial_path_length_lower_bound g p 0 t c ht.1 hcont hdiff
        (fun s hs ↦ hdom (c s) (hcs s hs)) hint
      have hc0 : c 0 = 0 := by
        change e.symm (γ 0) = 0
        exact (congrArg e.symm (hγ0.trans hezero.symm)).trans (e.left_inv h0)
      rw [hc0, norm_zero, sub_zero] at hh
      exact hh.trans_eq (Manifold.pathELength_congr hceq)
    have hbound := normal_chart_first_exit_length_lower_bound e.toOpenPartialHomeomorph hr hsource
      γ hγ.continuous.continuousOn (hγ0.trans hezero.symm) v hv hγ1
      (fun t ↦ Manifold.pathELength 𝓘(ℝ, E) γ 0 t)
      (fun t ht ↦ Manifold.pathELength_mono le_rfl ht.2) hradial
    exact (not_lt_of_ge hbound) hlength

set_option backward.isDefEq.respectTransparency false in
/-- A compact set admits a uniform normal radius on which distance from each base point equals the
exponential tangent norm. (Andrews, Prop. 11.3.1, pp. 104–105; HPS, Thm. 5.5, p. 62) -/
theorem compact_uniform_exponential_distance_radius
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ A, ∀ v : TangentSpace 𝓘(ℝ, E) p, ‖v‖ ≤ ρ →
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g ∧
      Manifold.riemannianEDist 𝓘(ℝ, E) p (riemannianExponential g ⟨p, v⟩) = ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨U, R, hAU, hR, hdomain, hinj, hloc⟩ := ExponentialLift.uniform_inverse_tube g A hA
  let O : TopologicalSpace.Opens (TangentBundle 𝓘(ℝ, E) M) :=
    ⟨ExponentialLift.normalTube g U R, ExponentialLift.isOpen_normalTube g U R⟩
  obtain ⟨B, Φ, hB, hΦ⟩ := ExponentialLift.glue_inverse_tube g O hinj hloc
  obtain ⟨L, hLinverse, hright, hleft⟩ := ExponentialLift.inverse_tube_laws g O B Φ hΦ
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro p hp v hv
  have hpU := hAU hp
  have hsmall (w : TangentSpace 𝓘(ℝ, E) p) (hw : ‖w‖ < R) :
      (⟨p, w⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O := ⟨hpU, hw⟩
  have hforward (w : TangentSpace 𝓘(ℝ, E) p) (hw : ‖w‖ < R) :
      (p, riemannianExponential g ⟨p, w⟩) ∈ B := by
    have hh := (Φ ⟨⟨p, w⟩, hsmall w hw⟩).property
    simpa only [hΦ, riemannianExponentialAddition] using hh
  have hbackward (y : M) (hy : (p, y) ∈ B) : ‖L p y‖ < R := by
    have hh := (Φ.symm ⟨(p, y), hy⟩).property
    rw [hLinverse] at hh
    exact hh.2
  have hLsmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) ∞
      (L p) {y | (p, y) ∈ B} := by
    have hh := ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm.contDiff.contMDiff).comp_contMDiffOn
      (ExponentialLift.inverse_fibre_contMDiffOn O B Φ L hLinverse p)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh
  let e : PartialDiffeomorph 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) p) M ∞ :=
    { toFun := fun w ↦ riemannianExponential g ⟨p, w⟩
      invFun := L p
      source := {w | ‖w‖ < R}
      target := {y | (p, y) ∈ B}
      map_source' := hforward
      map_target' := hbackward
      left_inv' := fun w hw ↦ hleft p w (hsmall w hw)
      right_inv' := fun y hy ↦ hright p y hy
      open_source := isOpen_lt continuous_norm continuous_const
      open_target := B.isOpen.preimage (continuous_const.prodMk continuous_id)
      contMDiffOn_toFun := fun w hw ↦
        (gauss_fibre_smooth g p w (hdomain (hsmall w hw))).contMDiffWithinAt
      contMDiffOn_invFun := hLsmooth }
  have hball : Metric.closedBall (0 : TangentSpace 𝓘(ℝ, E) p) (R / 2) ⊆ e.source := by
    intro w hw
    exact lt_of_le_of_lt (by simpa using hw) (half_lt_self hR)
  have heq := normal_exponential_chart_distance_eq g p e (R / 2) (half_pos hR) hball
    (fun w hw ↦ hdomain (hsmall w hw)) (fun _ _ ↦ rfl) v hv
  exact ⟨hdomain (hsmall v (hv.trans_lt (half_lt_self hR))), heq⟩


set_option backward.isDefEq.respectTransparency false in
/-- Exponential images of any prescribed positive tangent radius cover a uniform metric neighborhood
of the diagonal over a compact base. (HPS, Thm. 5.5, p. 62) -/
theorem compact_uniform_exponential_ball_cover
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ A, ∀ y : M, dist p y < δ →
      ∃ v : TangentSpace 𝓘(ℝ, E) p, ‖v‖ < ε ∧
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g ∧
        riemannianExponential g ⟨p, v⟩ = y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro ε hε
  obtain ⟨U, R, hAU, hR, hdomain, hinj, hloc⟩ := ExponentialLift.uniform_inverse_tube g A hA
  let O : TopologicalSpace.Opens (TangentBundle 𝓘(ℝ, E) M) :=
    ⟨ExponentialLift.normalTube g U (min R ε), ExponentialLift.isOpen_normalTube g U (min R ε)⟩
  have hsub : (O : Set _) ⊆ ExponentialLift.normalTube g U R :=
    fun z hz ↦ ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  obtain ⟨B, Φ, hB, hΦ⟩ := ExponentialLift.glue_inverse_tube g O (hinj.mono hsub)
    (fun z ↦ hloc ⟨z, hsub z.property⟩)
  obtain ⟨L, hLinverse, hright, hleft⟩ := ExponentialLift.inverse_tube_laws g O B Φ hΦ
  have hdiag : (fun p : M ↦ (p, p)) '' A ⊆ (B : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    have hz : (⟨p, (0 : TangentSpace 𝓘(ℝ, E) p)⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O :=
      ⟨hAU hp, by
        change ‖(0 : TangentSpace 𝓘(ℝ, E) p)‖ < min R ε
        simpa only [norm_zero] using lt_min hR hε⟩
    have hh := (Φ ⟨⟨p, 0⟩, hz⟩).property
    change (p, p) ∈ B
    simpa only [hΦ, riemannianExponentialAddition, (riemannianExponential_zero g p).2] using hh
  obtain ⟨δ, hδ, hthick⟩ :=
    (hA.image (continuous_id.prodMk continuous_id)).exists_thickening_subset_open B.isOpen hdiag
  refine ⟨δ, hδ, ?_⟩
  intro p hp y hy
  have hpy : (p, y) ∈ B := by
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨(p, p), ⟨p, hp, rfl⟩, ?_⟩
    simpa [Prod.dist_eq, dist_comm] using hy
  have hv := (Φ.symm ⟨(p, y), hpy⟩).property
  rw [hLinverse] at hv
  exact ⟨L p y, hv.2.trans_le (min_le_right _ _), hdomain (hsub hv), hright p y hpy⟩


end HolomorphicAnosov
