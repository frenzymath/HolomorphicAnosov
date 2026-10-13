import HolomorphicAnosov.Analysis.Complex.AnchoredUnivalentContinuity
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! The analytic ratio-to-jet continuity step in Ghys Proposition 3.1, pp.590–593. -/
noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov

/-- A biholomorphic scalar chart defined on the unit disk gives the genuine
univalent disk map used by the ratio-continuity theorem. Its derivative is
nonzero because differentiation of the actual inverse identity gives product one. -/
theorem holomorphic_chart_unitDisc_map_g1
    (e : OpenPartialHomeomorph ℂ ℂ) (hsource : Metric.ball (0 : ℂ) 1 ⊆ e.source)
    (he : DifferentiableOn ℂ e e.source) (hei : DifferentiableOn ℂ e.symm e.target) :
    ∃ F : C(Complex.UnitDisc, ℂ), (∀ z, F z = e z.val) ∧
      DifferentiableOn ℂ (unitDiscExtension F) (Metric.ball 0 1) ∧
      Function.Injective F ∧ ∀ z : Complex.UnitDisc, deriv (unitDiscExtension F) z.val ≠ 0 := by
  classical
  let F : C(Complex.UnitDisc, ℂ) := ⟨fun z ↦ e z.val,
    e.continuousOn.comp_continuous continuous_subtype_val (fun z ↦ hsource z.property)⟩
  have hgerm (z : Complex.UnitDisc) : unitDiscExtension F =ᶠ[𝓝 z.val] e := by
    filter_upwards [Metric.isOpen_ball.mem_nhds z.property] with w hw
    simp only [unitDiscExtension,dite_eq_left hw]
    rfl
  refine ⟨F,fun _ ↦ rfl,?_,?_,?_⟩
  · intro z hz
    exact ((he z (hsource hz)).differentiableAt (e.open_source.mem_nhds (hsource hz))
      |>.congr_of_eventuallyEq (hgerm ⟨z,hz⟩)).differentiableWithinAt
  · intro z w hzw
    exact Subtype.ext (e.injOn (hsource z.property) (hsource w.property) hzw)
  · intro z
    have hze := hsource z.property
    have hf := (he z.val hze).differentiableAt (e.open_source.mem_nhds hze)
    have hi := (hei (e z.val) (e.map_source hze)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hze))
    have hid : (fun w ↦ e.symm (e w)) =ᶠ[𝓝 z.val] id := by
      filter_upwards [e.open_source.mem_nhds hze] with w hw
      exact e.left_inv hw
    have hmul : deriv e.symm (e z.val) * deriv e z.val = 1 := by
      rw [← (hi.hasDerivAt.comp z.val hf.hasDerivAt).deriv]
      change deriv (fun w ↦ e.symm (e w)) z.val = 1
      rw [hid.deriv_eq]
      exact deriv_id _
    rw [(hgerm z).deriv_eq]
    intro hz
    simp only [hz,mul_zero] at hmul
    exact zero_ne_one hmul

/-- Continuous distinct-triple ratios for a family of holomorphic univalent disk maps
make their logarithmic derivative of the first derivative jointly continuous.
Source: Ghys Proposition 3.1, pp.590–593; Lyubich §4.4 Theorem 4.12, pp.113–114.
Normalize each map at zero and a fixed nonzero anchor. At every other point its value
is the stipulated ratio, while the anchor values are constant. Anchored univalent
compactness upgrades this to compact-open continuity and hence joint continuity.
Cauchy derivative continuity gives continuous first and second derivatives. The first
is nonzero, so their quotient is continuous. Affine normalization multiplies both
derivatives by the same nonzero constant, leaving this quotient unchanged. -/
theorem continuous_affine_ratio_jet_coefficient_g1
    (hcompact : IsCompact {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g})
    {T : Type*} [MetricSpace T] (F : T → C(Complex.UnitDisc, ℂ))
    (b : Complex.UnitDisc) (hb : b ≠ 0)
    (hF : ∀ t, DifferentiableOn ℂ (unitDiscExtension (F t)) (Metric.ball 0 1) ∧
      Function.Injective (F t) ∧ ∀ z : Complex.UnitDisc,
        deriv (unitDiscExtension (F t)) z.val ≠ 0)
    (hratio : ∀ z : Complex.UnitDisc, z ≠ 0 → z ≠ b →
      Continuous (fun t ↦ (F t 0 - F t z) / (F t 0 - F t b))) :
    Continuous (fun p : Complex.UnitDisc × T ↦
      deriv (deriv (unitDiscExtension (F p.2))) p.1.val /
        deriv (unitDiscExtension (F p.2)) p.1.val) := by
  classical
  let k : T → ℂ := fun t ↦ (F t b - F t 0)⁻¹
  have hk (t : T) : k t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (fun h ↦ hb ((hF t).2.1 h)))
  let G : T → C(Complex.UnitDisc, ℂ) := fun t ↦
    k t • (F t - ContinuousMap.const _ (F t 0))
  have heq (t : T) (z : Complex.UnitDisc) :
      unitDiscExtension (G t) =ᶠ[𝓝 z.val]
        (fun w ↦ k t * (unitDiscExtension (F t) w - F t 0)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds z.property] with w hw
    simp only [unitDiscExtension, dite_eq_left hw]
    rfl
  have hdG (t : T) : DifferentiableOn ℂ (unitDiscExtension (G t)) (Metric.ball 0 1) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact (((hF t).1 z hz |>.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).sub_const
        (F t 0) |>.const_mul (k t)).congr_of_eventuallyEq (heq t ⟨z, hz⟩)
  have hderiv (t : T) (z : Complex.UnitDisc) :
      deriv (unitDiscExtension (G t)) z.val = k t * deriv (unitDiscExtension (F t)) z.val := by
    rw [(heq t z).deriv_eq]
    exact (((hF t).1 z.val z.property |>.differentiableAt
      (Metric.isOpen_ball.mem_nhds z.property)).hasDerivAt.sub_const (F t 0)
        |>.const_mul (k t)).deriv
  have hGG : Continuous G := by
    apply continuous_anchored_univalent hcompact G b hb
    · intro t
      refine ⟨hdG t, ?_, ?_, ?_, ?_⟩
      · intro z w h
        apply (hF t).2.1
        change k t * (F t z - F t 0) = k t * (F t w - F t 0) at h
        simpa only [sub_left_inj] using mul_left_cancel₀ (hk t) h
      · change k t * (F t 0 - F t 0) = 0
        simp
      · change k t * (F t b - F t 0) = 1
        exact inv_mul_cancel₀ (sub_ne_zero.mpr (fun h ↦ hb ((hF t).2.1 h)))
      · have he := hderiv t (0 : Complex.UnitDisc)
        change deriv (unitDiscExtension (G t)) ((0 : Complex.UnitDisc) : ℂ) =
          k t * deriv (unitDiscExtension (F t)) ((0 : Complex.UnitDisc) : ℂ) at he
        rw [Complex.UnitDisc.coe_zero] at he
        rw [he]
        apply mul_ne_zero (hk t)
        have hne := (hF t).2.2 (0 : Complex.UnitDisc)
        change deriv (unitDiscExtension (F t)) ((0 : Complex.UnitDisc) : ℂ) ≠ 0 at hne
        simpa only [Complex.UnitDisc.coe_zero] using hne
    · intro z
      by_cases hz : z = 0
      · subst z
        convert continuous_const (y := (0 : ℂ)) using 1
        funext t
        simp [G]
      by_cases hzb : z = b
      · subst z
        convert continuous_const (y := (1 : ℂ)) using 1
        funext t
        change k t * (F t b - F t 0) = 1
        exact inv_mul_cancel₀ (sub_ne_zero.mpr (fun h ↦ hb ((hF t).2.1 h)))
      · apply (hratio z hz hzb).congr
        intro t
        change (F t 0 - F t z) / (F t 0 - F t b) = k t * (F t z - F t 0)
        dsimp [k]
        rw [show F t 0 - F t z = -(F t z - F t 0) by ring,
          show F t 0 - F t b = -(F t b - F t 0) by ring, neg_div_neg_eq]
        rw [div_eq_mul_inv, mul_comm]
  let Ω : Set (ℂ × T) := Metric.ball 0 1 ×ˢ univ
  have hΩ : IsOpen Ω := Metric.isOpen_ball.prod isOpen_univ
  let H : ℂ × T → ℂ := fun p ↦ unitDiscExtension (G p.2) p.1
  have hH : ContinuousOn H Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let : LocallyCompactSpace Complex.UnitDisc := Metric.isOpen_ball.locallyCompactSpace
    have hc : Continuous (fun p : Ω ↦ G p.val.2 (⟨p.val.1, p.property.1⟩ : Complex.UnitDisc)) :=
      continuous_eval.comp ((hGG.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _))
    apply hc.congr
    intro p
    change G p.val.2 ⟨p.val.1, p.property.1⟩ = unitDiscExtension (G p.val.2) p.val.1
    simp only [unitDiscExtension, dite_eq_left p.property.1]
  have hdH (t : T) : DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ Ω} := by
    simpa only [Ω, H, mem_prod, mem_univ, and_true, ofPred_mem_eq] using hdG t
  have h1 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ H hH hdH
  have h2 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p ↦ deriv (fun z ↦ H (z, p.2)) p.1) h1
    (fun t ↦ (hdH t).deriv (hΩ.preimage (continuous_id.prodMk continuous_const)))
  have hparam : Continuous (fun p : Complex.UnitDisc × T ↦ ((p.1.val, p.2) : ℂ × T)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hc1 : Continuous (fun p : Complex.UnitDisc × T ↦ deriv (unitDiscExtension (G p.2)) p.1.val) := by
    simpa only [H, Function.comp_def] using h1.comp_continuous hparam (fun p ↦ ⟨p.1.property, mem_univ _⟩)
  have hc2 : Continuous (fun p : Complex.UnitDisc × T ↦ deriv (deriv (unitDiscExtension (G p.2))) p.1.val) := by
    simpa only [H, Function.comp_def] using h2.comp_continuous hparam (fun p ↦ ⟨p.1.property, mem_univ _⟩)
  have hd2 (t : T) (z : Complex.UnitDisc) :
      deriv (deriv (unitDiscExtension (G t))) z.val =
        k t * deriv (deriv (unitDiscExtension (F t))) z.val := by
    have he : deriv (unitDiscExtension (G t)) =ᶠ[𝓝 z.val]
        (fun w ↦ k t * deriv (unitDiscExtension (F t)) w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property] with w hw
      exact hderiv t ⟨w, hw⟩
    rw [he.deriv_eq, deriv_const_mul_field]
  apply (hc2.div hc1 (fun p ↦ by rw [hderiv]; exact mul_ne_zero (hk _) ((hF _).2.2 _))).congr
  intro p
  change deriv (deriv (unitDiscExtension (G p.2))) p.1.val /
      deriv (unitDiscExtension (G p.2)) p.1.val = _
  rw [hd2 p.2 p.1, hderiv p.2 p.1, mul_div_mul_left _ _ (hk p.2)]

/-- The ratio-to-jet conclusion also holds for a holomorphic coefficient family
identified only as a germ at the disk center. The identity principle extends
that germ equation over the connected disk. This permits arbitrary legitimate
representatives of a given holonomy germ in the continuity convention. -/
theorem continuous_affine_ratio_coefficient_of_germs_g1
    (hcompact : IsCompact {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g})
    {T : Type*} [MetricSpace T] (F : T → C(Complex.UnitDisc, ℂ))
    (b : Complex.UnitDisc) (hb : b ≠ 0)
    (hF : ∀ t, DifferentiableOn ℂ (unitDiscExtension (F t)) (Metric.ball 0 1) ∧
      Function.Injective (F t) ∧ ∀ z : Complex.UnitDisc,
        deriv (unitDiscExtension (F t)) z.val ≠ 0)
    (hratio : ∀ z : Complex.UnitDisc, z ≠ 0 → z ≠ b →
      Continuous (fun t ↦ (F t 0 - F t z) / (F t 0 - F t b)))
    (A : T → ℂ → ℂ)
    (hA : ∀ t, DifferentiableOn ℂ (A t) (Metric.ball 0 1))
    (hAgerm : ∀ t, A t =ᶠ[𝓝 0] fun z ↦
      -(deriv (deriv (unitDiscExtension (F t))) z /
        (2 * deriv (unitDiscExtension (F t)) z))) :
    Continuous (fun p : Complex.UnitDisc × T ↦ A p.2 p.1.val) := by
  have heq (t : T) : EqOn (A t) (fun z ↦
      -(deriv (deriv (unitDiscExtension (F t))) z /
        (2 * deriv (unitDiscExtension (F t)) z))) (Metric.ball 0 1) := by
    apply ((hA t).analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      _ (convex_ball (0 : ℂ) 1).isPreconnected (Metric.mem_ball_self (by norm_num)) (hAgerm t)
    have hd1 := (hF t).1.deriv Metric.isOpen_ball
    have hd2 := hd1.deriv Metric.isOpen_ball
    exact (hd2.div (hd1.const_mul (2 : ℂ))
      (fun z hz ↦ mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ((hF t).2.2 ⟨z, hz⟩))
      |>.neg).analyticOnNhd Metric.isOpen_ball
  have hc := continuous_affine_ratio_jet_coefficient_g1 hcompact F b hb hF hratio
  apply ((hc.div_const (2 : ℂ)).neg).congr
  intro p
  rw [heq p.2 p.1.property]
  change -(deriv (deriv (unitDiscExtension (F p.2))) p.1.val /
    deriv (unitDiscExtension (F p.2)) p.1.val / 2) = _
  rw [div_div, mul_comm]

end HolomorphicAnosov
