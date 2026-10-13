import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import Mathlib.Analysis.Calculus.MeanValue
import HolomorphicAnosov.Analysis.Complex.UniformFlatCoordinate

/-! # Flat holomorphic coordinates continuous in parameters

Ghys, Holomorphic Anosov systems (1995), Lemma 3.2 and Proposition 3.1,
pp.590–593. Integrating twice on fixed convex plaques makes the transverse
continuity of the flat coordinates explicit.
-/
noncomputable section
open Set MeasureTheory AffineMap
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- The primitive normalized at a, given by integration along the straight
segment from a. This is actual data, with no chosen primitive. -/
def normalizedSegmentPrimitive (g : ℂ → ℂ) (a z : ℂ) : ℂ :=
  ∫ᶜ w in Path.segment a z, (1 : ℂ →L[ℂ] ℂ).smulRight (g w)

/-- On an open convex domain the normalized segment integral has the specified
holomorphic derivative. This is the one-dimensional Poincaré lemma with its
explicit segment witness, including its normalization. -/
theorem normalizedSegmentPrimitive_hasDerivAt {U : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {a z : ℂ} (ha : a ∈ U) (hz : z ∈ U) :
    HasDerivAt (normalizedSegmentPrimitive g a) (g z) z := by
  have h := hconv.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (ω := fun w ↦ (1 : ℂ →L[ℂ] ℂ).smulRight (g w))
    (fun w hw ↦ (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).hasFDerivAt
      |>.comp_hasDerivWithinAt w (hg w hw).hasDerivWithinAt |>.restrictScalars ℝ)
    (fun w hw x hx y hy ↦ by simpa using smul_comm x y (derivWithin g U w)) ha hz
  exact h.hasFDerivAt (hU.mem_nhds hz)

/-- Joint continuity of a coefficient gives joint continuity of its normalized
segment primitive on the same convex domain. Clamp the integration parameter
outside [0,1], so only coefficient values in the original domain are used;
the continuous parametric integral theorem applies to this actual integrand. -/
theorem normalizedSegmentPrimitive_continuousOn {T : Type*} [TopologicalSpace T]
    {U : Set ℂ} (hconv : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    {g : T → ℂ → ℂ} (hg : ContinuousOn (Function.uncurry g) (univ ×ˢ U)) :
    ContinuousOn (fun p : T × ℂ ↦ normalizedSegmentPrimitive (g p.1) a p.2)
      (univ ×ˢ U) := by
  let F : (T × U) → ℝ → ℂ := fun p r ↦
    (p.2.val - a) * g p.1 (lineMap a p.2.val (projIcc 0 1 zero_le_one r).val)
  have hf : Continuous (Function.uncurry F) := by
    have hmap : Continuous (fun p : (T × U) × ℝ ↦
        (p.1.1, lineMap a p.1.2.val (projIcc 0 1 zero_le_one p.2).val)) := by
      dsimp [lineMap_apply]
      fun_prop
    have hg' := hg.comp_continuous hmap (fun p ↦
      ⟨mem_univ _, hconv.lineMap_mem ha p.1.2.property (projIcc 0 1 zero_le_one p.2).property⟩)
    exact (by fun_prop : Continuous (fun p : (T × U) × ℝ ↦ p.1.2.val - a)).mul hg'
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf 0 1
  have heq (p : T × U) : (∫ r in (0 : ℝ)..1, F p r) =
      normalizedSegmentPrimitive (g p.1) a p.2.val := by
    rw [normalizedSegmentPrimitive, curveIntegral_segment]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    simp [F, projIcc_of_mem zero_le_one hr]
  have hrestricted : Continuous (fun p : T × U ↦
      normalizedSegmentPrimitive (g p.1) a p.2.val) := by
    simpa only [heq] using hcont
  rw [continuousOn_iff_continuous_domRestrict]
  exact hrestricted.comp (show Continuous (fun p : univ ×ˢ U ↦
    (p.val.1, (⟨p.val.2, p.property.2⟩ : U))) by fun_prop)

/-- A jointly continuous family of holomorphic coefficients on a fixed open convex
plaque has jointly continuous flat-coordinate primitives, normalized by H(a)=0
and H′(a)=1. Their derivatives never vanish and satisfy H″=-2 A H′.
No injectivity on the entire plaque is asserted. Source: the normalized local
ODE step of Ghys Lemma 3.2 and Proposition 3.1, pp.590–593. Integrate -2 A
along segments, exponentiate, and integrate again; the preceding continuity
lemma and the exponential chain rule give every claimed property. -/
theorem parametric_holomorphic_flat_coordinate_g1
    {T : Type*} [TopologicalSpace T] {U : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (A : T → ℂ → ℂ) (hA : ContinuousOn (Function.uncurry A) (univ ×ˢ U))
    (hhol : ∀ t, DifferentiableOn ℂ (A t) U) :
    ∃ H : T → ℂ → ℂ,
      ContinuousOn (Function.uncurry H) (univ ×ˢ U) ∧
      (∀ t, H t a = 0 ∧ deriv (H t) a = 1) ∧
      ∀ t z, z ∈ U → DifferentiableAt ℂ (H t) z ∧
        deriv (H t) z ≠ 0 ∧
        deriv (deriv (H t)) z = (-2 : ℂ) * A t z * deriv (H t) z := by
  let P : T → ℂ → ℂ := fun t ↦ normalizedSegmentPrimitive (fun z ↦ (-2 : ℂ) * A t z) a
  have hP (t : T) (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (P t) ((-2 : ℂ) * A t z) z :=
    normalizedSegmentPrimitive_hasDerivAt hU hconv ((hhol t).const_mul (-2 : ℂ)) ha hz
  have hcP : ContinuousOn (Function.uncurry P) (univ ×ˢ U) :=
    normalizedSegmentPrimitive_continuousOn hconv ha (g := fun t z ↦ (-2 : ℂ) * A t z)
      (continuousOn_const.mul hA)
  let E : T → ℂ → ℂ := fun t z ↦ Complex.exp (P t z)
  have hE (t : T) : DifferentiableOn ℂ (E t) U := fun z hz ↦
    (hP t z hz).cexp.differentiableAt.differentiableWithinAt
  let H : T → ℂ → ℂ := fun t ↦ normalizedSegmentPrimitive (E t) a
  have hH (t : T) (z : ℂ) (hz : z ∈ U) : HasDerivAt (H t) (E t z) z :=
    normalizedSegmentPrimitive_hasDerivAt hU hconv (hE t) ha hz
  refine ⟨H, normalizedSegmentPrimitive_continuousOn hconv ha hcP.cexp, ?_, ?_⟩
  · intro t
    have hPa : P t a = 0 := by
      simp [P, normalizedSegmentPrimitive]
    refine ⟨?_, ?_⟩
    · simp [H, normalizedSegmentPrimitive]
    · rw [(hH t a ha).deriv]
      simp [E, hPa]
  · intro t z hz
    have heq : deriv (H t) =ᶠ[𝓝 z] E t := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (hH t w hw).deriv
    refine ⟨(hH t z hz).differentiableAt, ?_, ?_⟩
    · rw [(hH t z hz).deriv]
      exact Complex.exp_ne_zero _
    · rw [heq.deriv_eq, (hP t z hz).cexp.deriv, (hH t z hz).deriv]
      dsimp [E]
      ring

/-- A continuous compact family of holomorphic maps with derivative one at a
common center is injective on one common disk. Joint derivative continuity and
the tube lemma give |H'-1|<1/2 there. The convex mean-value estimate applied to
H-id bounds its difference by half the input difference, which proves injectivity.
Source: the uniform local-coordinate step in Ghys Proposition 3.1, pp.591–593. -/
theorem compact_holomorphic_family_uniform_injective_g1
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {U : Set ℂ} (hU : IsOpen U) {a : ℂ} (ha : a ∈ U)
    (H : T → ℂ → ℂ) (hH : ContinuousOn (Function.uncurry H) (univ ×ˢ U))
    (hd : ∀ t, DifferentiableOn ℂ (H t) U)
    (hnorm : ∀ t, deriv (H t) a = 1) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ U ∧
      ∀ t, Set.InjOn (H t) (Metric.ball a r) := by
  let Ω : Set (ℂ × T) := U ×ˢ univ
  have hΩ : IsOpen Ω := hU.prod isOpen_univ
  have hcH : ContinuousOn (fun p : ℂ × T ↦ H p.2 p.1) Ω :=
    hH.comp continuous_swap.continuousOn (fun p hp ↦ ⟨mem_univ _, hp.1⟩)
  have hderiv := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p : ℂ × T ↦ H p.2 p.1) hcH
    (fun t ↦ by simpa only [Ω, mem_prod, mem_univ, and_true, ofPred_mem_eq] using hd t)
  let V : Set (ℂ × T) := Ω ∩ {p | ‖deriv (H p.2) p.1 - 1‖ < (1 / 2 : ℝ)}
  have hV : IsOpen V := by
    exact (continuousOn_open_iff hΩ).mp ((hderiv.sub continuousOn_const).norm)
      (Set.Iio (1 / 2 : ℝ)) isOpen_Iio
  have hsub : ({a} : Set ℂ) ×ˢ (univ : Set T) ⊆ V := by
    rintro ⟨z, t⟩ ⟨hz, _⟩
    simp only [mem_singleton_iff] at hz
    subst z
    exact ⟨⟨ha, mem_univ _⟩, by simp [hnorm]⟩
  obtain ⟨W, S, hW, _, haW, hS, hWS⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hV hsub
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW a (haW (mem_singleton a))
  have hbound (t : T) (z : ℂ) (hz : z ∈ Metric.ball a r) :
      z ∈ U ∧ ‖deriv (H t) z - 1‖ ≤ (1 / 2 : ℝ) := by
    have h := hWS (show (z,t) ∈ W ×ˢ S from ⟨hrW hz, hS (mem_univ t)⟩)
    exact ⟨h.1.1, h.2.le⟩
  by_cases hT : Nonempty T
  · have := hT
    refine ⟨r, hr, fun z hz ↦ (hbound (Classical.arbitrary T) z hz).1, ?_⟩
    intro t z hz w hw heq
    have hest := (convex_ball a r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x ↦ H t x - x)
      (fun x hx ↦ ((hd t x (hbound t x hx).1).differentiableAt
        (hU.mem_nhds (hbound t x hx).1)).hasDerivAt.sub (hasDerivAt_id x)
        |>.hasDerivWithinAt)
      (fun x hx ↦ (hbound t x hx).2) hz hw
    rw [← heq] at hest
    have hsimp : (H t z - w) - (H t z - z) = z - w := by ring
    rw [hsimp, norm_sub_rev w z] at hest
    have hzero : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z-w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.mp hU a ha
    exact ⟨r', hr', hr'U, fun t ↦ (hT ⟨t⟩).elim⟩

open scoped ContDiff

/-- On a compact parameter family the normalized flat primitives define actual
biholomorphic charts on one fixed disk, with jointly continuous evaluations.
This strengthens the primitive statement by the uniform injectivity just proved. -/
theorem parametric_holomorphic_flat_charts_g1
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (A : T → ℂ → ℂ) (hA : ContinuousOn (Function.uncurry A) (univ ×ˢ U))
    (hhol : ∀ t, DifferentiableOn ℂ (A t) U) :
    ∃ (r : ℝ) (e : T → OpenPartialHomeomorph ℂ ℂ), 0 < r ∧ Metric.ball a r ⊆ U ∧
      ContinuousOn (fun p : T × ℂ ↦ e p.1 p.2) (univ ×ˢ Metric.ball a r) ∧
      ∀ t, (e t).source = Metric.ball a r ∧ e t a = 0 ∧ deriv (e t) a = 1 ∧
        ContDiffOn ℂ ∞ (e t) (e t).source ∧ ContDiffOn ℂ ∞ (e t).symm (e t).target ∧
        ∀ z ∈ (e t).source, deriv (e t) z ≠ 0 ∧
          deriv (deriv (e t)) z = (-2 : ℂ) * A t z * deriv (e t) z := by
  classical
  obtain ⟨H, hH, hnorm, hODE⟩ := parametric_holomorphic_flat_coordinate_g1 hU hconv ha A hA hhol
  have hd : ∀ t, DifferentiableOn ℂ (H t) U :=
    fun t z hz ↦ (hODE t z hz).1.differentiableWithinAt
  obtain ⟨r, hr, hrU, hinj⟩ := compact_holomorphic_family_uniform_injective_g1
    hU ha H hH hd (fun t ↦ (hnorm t).2)
  have hcharts (t : T) := holomorphic_injective_openPartialHomeomorph_g1
    Metric.isOpen_ball ((hd t).mono hrU) (hinj t) (fun z hz ↦ (hODE t z (hrU hz)).2.1)
  choose e hes heH hsm hinv using hcharts
  refine ⟨r, e, hr, hrU, ?_, ?_⟩
  · apply (hH.mono (Set.prod_mono_right hrU)).congr
    intro p hp
    exact congrFun (heH p.1) p.2
  · intro t
    refine ⟨hes t, ?_, ?_, hsm t, hinv t, ?_⟩
    · simpa only [heH] using (hnorm t).1
    · simpa only [heH] using (hnorm t).2
    · intro z hz
      simpa only [heH] using (hODE t z (hrU (hes t ▸ hz))).2

end HolomorphicAnosov



