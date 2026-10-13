import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Uniform normalized flat holomorphic coordinates

Source: Ghys, *Holomorphic Anosov systems*, Lemma 3.2, p.591; the
quantitative primitive estimate used in Lemma 3.3, pp.592–593.
-/

open Set Filter Metric
open scoped _root_.Topology NNReal ContDiff
namespace HolomorphicAnosov

/-- The exact-domain chart constructor used by the uniform flat-coordinate
proof. A holomorphic injection with nonzero derivative has local smooth
inverses; injectivity identifies them with the inverse of its partial equivalence. -/
theorem holomorphic_injective_openPartialHomeomorph_g1
    {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H U) (hinj : InjOn H U)
    (hne : ∀ z ∈ U, deriv H z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ (e : ℂ → ℂ) = H ∧
      ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target := by
  classical
  have hsm : ContDiffOn ℂ ∞ H U := hH.contDiffOn hU
  let pe : PartialEquiv ℂ ℂ := hinj.toPartialEquiv H U
  have hopen : IsOpenMap (U.domRestrict H) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    have hs := hsm.contDiffAt (hU.mem_nhds z.property)
    have hd := ((hH _ z.property).differentiableAt (hU.mem_nhds z.property)).hasDerivAt.hasFDerivAt_equiv (hne _ z.property)
    have hmap := (hs.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv
    change 𝓝 (H z.val) ≤ Filter.map (H ∘ Subtype.val) (𝓝 z)
    rw [← Filter.map_map, map_nhds_subtype_val,
      nhdsWithin_eq_nhds.mpr (hU.mem_nhds z.property), hmap]
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict pe hsm.continuousOn hopen hU
  refine ⟨e, rfl, rfl, hsm, ?_⟩
  intro w hw
  have hp : e.symm w ∈ U := e.map_target hw
  have hd : HasDerivAt e (deriv e (e.symm w)) (e.symm w) :=
    ((hH _ hp).differentiableAt (hU.mem_nhds hp)).hasDerivAt
  exact (e.contDiffAt_symm_deriv (hne _ hp) hw hd
    (hsm.contDiffAt (hU.mem_nhds hp))).contDiffWithinAt

/-- A common coefficient bound gives a common disk on which the normalized
flat coordinate has derivative within one quarter of the identity.

Proof: choose an exponential continuity radius η at zero, and choose
0 < R < δ with 2 C R < η. Integrate -2A on the convex δ-disk, subtract the
value at its center, and call the result P. The convex mean-value estimate
gives |P(z)| ≤ 2 C |z-a|. Integrate exp(P), and again subtract the central
value, obtaining H. Then H(a)=0, H'(a)=1, H''=-2AH', and H' never vanishes.
On the closed R-disk the bound on P and the choice of η give the asserted
uniform derivative bound. C=0 is included by using C+1 in the choice of R.
The radius depends only on C and δ, and not on A or its center. -/
theorem uniform_flat_coordinate_derivative (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ R < δ ∧ ∀ (a : ℂ) (A : ℂ → ℂ),
      DifferentiableOn ℂ A (ball a δ) →
      (∀ z ∈ ball a δ, ‖A z‖ ≤ C) →
      ∃ H : ℂ → ℂ, H a = 0 ∧ deriv H a = 1 ∧
        DifferentiableOn ℂ H (ball a δ) ∧
        (∀ z ∈ ball a δ, deriv H z ≠ 0 ∧
          deriv (deriv H) z = (-2 : ℂ) * A z * deriv H z) ∧
        ∀ z ∈ closedBall a R, ‖deriv H z - 1‖ ≤ (1/4 : ℝ) := by
  obtain ⟨η, hη, hExp⟩ := Metric.continuousAt_iff.mp
    Complex.continuous_exp.continuousAt (1/4 : ℝ) (by norm_num)
  let R := min (δ/2) (η/(4*(C+1)))
  have hden : 0 < 4*(C+1) := by positivity
  have hR : 0 < R := lt_min (by positivity) (div_pos hη hden)
  have hRd : R < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRη : 2*C*R < η := by
    have hbound : R * (4*(C+1)) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  refine ⟨R, hR, hRd, ?_⟩
  intro a A hA hbound
  obtain ⟨P₀, hP₀⟩ := (convex_ball a δ).exists_forall_hasDerivWithinAt
    (hA.const_mul (-2 : ℂ))
  let P := fun z ↦ P₀ z - P₀ a
  have hP {z : ℂ} (hz : z ∈ ball a δ) :
      HasDerivAt P ((-2 : ℂ) * A z) z :=
    ((hP₀ z hz).hasDerivAt (isOpen_ball.mem_nhds hz)).sub_const _
  have hPa : P a = 0 := sub_self _
  have hEa : Complex.exp (P a) = 1 := by rw [hPa, Complex.exp_zero]
  have hE : DifferentiableOn ℂ (fun z ↦ Complex.exp (P z)) (ball a δ) :=
    fun z hz ↦ (hP hz).cexp.differentiableAt.differentiableWithinAt
  obtain ⟨H₀, hH₀⟩ := (convex_ball a δ).exists_forall_hasDerivWithinAt hE
  let H := fun z ↦ H₀ z - H₀ a
  have hH {z : ℂ} (hz : z ∈ ball a δ) :
      HasDerivAt H (Complex.exp (P z)) z :=
    ((hH₀ z hz).hasDerivAt (isOpen_ball.mem_nhds hz)).sub_const _
  have ha : a ∈ ball a δ := mem_ball_self hδ
  refine ⟨H, sub_self _, (hH ha).deriv.trans hEa,
    (fun z hz ↦ (hH hz).differentiableAt.differentiableWithinAt), ?_, ?_⟩
  · intro z hz
    have heq : deriv H =ᶠ[𝓝 z] (fun w ↦ Complex.exp (P w)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact (hH hw).deriv
    refine ⟨by rw [(hH hz).deriv]; exact Complex.exp_ne_zero _, ?_⟩
    rw [heq.deriv_eq, (hP hz).cexp.deriv, (hH hz).deriv]
    ring
  · intro z hz
    have hzδ : z ∈ ball a δ := closedBall_subset_ball hRd hz
    have hPbound : ‖P z‖ ≤ 2*C*‖z-a‖ := by
      have hn (w : ℂ) (hw : w ∈ ball a δ) : ‖(-2 : ℂ) * A w‖ ≤ 2*C := by
        simpa only [norm_mul, norm_neg, Complex.norm_ofNat] using
          mul_le_mul_of_nonneg_left (hbound w hw) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [hPa, sub_zero] using
        (convex_ball a δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun w hw ↦ (hP hw).hasDerivWithinAt) hn ha hzδ
    have hPη : dist (P z) 0 < η := by
      rw [dist_zero_right]
      have hzR : ‖z-a‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
      exact lt_of_le_of_lt (hPbound.trans
        (mul_le_mul_of_nonneg_left hzR (by positivity))) hRη
    simpa only [(hH hzδ).deriv, Complex.exp_zero, dist_eq_norm] using (hExp hPη).le


/-- The same uniform coordinates are injective on their closed disk and contain
an open disk of half the radius in the image of the open disk.

Proof: the derivative estimate and the convex mean-value theorem applied to
H-id give |H(z)-H(w)-(z-w)| ≤ |z-w|/4. This makes H injective and makes it an
approximation of the identity with error 1/4. The quantitative inverse theorem
covers the closed disk of radius 3R/4. A preimage of a point of norm < R/2
has norm displacement < 2R/3 by the same estimate, so belongs to the open
R-disk. All normalizations and the flat-coordinate equation are retained. -/
theorem uniform_flat_coordinate (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ R < δ ∧ ∀ (a : ℂ) (A : ℂ → ℂ),
      DifferentiableOn ℂ A (ball a δ) →
      (∀ z ∈ ball a δ, ‖A z‖ ≤ C) →
      ∃ H : ℂ → ℂ, H a = 0 ∧ deriv H a = 1 ∧
        DifferentiableOn ℂ H (ball a δ) ∧
        (∀ z ∈ ball a δ, deriv H z ≠ 0 ∧
          deriv (deriv H) z = (-2 : ℂ) * A z * deriv H z) ∧
        (∀ z ∈ closedBall a R, ‖deriv H z - 1‖ ≤ (1/4 : ℝ)) ∧
        InjOn H (closedBall a R) ∧ ball (0 : ℂ) (R/2) ⊆ H '' ball a R := by
  obtain ⟨R, hR, hRd, hcoord⟩ := uniform_flat_coordinate_derivative C δ hC hδ
  refine ⟨R, hR, hRd, ?_⟩
  intro a A hA hAbound
  obtain ⟨H, hHa, hH'a, hH, hHflat, hHbound⟩ := hcoord a A hA hAbound
  have happrox : ApproximatesLinearOn H (ContinuousLinearMap.id ℂ ℂ)
      (closedBall a R) (1/4 : ℝ≥0) := by
    intro z hz w hw
    have hderiv (x : ℂ) (hx : x ∈ closedBall a R) :
        HasDerivWithinAt (fun y ↦ H y - y) (deriv H x - 1) (closedBall a R) x := by
      have hxδ := closedBall_subset_ball hRd hx
      exact (((hH x hxδ).differentiableAt (isOpen_ball.mem_nhds hxδ)).hasDerivAt.sub
        (hasDerivAt_id x)).hasDerivWithinAt
    have hestimate := (convex_closedBall a R).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hHbound hw hz
    convert hestimate using 1 <;> simp only [ContinuousLinearMap.id_apply, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    congr 1
    ring
  have hclose (z : ℂ) (hz : z ∈ closedBall a R) :
      (3/4 : ℝ) * ‖z-a‖ ≤ ‖H z‖ := by
    have he := happrox z hz a (mem_closedBall_self hR.le)
    simp only [ContinuousLinearMap.id_apply, hHa, sub_zero, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] at he
    have ht : ‖z-a‖ ≤ ‖H z‖ + ‖H z - (z-a)‖ := by
      calc
        ‖z-a‖ = ‖H z - (H z - (z-a))‖ := by congr 1; ring
        _ ≤ ‖H z‖ + ‖H z - (z-a)‖ := norm_sub_le _ _
    linarith
  have hinj : InjOn H (closedBall a R) := by
    apply happrox.injOn (f' := ContinuousLinearEquiv.refl ℂ ℂ)
    right
    norm_num
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse hR.le (Subset.refl _)
  refine ⟨H, hHa, hH'a, hH, hHflat, hHbound, hinj, ?_⟩
  intro y hy
  have hynorm : ‖y‖ < R/2 := by simpa only [mem_ball, dist_zero_right] using hy
  have hybig : y ∈ closedBall (H a)
      ((((ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse.nnnorm : ℝ)⁻¹ -
        (1/4 : ℝ≥0)) * R) := by
    change dist y (H a) ≤ ((‖(ContinuousLinearMap.id ℂ ℂ)‖₊ : ℝ)⁻¹ -
      ((1/4 : ℝ≥0) : ℝ)) * R
    norm_num [hHa, dist_zero_right]
    linarith
  obtain ⟨z, hz, hzy⟩ := hsurj hybig
  refine ⟨z, ?_, hzy⟩
  rw [mem_ball, dist_eq_norm]
  have he := hclose z hz
  rw [hzy] at he
  linarith

/-- The quantitative primitive is an actual biholomorphic chart on the full
common open disk. Its derivative is nonzero there, so each point has a local
smooth inverse and the restricted map is open. Injectivity lets these inverses
glue to the inverse of the exact-domain partial homeomorphism. -/
theorem uniform_flat_coordinate_chart (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ R < δ ∧ ∀ (a : ℂ) (A : ℂ → ℂ),
      DifferentiableOn ℂ A (ball a δ) →
      (∀ z ∈ ball a δ, ‖A z‖ ≤ C) →
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        e.source = ball a R ∧ e a = 0 ∧ deriv e a = 1 ∧
        ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target ∧
        ball 0 (R/2) ⊆ e.target ∧
        ∀ z ∈ e.source, deriv e z ≠ 0 ∧
          deriv (deriv e) z = (-2 : ℂ) * A z * deriv e z := by
  classical
  obtain ⟨R, hR, hRδ, h⟩ := uniform_flat_coordinate C δ hC hδ
  refine ⟨R, hR, hRδ, ?_⟩
  intro a A hA hAbound
  obtain ⟨H, hHa, hH'a, hH, hODE, _, hinj, himage⟩ := h a A hA hAbound
  have hsub : ball a R ⊆ ball a δ := ball_subset_ball hRδ.le
  obtain ⟨e, hes, heH, hsm, hinv⟩ := holomorphic_injective_openPartialHomeomorph_g1
    isOpen_ball (hH.mono hsub) (hinj.mono ball_subset_closedBall)
    (fun z hz ↦ (hODE z (hsub hz)).1)
  refine ⟨e, hes, ?_, ?_, hsm, hinv, ?_, ?_⟩
  · simpa only [heH] using hHa
  · simpa only [heH] using hH'a
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := himage hw
    have hz' : z ∈ e.source := hes.symm ▸ hz
    rw [← heH] at hzw
    exact hzw ▸ e.map_source hz'
  · intro z hz
    simpa only [heH] using hODE z (hsub (hes ▸ hz))

end HolomorphicAnosov

