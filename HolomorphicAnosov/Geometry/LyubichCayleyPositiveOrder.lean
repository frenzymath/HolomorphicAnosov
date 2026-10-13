import HolomorphicAnosov.Analysis.PositiveCircleLogarithmOrder
import HolomorphicAnosov.Geometry.ConvexFrontierDirection
import HolomorphicAnosov.Geometry.IdealDiskKleinPositiveLogarithm
import HolomorphicAnosov.Analysis.PositiveLogarithmHomotopy
import HolomorphicAnosov.Analysis.CayleyCircleOrder
import HolomorphicAnosov.Analysis.PositiveLogarithmComparison
import Mathlib.Analysis.Complex.Norm

set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov

open Analysis.MarkedRectangle Set
open scoped ComplexConjugate

/-- Positive winding places the first two marks in increasing real Cayley order. (Lyubich, §2.4.13, Exercise 2.49(i)) -/
theorem markedIdealDiskTriangle_cayley_positive_order
    (T : MarkedIdealDiskTriangle)
    (Φ : {z : ℂ | ‖z‖ ≤ 1} ≃ₜ closure T.interiorSet)
    (β : Circle ≃ₜ frontier T.interiorSet)
    (hβΦ : ∀ ζ : Circle,
      (β ζ : ℂ) = (Φ ⟨ζ, (Circle.norm_coe ζ).le⟩ : ℂ))
    (hβpos : ∀ a ∈ T.interiorSet,
      ContinuousOn (fun t : ℝ ↦ (β (Circle.exp (2 * Real.pi * t)) : ℂ)) (Icc 0 1) ∧
      (β (Circle.exp (2 * Real.pi * 0)) : ℂ) = β (Circle.exp (2 * Real.pi * 1)) ∧
      ∃ L : C(Icc (0 : ℝ) 1, ℂ),
        (∀ t, Complex.exp (L t) = (β (Circle.exp (2 * Real.pi * (t : ℝ))) : ℂ) - a) ∧
        L ⟨1, by simp⟩ - L ⟨0, by simp⟩ = (2 * Real.pi : ℂ) * Complex.I)
    (q : Fin 3 → Circle)
    (hq : ∀ i : Fin 3,
      (Φ ⟨q i, (Circle.norm_coe (q i)).le⟩ : ℂ) = T.vertex i) :
    ∃ a b : ℝ, a < b ∧
      Complex.I * (1 + conj (q 2 : ℂ) * (q 0 : ℂ)) /
          (1 - conj (q 2 : ℂ) * (q 0 : ℂ)) = (a : ℂ) ∧
      Complex.I * (1 + conj (q 2 : ℂ) * (q 1 : ℂ)) /
          (1 - conj (q 2 : ℂ) * (q 1 : ℂ)) = (b : ℂ) := by
  have hqinj : Function.Injective q := by
    intro i j hij
    apply T.distinct
    rw [← hq i, ← hq j, hij]
  have hβq (i : Fin 3) : (β (q i) : ℂ) = T.vertex i := (hβΦ _).trans (hq i)
  have hfix (i : Fin 3) : idealDiskKlein (T.vertex i) = T.vertex i := by
    norm_num [idealDiskKlein, T.norm_vertex]
  let S := convexHull ℝ (Set.range T.vertex)
  have hS : Convex ℝ S := convex_convexHull ℝ _
  have hSball : S ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min
    · rintro z ⟨i, rfl⟩
      simp [Metric.mem_closedBall, dist_zero_right, T.norm_vertex]
    · exact convex_closedBall _ _
  have hSint {z : ℂ} (hz : z ∈ interior S) : ‖z‖ < 1 := by
    have hi := interior_mono hSball hz
    rw [interior_closedBall (0 : ℂ) (by norm_num)] at hi
    simpa [Metric.mem_ball, dist_zero_right] using hi
  have hkcont : Continuous idealDiskKlein := by
    have hc := continuous_idealDiskKleinHomotopy.comp
      ((continuous_const (y := (1 : ℝ))).prodMk continuous_id)
    simpa only [Function.comp_def, id_eq, idealDiskKleinHomotopy_one] using hc
  have hβclosed (z : Circle) : ‖(β z : ℂ)‖ ≤ 1 ∧ idealDiskKlein (β z) ∈ S := by
    have hcl : closure T.interiorSet ⊆ {x | ‖x‖ ≤ 1 ∧ idealDiskKlein x ∈ S} := by
      refine closure_minimal ?_ ?_
      · intro x hx
        exact ⟨hx.1.le, interior_subset hx.2⟩
      exact (isClosed_le continuous_norm continuous_const).inter
        (((Set.finite_range T.vertex).isClosed_convexHull ℝ).preimage hkcont)
    exact hcl (β z).property.1
  have hβnorm (z : Circle) : ‖(β z : ℂ)‖ ≤ 1 := (hβclosed z).1
  have hβfront (z : Circle) : idealDiskKlein (β z) ∈ frontier S := by
    refine ⟨subset_closure (hβclosed z).2, ?_⟩
    intro hi
    have hn : ‖(β z : ℂ)‖ < 1 := by
      apply lt_of_le_of_ne (hβnorm z)
      intro he
      have hk : idealDiskKlein (β z) = β z := by norm_num [idealDiskKlein, he]
      have hh := hSint hi
      rw [hk, he] at hh
      exact lt_irrefl _ hh
    apply (β z).property.2
    rw [mem_interior_iff_mem_nhds]
    exact Filter.inter_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hn)
      ((isOpen_interior.preimage hkcont).mem_nhds hi)
  let o : {z : ℂ | ‖z‖ ≤ 1} := ⟨0, by simp⟩
  let a : ℂ := Φ o
  have hain : a ∈ interior T.interiorSet := by
    by_contra hnot
    have haf : a ∈ frontier T.interiorSet := ⟨(Φ o).property, hnot⟩
    obtain ⟨ζ, hζ⟩ := β.surjective ⟨a, haf⟩
    have he : Φ ⟨ζ, (Circle.norm_coe ζ).le⟩ = Φ o := by
      apply Subtype.ext
      exact (hβΦ ζ).symm.trans (congrArg Subtype.val hζ)
    have hz : (ζ : ℂ) = 0 := congrArg Subtype.val (Φ.injective he)
    have hn := Circle.norm_coe ζ
    rw [hz, norm_zero] at hn
    norm_num at hn
  have ha : a ∈ T.interiorSet := interior_subset hain
  let w := idealDiskKlein a
  have hwint : w ∈ interior S := ha.2
  have hwnorm : ‖w‖ < 1 := hSint hwint
  have hβne (z : Circle) : (β z : ℂ) ≠ a := by
    intro he
    exact (β z).property.2 (he.symm ▸ hain)
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  obtain ⟨L, hL, hiL⟩ := (hβpos a ha).2.2
  obtain ⟨K, hK, hiK⟩ := idealDiskKlein_positive_logarithm γ hβnorm a ha.1.le hβne L hL hiL
  let δ : ComplexLoop := ⟨fun z ↦ idealDiskKlein (β z) - w,
    by
      have hc : Continuous (fun z ↦ idealDiskKleinHomotopy 1 (γ z) - w) :=
        (continuous_idealDiskKleinHomotopy.comp
          (continuous_const.prodMk γ.continuous)).sub continuous_const
      simpa only [idealDiskKleinHomotopy_one, γ, ContinuousMap.coe_mk] using hc⟩
  have hδne (z : Circle) : δ z ≠ 0 := by
    intro he
    exact (hβfront z).2 (sub_eq_zero.mp he ▸ hwint)
  obtain ⟨M, hM, hiM⟩ := positive_logarithm_rotate δ hδne K hK hiK (q 2)
  have hinj : Function.Injective (fun z : Circle ↦
      (idealDiskKlein (β z) - w) / (‖idealDiskKlein (β z) - w‖ : ℂ)) := by
    intro x y hxy
    apply β.injective
    apply Subtype.ext
    apply idealDiskKleinHomotopy_injOn (t := 1) (by simp) (hβnorm x) (hβnorm y)
    simpa using convex_frontier_normalized_direction_injective hS hwint (hβfront x) (hβfront y) hxy
  have hMmono : StrictMono (fun t ↦ (M t).im) := by
    apply normalized_loop_log_strictMono (fun z ↦ idealDiskKlein (β (q 2*z))) w
      (fun z he ↦ hδne (q 2*z) (sub_eq_zero.mpr he))
      (hinj.comp (mul_right_injective (q 2))) M hM hiM
  obtain ⟨θ₀, θ₁, θ₂, h01, h12, h20, hv0, hv1, hv2⟩ := T.positive_order
  let v₂ := Circle.exp θ₂
  have hv₂ : (v₂ : ℂ) = T.vertex 2 := hv2.symm
  obtain ⟨N₀, hN₀, hiN₀⟩ := circle_sub_positive_logarithm w hwnorm
  let η : ComplexLoop := ⟨fun z ↦ (z : ℂ) - w, by fun_prop⟩
  have hηne (z : Circle) : η z ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    rw [Circle.norm_coe] at hh
    linarith
  obtain ⟨N, hN, hiN⟩ := positive_logarithm_rotate η hηne N₀ hN₀ hiN₀ v₂
  have hinjCircle : Function.Injective (fun z : Circle ↦
      ((z : ℂ) - w) / (‖(z : ℂ) - w‖ : ℂ)) := by
    intro x y he
    apply Subtype.ext
    apply convex_frontier_normalized_direction_injective (convex_closedBall (0 : ℂ) 1)
      (a := w) ?_ ?_ ?_ he
    · rw [interior_closedBall (0 : ℂ) (by norm_num)]
      simpa [Metric.mem_ball, dist_zero_right] using hwnorm
    · rw [frontier_closedBall (0 : ℂ) (by norm_num)]
      exact x.property
    · rw [frontier_closedBall (0 : ℂ) (by norm_num)]
      exact y.property
  have hNmono : StrictMono (fun t ↦ (N t).im) := by
    apply normalized_loop_log_strictMono (fun z ↦ ((v₂*z : Circle) : ℂ)) w
      (fun z he ↦ hηne (v₂*z) (sub_eq_zero.mpr he))
      (hinjCircle.comp (mul_right_injective v₂)) N hN hiN
  obtain ⟨t₀, ht₀, he₀⟩ := circle_exists_open_turn (q 2) (q 0)
    (fun he ↦ by have := hqinj he; omega)
  obtain ⟨t₁, ht₁, he₁⟩ := circle_exists_open_turn (q 2) (q 1)
    (fun he ↦ by have := hqinj he; omega)
  let s₀ := (θ₀ + 2*Real.pi - θ₂) / (2*Real.pi)
  let s₁ := (θ₁ + 2*Real.pi - θ₂) / (2*Real.pi)
  have hs₀ : s₀ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [s₀]
    constructor
    · apply div_pos _ (by positivity); linarith
    · apply (div_lt_one (by positivity)).mpr; linarith
  have hs₁ : s₁ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [s₁]
    constructor
    · apply div_pos _ (by positivity); linarith
    · apply (div_lt_one (by positivity)).mpr; linarith
  have hs01 : s₀ < s₁ := by
    apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    linarith
  have hvs (θ : ℝ) :
      (v₂ * Circle.exp (2*Real.pi*((θ+2*Real.pi-θ₂)/(2*Real.pi))) : Circle) = Circle.exp θ := by
    rw [mul_div_cancel₀ _ (by positivity)]
    dsimp [v₂]
    rw [← Circle.exp_add]
    convert Circle.exp_add_two_pi θ using 1
    congr 1
    ring
  have hzero : Complex.exp (M 0) = Complex.exp (N 0) := by
    rw [hM, hN]
    change idealDiskKlein (β (q 2 * Circle.exp (2*Real.pi*0))) - w =
      ((v₂ * Circle.exp (2*Real.pi*0) : Circle) : ℂ) - w
    simp only [mul_zero, Circle.exp_zero, mul_one, hβq, hfix, hv₂]
  have hmatch₀ : Complex.exp (M ⟨t₀, ht₀.1.le, ht₀.2.le⟩) =
      Complex.exp (N ⟨s₀, hs₀.1.le, hs₀.2.le⟩) := by
    rw [hM, hN]
    change idealDiskKlein (β (q 2 * Circle.exp (2*Real.pi*t₀))) - w =
      ((v₂ * Circle.exp (2*Real.pi*s₀) : Circle) : ℂ) - w
    rw [he₀, hβq, hfix, hvs]
    exact congrArg (fun z : ℂ ↦ z-w) hv0
  have hmatch₁ : Complex.exp (M ⟨t₁, ht₁.1.le, ht₁.2.le⟩) =
      Complex.exp (N ⟨s₁, hs₁.1.le, hs₁.2.le⟩) := by
    rw [hM, hN]
    change idealDiskKlein (β (q 2 * Circle.exp (2*Real.pi*t₁))) - w =
      ((v₂ * Circle.exp (2*Real.pi*s₁) : Circle) : ℂ) - w
    rw [he₁, hβq, hfix, hvs]
    exact congrArg (fun z : ℂ ↦ z-w) hv1
  have ht01 : t₀ < t₁ := positive_logarithms_order M N hMmono hNmono hiM hiN hzero
    ⟨t₀, ht₀.1.le, ht₀.2.le⟩ ⟨t₁, ht₁.1.le, ht₁.2.le⟩
    ⟨s₀, hs₀.1.le, hs₀.2.le⟩ ⟨s₁, hs₁.1.le, hs₁.2.le⟩
    ht₀ ht₁ hs₀ hs₁ hmatch₀ hmatch₁ hs01
  let C : ℂ → ℂ := fun z ↦ Complex.I * (1 + conj (q 2 : ℂ) * z) /
    (1 - conj (q 2 : ℂ) * z)
  have hreal (z : Circle) : (C z).im = 0 := by
    have hgeneric (w : ℂ) :
        (Complex.I * (1 + w) / (1 - w)).im =
          (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
      simp only [Complex.div_im, Complex.mul_im, Complex.mul_re,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    dsimp only [C]
    rw [hgeneric, norm_mul, Complex.norm_conj, Circle.norm_coe, Circle.norm_coe]
    norm_num
  have hcoe (z : Circle) : C z = ((C z).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  refine ⟨(C (q 0)).re, (C (q 1)).re, ?_, hcoe (q 0), hcoe (q 1)⟩
  have hc (t : ℝ) : C (q 2 * Circle.exp (2*Real.pi*t) : Circle) =
      Complex.I * (1 + (Circle.exp (2*Real.pi*t) : ℂ)) /
        (1 - (Circle.exp (2*Real.pi*t) : ℂ)) := by
    dsimp [C]
    simp only [← mul_assoc, Complex.conj_mul', Circle.norm_coe, one_pow,
      Complex.ofReal_one, one_mul]
  rw [← he₀, ← he₁, hc, hc]
  apply cayley_exp_strictMonoOn
  · constructor <;> nlinarith [Real.pi_pos, ht₀.1, ht₀.2]
  · constructor <;> nlinarith [Real.pi_pos, ht₁.1, ht₁.2]
  · exact mul_lt_mul_of_pos_left ht01 (by positivity)

end HolomorphicAnosov

