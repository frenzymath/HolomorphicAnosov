import HolomorphicAnosov.Analysis.Complex.ConwayDiskMobius
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The omitted-value improvement in Conway's mapping theorem

Source: Conway, *Functions of One Complex Variable*, VII Lemma 4.3, pp.161–162.
-/
namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- A zero-normalized injective holomorphic disk map that omits a disk value cannot
maximize the modulus of its derivative among such maps when the domain has the
holomorphic square-root property.

Source: Conway VII Lemma 4.3, pp.161–162, equation (4.6) and its derivative computation.
Move an omitted value `w` to zero by a disk Möbius map, take a holomorphic square
root `h`, and move `h(a)` to zero by another disk Möbius map. Each operation preserves
injectivity and disk-valuedness. Put `b=|h(a)|`, so `b²=|w|` and `0<b<1`.
Differentiating the square identity and the two Möbius maps shows that the new
normalized derivative has modulus `|f′(a)|(1+b²)/(2b)`. This is strictly larger
because `(1-b)²>0`. The omitted value cannot be zero because `f(a)=0`, so all
cancellations use strictly positive factors. This modulus-only conclusion does not
need the final unit rotation used by Conway to make the new derivative positive.
No branch of the real square root is needed in the calculation. -/
theorem conway_square_root_derivative_improvement
    {U : Set ℂ} (hU : IsOpen U)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hfm : MapsTo f U (Metric.ball (0 : ℂ) 1)) (hfa : f a = 0)
    (hfd : deriv f a ≠ 0)
    {w : ℂ} (hw : ‖w‖ < 1) (hwomit : w ∉ f '' U) :
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k U ∧ InjOn k U ∧
      MapsTo k U (Metric.ball (0 : ℂ) 1) ∧ k a = 0 ∧
      ‖deriv f a‖ < ‖deriv k a‖ := by
  let T : ℂ → ℂ := fun z ↦ (z - w) / (1 - conj w * z)
  obtain ⟨hT, hTi, hTm, hTw, hTd⟩ := conway_disk_mobius w hw
  let q : ℂ → ℂ := fun z ↦ T (f z)
  have hq : DifferentiableOn ℂ q U := hT.comp hf hfm
  have hqi : InjOn q U := hTi.comp hfi hfm
  have hqm : MapsTo q U (Metric.ball (0 : ℂ) 1) := hTm.comp hfm
  have hq0 : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz he
    have heq : T (f z) = T w := he.trans hTw.symm
    have := hTi (hfm hz) (mem_ball_zero_iff.mpr hw) heq
    exact hwomit ⟨z, hz, this⟩
  obtain ⟨h, hh, hsq⟩ := hsqrt q hq hq0
  have hhi : InjOn h U := by
    intro x hx y hy he
    apply hqi hx hy
    rw [← hsq x hx, ← hsq y hy, he]
  have hhm : MapsTo h U (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have heq := congrArg norm (hsq z hz)
    rw [norm_pow] at heq
    have hb := mem_ball_zero_iff.mp (hqm hz)
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg (h z)]
  have hbeta : ‖h a‖ < 1 := mem_ball_zero_iff.mp (hhm ha)
  have hbeta0 : h a ≠ 0 := by
    intro he
    have := hsq a ha
    simp only [he, zero_pow (by decide : 2 ≠ 0)] at this
    exact hq0 a ha this.symm
  let k : ℂ → ℂ := fun z ↦ (h z - h a) / (1 - conj (h a) * h z)
  obtain ⟨hS, hSi, hSm, hSa, hSd⟩ := conway_disk_mobius (h a) hbeta
  refine ⟨k, hS.comp hh hhm, hSi.comp hhi hhm, hSm.comp hhm, hSa, ?_⟩
  have hqa : q a = -w := by simp [q, T, hfa]
  have hb2 : ‖h a‖ ^ 2 = ‖w‖ := by
    have := congrArg norm (hsq a ha)
    simpa only [norm_pow, hqa, norm_neg] using this
  have hqd : HasDerivAt q ((1 - conj w * w) * deriv f a) a := by
    have H := (hTd (f a) (hfm ha)).comp a
      ((hf a ha).differentiableAt (hU.mem_nhds ha)).hasDerivAt
    simpa only [q, T, Function.comp_def, hfa, mul_zero, sub_zero, one_pow, div_one] using H
  have heqder : 2 * h a * deriv h a = (1 - conj w * w) * deriv f a := by
    have H := (((hh a ha).differentiableAt (hU.mem_nhds ha)).hasDerivAt.pow 2)
    have Heq : (fun z ↦ h z ^ 2) =ᶠ[nhds a] q := by
      filter_upwards [hU.mem_nhds ha] with z hz using hsq z hz
    have H' := H.congr_of_eventuallyEq Heq.symm
    have := H'.unique hqd
    simpa using this
  have hkd : HasDerivAt k
      (((1 - conj (h a) * h a) / (1 - conj (h a) * h a) ^ 2) * deriv h a) a :=
    (hSd (h a) (hhm ha)).comp a
      ((hh a ha).differentiableAt (hU.mem_nhds ha)).hasDerivAt
  have hnormw : ‖1 - conj (w) * (w)‖ = 1 - ‖w‖ ^ 2 := by
    rw [Complex.conj_mul']
    have he : (1 : ℂ) - (‖w‖ : ℂ) ^ 2 = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    nlinarith [norm_nonneg (w)]
  have hnormh : ‖1 - conj (h a) * (h a)‖ = 1 - ‖h a‖ ^ 2 := by
    rw [Complex.conj_mul']
    have he : (1 : ℂ) - (‖h a‖ : ℂ) ^ 2 = ((1 - ‖h a‖ ^ 2 : ℝ) : ℂ) := by simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    nlinarith [norm_nonneg (h a)]
  have heqnorm := congrArg norm heqder
  simp only [norm_mul, hnormw] at heqnorm
  norm_num at heqnorm
  have hknorm : ‖deriv k a‖ * (1 - ‖h a‖ ^ 2) = ‖deriv h a‖ := by
    rw [hkd.deriv, norm_mul, norm_div, norm_pow, hnormh]
    have hp : 0 < 1 - ‖h a‖ ^ 2 := by nlinarith [norm_nonneg (h a)]
    field_simp
  have haPos : 0 < ‖deriv f a‖ := norm_pos_iff.mpr hfd
  have hbPos : 0 < ‖h a‖ := norm_pos_iff.mpr hbeta0
  have hbGap : 0 < 1 - ‖h a‖ ^ 2 := by nlinarith
  have hratio : 2 * ‖h a‖ * ‖deriv k a‖ = (1 + ‖h a‖ ^ 2) * ‖deriv f a‖ := by
    have hfactor : (1 - ‖h a‖ ^ 2) *
        (2 * ‖h a‖ * ‖deriv k a‖ - (1 + ‖h a‖ ^ 2) * ‖deriv f a‖) = 0 := by
      rw [← hb2] at heqnorm
      linear_combination 2 * ‖h a‖ * hknorm + heqnorm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hbGap))
  have hgap : 0 < (1 - ‖h a‖) ^ 2 := sq_pos_of_pos (sub_pos.mpr hbeta)
  have hprod := mul_pos haPos hgap
  nlinarith

end HolomorphicAnosov
