import HolomorphicAnosov.Analysis.SchwarzChristoffelPrimitive
import HolomorphicAnosov.Analysis.SchwarzChristoffelDiskBoundary
import HolomorphicAnosov.Analysis.SchwarzChristoffelBoundaryBranch
import HolomorphicAnosov.Analysis.HolomorphicBoundaryPrimitiveIncrement
import HolomorphicAnosov.Analysis.MarkedRectangleG3InverseCayleyInfinity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set
open Filter
open scoped Topology _root_.Topology
open scoped Interval

/-- The Schwarz–Christoffel primitive extends continuously to the finite closed
upper half-plane, with the same interior values and derivative.

Source: Bak–Newman, Complex Analysis (third edition, 2010), Theorem 13.16
pp.183–184 and the real-boundary primitive passage pp.189–190; the disk extension
is supplied by the explicit Cayley/Mashreghi adapter.

Proof: take the global primitive and extend its Cayley pullback to the closed
unit disk. The inverse Cayley function N(w)=(w-i)/(w+i) is continuous on the
closed upper half-plane, maps it into the closed disk and maps its interior
into the open disk: the denominator/numerator squared-norm difference is
4 Im(w). Define Wbar(w)=Fbar(N(w)). The identity C(N(w))=w proves agreement
with the same W in the interior. Composition proves boundary continuity.
On each real interval avoiding the prevertices, the downward-cut branch is
holomorphic on the upper rectangle and agrees with the principal expression.
The real-path boundary increment theorem identifies Wbar(b)-Wbar(a) with
the integral of that expression. Finally, both real infinities approach the
same inverse-Cayley boundary point, so continuity of Fbar gives one shared
finite limit for Wbar at +∞ and −∞. -/
theorem exists_marked_rectangle_g3_primitive_with_boundary
    (x : Fin 4 → ℝ) (hx : Function.Injective x) :
    ∃ W Wbar : ℂ → ℂ,
      (∀ w : ℂ, 0 < w.im →
        HasDerivAt W (-Complex.I * ∏ j : Fin 4,
          Complex.exp (-Complex.log (w - (x j : ℂ)) / 2)) w ∧
        deriv W w ≠ 0 ∧
        (deriv W w)^2 = -(∏ j : Fin 4, (w - (x j : ℂ)))⁻¹) ∧
      EqOn Wbar W {w : ℂ | 0 < w.im} ∧
      ContinuousOn Wbar {w : ℂ | 0 ≤ w.im} ∧
      (∀ a b : ℝ, a ≤ b → (∀ j, x j ∉ Icc a b) →
        Wbar (b : ℂ) - Wbar (a : ℂ) =
          ∫ t in a..b, -Complex.I * ∏ j : Fin 4,
            Complex.exp (-Complex.log ((t : ℂ) - (x j : ℂ)) / 2)) ∧
      (∃ L : ℂ, Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atTop (𝓝 L) ∧
        Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atBot (𝓝 L)) := by
  obtain ⟨W, hW⟩ := exists_schwarzChristoffel_primitive x
  obtain ⟨Fbar, heq, hcont⟩ := schwarzChristoffel_primitive_continuous_extension x hx W
    (fun w hw ↦ ⟨(hW w hw).1.differentiableAt, (hW w hw).2.2⟩)
  let N : ℂ → ℂ := fun w ↦ (w - Complex.I) / (w + Complex.I)
  have hden (w : ℂ) (hw : 0 ≤ w.im) : w + Complex.I ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    linarith
  have hsq (w : ℂ) : ‖w + Complex.I‖ ^ 2 - ‖w - Complex.I‖ ^ 2 = 4 * w.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  have hNle (w : ℂ) (hw : 0 ≤ w.im) : ‖N w‖ ≤ 1 := by
    dsimp only [N]
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden w hw))]
    have hs := hsq w
    nlinarith [norm_nonneg (w - Complex.I), norm_nonneg (w + Complex.I)]
  have hNlt (w : ℂ) (hw : 0 < w.im) : ‖N w‖ < 1 := by
    dsimp only [N]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden w hw.le))]
    have hs := hsq w
    nlinarith [norm_nonneg (w - Complex.I), norm_nonneg (w + Complex.I)]
  have hNcont : ContinuousOn N {w : ℂ | 0 ≤ w.im} := by
    exact (continuous_id.sub continuous_const).continuousOn.div
      (continuous_id.add continuous_const).continuousOn (fun w hw ↦ hden w hw)
  have hWbarEq : EqOn (fun w ↦ Fbar (N w)) W {w : ℂ | 0 < w.im} := by
    intro w hw
    change Fbar (N w) = W w
    rw [heq (hNlt w hw)]
    change W (Complex.I * (1 + N w) / (1 - N w)) = W w
    apply congrArg W
    have hNne : 1 - N w ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have hn := hNlt w hw
      rw [← he] at hn
      simp at hn
    dsimp only [N] at hNne ⊢
    field_simp [hden w hw.le, hNne]
    ring

  let Wbar : ℂ → ℂ := fun w ↦ Fbar (N w)
  have hWbarCont : ContinuousOn Wbar {w : ℂ | 0 ≤ w.im} := hcont.comp hNcont hNle
  have hone : (1 : ℂ) ∈ {z : ℂ | ‖z‖ ≤ 1} := by simp
  have hFbar_one : ContinuousWithinAt Fbar {z : ℂ | ‖z‖ ≤ 1} 1 := hcont 1 hone
  have hN_top : Tendsto (fun t : ℝ ↦ N (t : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa [N] using inverseCayley_real_tendsto_one
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
      (Filter.Eventually.mono (eventually_ne_atTop (0 : ℝ)) (fun t ht ↦ ht))
  have hN_bot : Tendsto (fun t : ℝ ↦ N (t : ℂ)) atBot (𝓝 (1 : ℂ)) := by
    simpa [N] using inverseCayley_real_tendsto_one
      (tendsto_inv_atBot_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atBot (𝓝 0))
      (Filter.Eventually.mono (eventually_ne_atBot (0 : ℝ)) (fun t ht ↦ ht))
  have hN_topWithin : Tendsto (fun t : ℝ ↦ N (t : ℂ)) atTop
      (𝓝[{z : ℂ | ‖z‖ ≤ 1}] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hN_top
      (Filter.Eventually.of_forall (fun t ↦ hNle (t : ℂ) (by simp)))
  have hN_botWithin : Tendsto (fun t : ℝ ↦ N (t : ℂ)) atBot
      (𝓝[{z : ℂ | ‖z‖ ≤ 1}] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hN_bot
      (Filter.Eventually.of_forall (fun t ↦ hNle (t : ℂ) (by simp)))
  have hWbar_top : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atTop (𝓝 (Fbar 1)) := by
    exact hFbar_one.tendsto.comp hN_topWithin
  have hWbar_bot : Tendsto (fun t : ℝ ↦ Wbar (t : ℂ)) atBot (𝓝 (Fbar 1)) := by
    exact hFbar_one.tendsto.comp hN_botWithin
  refine ⟨W, Wbar, hW, hWbarEq, hWbarCont, ?_, ⟨Fbar 1, hWbar_top, hWbar_bot⟩⟩
  intro a b hab hxavoid
  let G : ℂ → ℂ := fun z ↦ -Complex.I * ∏ j : Fin 4,
    Complex.exp (-(Complex.log (-Complex.I * (z - (x j : ℂ))) -
      Complex.log (-Complex.I)) / 2)
  have hbranch := (schwarzChristoffel_boundary_branch x).1
  have hnonvertex (z : ℂ) (hz : z.re ∈ Icc a b) : ∀ j, z ≠ (x j : ℂ) := by
    intro j he
    apply hxavoid j
    simpa [he] using hz
  have hGcont : ContinuousOn G {z : ℂ | z.re ∈ Icc a b ∧ z.im ∈ Icc (0 : ℝ) 1} := by
    intro z hz
    exact (hbranch z hz.2.1 (hnonvertex z hz.1)).1.continuousAt.continuousWithinAt
  have hGder : ∀ z : ℂ, 0 < z.im → HasDerivAt W (G z) z := by
    intro z hz
    have hne : ∀ j, z ≠ (x j : ℂ) := by
      intro j he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    rw [show G z = -Complex.I * ∏ j : Fin 4,
      Complex.exp (-Complex.log (z - (x j : ℂ)) / 2) from (hbranch z hz.le hne).2]
    exact (hW z hz).1
  rw [holomorphic_boundary_primitive_increment W Wbar G a b hab
    hGder hWbarEq hWbarCont hGcont]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  exact (hbranch (t : ℂ) (by simp) (hnonvertex t ht')).2

end HolomorphicAnosov.Analysis.MarkedRectangle

