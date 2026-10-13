import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Superposition on arbitrary dependent bounded sections

This is the arbitrary-index bridge needed by the HPS graph transform when the
base is a compact invariant set and tangent fibres vary with the base point.
The carrier is Mathlib's dependent `lp` space at exponent infinity, so sections
may be discontinuous and the index may be uncountable.
-/

noncomputable section
namespace HolomorphicAnosov.Analysis
open Set Filter
open scoped Topology _root_.Topology ContDiff

/-- Uniformly differentiable fibre maps induce the ordinary Banach derivative of
superposition on bounded dependent sections. Source: Walter (2014), author
preprint Definitions 4.1.1, 4.2.5--4.2.6, Proposition 4.3.3 and Corollary
4.3.6, pp.10--22; the ordinary norm-Frechet bridge is Walter (2012),
Dissertationes Mathematicae 484, Proposition A.3.2 and Lemma A.3.3,
pp.107--110. The proof uses the same convex mean-value remainder estimate as
Wells (1976), p.288, coordinatewise followed by `lp.norm_le_of_forall_le`.
No topology or differentiability is imposed on the index set.
Correction of the initial draft: the pointwise derivative premise is essential.
With one real fibre, β = id and D = 0, its omission would assert that the
identity has zero derivative. The explicit `hβ` below excludes that counterexample. -/
theorem bounded_dependent_superposition_hasFDerivAt
    {A : Type*} {E F : A → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (s : ℝ) (β : ∀ i, E i → F i)
    (D : ∀ i, E i → E i →L[ℝ] F i)
    (hβ : ∀ i y, y ∈ Metric.ball (0 : E i) s → HasFDerivAt (β i) (D i y) y)
    (C : lp E ⊤ → lp F ⊤)
    (hC : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ i,
      C w i = β i (w i))
    (w : lp E ⊤) (hw : w ∈ Metric.ball (0 : lp E ⊤) s)
    (L : lp E ⊤ →L[ℝ] lp F ⊤)
    (hL : ∀ v i, L v i = D i (w i) (v i))
    (hU : ∀ ε > 0, ∃ δ > 0, ∀ i y,
      ‖y - w i‖ < δ → ‖D i y - D i (w i)‖ < ε) :
    HasFDerivAt C L w := by
  have hcoord (z : lp E ⊤) (i : A) : ‖z i‖ ≤ ‖z‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero z i
  have hw' : ‖w‖ < s := by simpa using hw
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hU ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : lp E ⊤) (lt_min hδ (sub_pos.mpr hw'))]
    with v hv
  have hv' : ‖v‖ < min δ (s - ‖w‖) := by simpa using hv
  have hvδ : ‖v‖ < δ := hv'.trans_le (min_le_left _ _)
  have hwv : ‖w + v‖ < s := (norm_add_le _ _).trans_lt
    (by linarith [hv'.trans_le (min_le_right δ (s - ‖w‖))])
  apply lp.norm_le_of_forall_le (mul_nonneg hε.le (norm_nonneg v))
  intro i
  change ‖C (w + v) i - C w i - L v i‖ ≤ ε * ‖v‖
  rw [hC (w + v) (by simpa using hwv) i, hC w hw i, hL v i]
  let t : Set (E i) := Metric.ball 0 s ∩ Metric.ball (w i) δ
  have ha : w i ∈ t := ⟨by simpa using (hcoord w i).trans_lt hw', by simpa using hδ⟩
  have hb : (w + v) i ∈ t := ⟨by simpa using (hcoord (w + v) i).trans_lt hwv, by
    simpa [dist_eq_norm] using (hcoord v i).trans_lt hvδ⟩
  have hrem := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hs := (convex_ball (0 : E i) s).inter (convex_ball (w i) δ))
    (fun x hx ↦ (hβ i x hx.1).hasFDerivWithinAt)
    (fun x hx ↦ (hbound i x (by simpa [dist_eq_norm] using hx.2)).le) ha hb
  have hh : ‖β i ((w + v) i) - β i (w i) - D i (w i) (v i)‖ ≤ ε * ‖v i‖ := by
    simpa using hrem
  exact hh.trans (mul_le_mul_of_nonneg_left (hcoord v i) hε.le)


/-- Uniform coordinate derivative variation also makes the derivative field continuous
in the supremum operator norm. Hence superposition is ordinary C¹ on the original
open section ball. Source: Walter (2014), Proposition 4.3.3 and Corollary 4.3.6;
Walter (2012), Proposition A.3.2. Fix a section and a tolerance, take the common
coordinate radius, and use the lp bound twice: first on the derivative applied to
an arbitrary bounded section and then in the operator norm. The previous theorem
gives the derivative itself, and the open-domain C¹ criterion concludes. -/
theorem bounded_dependent_superposition_contDiffOn
    {A : Type*} {E F : A → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (s : ℝ) (β : ∀ i, E i → F i)
    (D : ∀ i, E i → E i →L[ℝ] F i)
    (hβ : ∀ i y, y ∈ Metric.ball (0 : E i) s → HasFDerivAt (β i) (D i y) y)
    (C : lp E ⊤ → lp F ⊤)
    (hC : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ i, C w i = β i (w i))
    (L : lp E ⊤ → lp E ⊤ →L[ℝ] lp F ⊤)
    (hL : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ v i, L w v i = D i (w i) (v i))
    (hU : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ ε > 0, ∃ δ > 0, ∀ i y,
      ‖y - w i‖ < δ → ‖D i y - D i (w i)‖ < ε) :
    ContDiffOn ℝ 1 C (Metric.ball (0 : lp E ⊤) s) := by
  have hLcont : ContinuousOn L (Metric.ball (0 : lp E ⊤) s) := by
    intro w hw
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hU w hw (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun z hz hzw ↦ ?_⟩
    have hbound : ‖L z - L w‖ ≤ ε / 2 := by
      apply (L z - L w).opNorm_le_bound (half_pos hε).le
      intro v
      apply lp.norm_le_of_forall_le (mul_nonneg (by positivity) (norm_nonneg v))
      intro i
      change ‖L z v i - L w v i‖ ≤ (ε / 2) * ‖v‖
      rw [hL z hz v i, hL w hw v i]
      have hzi : ‖z i - w i‖ < δ := by
        exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i).trans_lt
          (by simpa only [dist_eq_norm] using hzw)
      calc
        ‖D i (z i) (v i) - D i (w i) (v i)‖ = ‖(D i (z i) - D i (w i)) (v i)‖ := rfl
        _ ≤ ‖D i (z i) - D i (w i)‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (ε / 2) * ‖v i‖ := mul_le_mul_of_nonneg_right (hb i (z i) hzi).le (norm_nonneg _)
        _ ≤ (ε / 2) * ‖v‖ := mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero v i) (by positivity)
    rw [dist_eq_norm]
    exact hbound.trans_lt (half_lt_self hε)
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp, L, ?_, fun w hw ↦ ?_⟩
  · exact contDiffOn_zero.mpr hLcont
  · exact (bounded_dependent_superposition_hasFDerivAt s β D hβ C hC w hw
      (L w) (hL w hw) (hU w hw)).hasFDerivWithinAt


/-- A uniformly bounded, uniformly continuous derivative family on a common ball,
with each fibre map vanishing at zero, defines a C¹ map on the bounded section ball.
Source: Walter (2014), Corollary 4.3.6, specialized to order one. The mean-value
bound makes the coordinate values bounded, `lp.mapCLM` supplies the diagonal
operator, and the preceding theorem supplies C¹. Outside the open ball the chosen
total extension is zero; no regularity is claimed there. -/
theorem exists_bounded_dependent_superposition
    {A : Type*} {E F : A → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (s : ℝ) (hs : 0 < s) (β : ∀ i, E i → F i)
    (D : ∀ i, E i → E i →L[ℝ] F i)
    (hβ : ∀ i y, y ∈ Metric.ball (0 : E i) s → HasFDerivAt (β i) (D i y) y)
    (hzero : ∀ i, β i 0 = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ i y, ‖y‖ < s → ‖D i y‖ ≤ K)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ i x y,
      ‖x‖ < s → ‖y‖ < s → ‖y - x‖ < δ → ‖D i y - D i x‖ < ε) :
    ∃ C : lp E ⊤ → lp F ⊤,
      C 0 = 0 ∧ ContDiffOn ℝ 1 C (Metric.ball (0 : lp E ⊤) s) ∧
      ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ i, C w i = β i (w i) := by
  classical
  have hcoord (w : lp E ⊤) (i : A) : ‖w i‖ ≤ ‖w‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero w i
  have hb (w : lp E ⊤) (hw : w ∈ Metric.ball (0 : lp E ⊤) s) :
      Memℓp (fun i ↦ β i (w i)) ⊤ := by
    apply memℓp_infty
    refine ⟨K * ‖w‖, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hi : ‖w i‖ < s := (hcoord w i).trans_lt (by simpa using hw)
    have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy ↦ (hβ i y hy).hasFDerivWithinAt)
      (fun y hy ↦ hbound i y (by simpa using hy))
      (convex_ball (0 : E i) s) (x := (0 : E i)) (y := w i)
      (by simpa using hs) (by simpa using hi)
    rw [hzero i, sub_zero, sub_zero] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (hcoord w i) hK)
  let C : lp E ⊤ → lp F ⊤ := fun w ↦
    if hw : w ∈ Metric.ball (0 : lp E ⊤) s then ⟨fun i ↦ β i (w i), hb w hw⟩ else 0
  have hC : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ i, C w i = β i (w i) := by
    intro w hw i
    simp only [C, dite_eq_left hw]
  let L : lp E ⊤ → lp E ⊤ →L[ℝ] lp F ⊤ := fun w ↦
    if hw : w ∈ Metric.ball (0 : lp E ⊤) s then
      lp.mapCLM ⊤ (fun i ↦ D i (w i)) hK
        (fun i ↦ hbound i (w i) ((hcoord w i).trans_lt (by simpa using hw))) else 0
  have hL : ∀ w ∈ Metric.ball (0 : lp E ⊤) s, ∀ v i, L w v i = D i (w i) (v i) := by
    intro w hw v i
    simp only [L, dite_eq_left hw]
    rfl
  refine ⟨C, ?_, ?_, hC⟩
  · apply Subtype.ext
    funext i
    change C 0 i = 0
    rw [hC 0 (by simpa using hs) i]
    exact hzero i
  · apply bounded_dependent_superposition_contDiffOn s β D hβ C hC L hL
    intro w hw ε hε
    obtain ⟨δ, hδ, hu⟩ := hunif ε hε
    have hw' : ‖w‖ < s := by simpa using hw
    refine ⟨min δ (s - ‖w‖), lt_min hδ (sub_pos.mpr hw'), ?_⟩
    intro i y hy
    apply hu i (w i) y ((hcoord w i).trans_lt hw')
    · have hy' := hy.trans_le (min_le_right δ (s - ‖w‖))
      have hn : ‖y‖ ≤ ‖y - w i‖ + ‖w i‖ := by simpa only [add_comm] using norm_le_insert' y (w i)
      linarith [hcoord w i]
    · exact hy.trans_le (min_le_left _ _)


end HolomorphicAnosov.Analysis
