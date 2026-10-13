import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas
import HolomorphicAnosov.Analysis.Regularity.MontgomeryDerivativeBoundClosed

/-!
This file proves dense joint continuity for a directional derivative (Montgomery, 1945).
-/ 

namespace HolomorphicAnosov.Analysis.Regularity

open Set Filter
open scoped Topology _root_.Topology

/-- For each fixed spatial point, the parameters at which its coordinate partial derivative is jointly continuous form a dense Gδ set in the parameter subspace, with its original normed-space subspace topology. (Montgomery, 1945) -/
theorem montgomery_directional_derivative_dense_joint_continuity
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Set V) (hW : IsOpen W)
    (a : E) (R : ℝ) (d : E)
    (F H : V × E → ℝ)
    (hF : ContinuousOn F (W ×ˢ Metric.ball a R))
    (hderiv : ∀ v ∈ W, ∀ y ∈ Metric.ball a R,
      HasDerivAt (fun t : ℝ ↦ F (v, y + t • d))
        (H (v, y)) 0)
    (hH : ∀ v ∈ W, ContinuousOn (fun y ↦ H (v, y)) (Metric.ball a R)) :
    ∀ y₀ ∈ Metric.ball a R,
      Dense {v : W | ContinuousWithinAt H (W ×ˢ Metric.ball a R)
        (v.val, y₀)} ∧
      IsGδ {v : W | ContinuousWithinAt H (W ×ˢ Metric.ball a R)
        (v.val, y₀)} := by
  intro y₀ hy₀
  constructor
  · let : LocallyCompactSpace W := hW.locallyCompactSpace
    let I := {q : ℚ // 0 < q} × ℚ
    let U : I → Set E := fun p ↦
      Metric.ball y₀ (p.1.val : ℝ) ∩ Metric.ball a R
    have hUo (p : I) : IsOpen (U p) := Metric.isOpen_ball.inter Metric.isOpen_ball
    have hUy (p : I) : y₀ ∈ U p :=
      ⟨Metric.mem_ball_self (by exact_mod_cast p.1.property), hy₀⟩
    let C : ℕ → I → Set W := fun k p ↦
      {v | ∀ y ∈ U p, ‖H (v.val, y) - (p.2 : ℝ)‖ ≤ 1 / (k + 1 : ℝ)}
    have hCc (k : ℕ) (p : I) : IsClosed (C k p) := by
      apply montgomery_isClosed_derivative_bound (U p) (hUo p)
        ((convex_ball y₀ _).inter (convex_ball a R)) (d)
        (fun v : W ↦ fun y ↦ F (v.val, y)) (fun v : W ↦ fun y ↦ H (v.val, y))
      · intro y hy
        exact hF.comp_continuous (continuous_subtype_val.prodMk continuous_const)
          (fun v ↦ ⟨v.property, hy.2⟩)
      · intro v y hy
        exact hderiv v.val v.property y hy.2
      · positivity
    have hcover (k : ℕ) : ⋃ p : I, C k p = univ := by
      apply eq_univ_of_forall
      intro v
      have hε : 0 < 1 / (k + 1 : ℝ) := by positivity
      obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn
        (show H (v.val, y₀) - (1 / (k + 1 : ℝ)) / 2 <
            H (v.val, y₀) + (1 / (k + 1 : ℝ)) / 2 by linarith)
      obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousWithinAt_iff.mp
        (hH v.val v.property y₀ hy₀) _ (half_pos hε)
      obtain ⟨ρ, hρ, hρδ⟩ := exists_rat_btwn hδ
      let p : I := (⟨ρ, by exact_mod_cast hρ⟩, q)
      refine mem_iUnion.mpr ⟨p, ?_⟩
      intro y hy
      have hb := hδbound hy.2 (lt_trans hy.1 hρδ)
      have hq : ‖H (v.val, y₀) - (q : ℝ)‖ < (1 / (k + 1 : ℝ)) / 2 := by
        rw [Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      have ht := dist_triangle (H (v.val, y)) (H (v.val, y₀)) (q : ℝ)
      simp only [dist_eq_norm] at ht hb
      change ‖H (v.val, y) - (q : ℝ)‖ ≤ _
      linarith
    let Good : ℕ → Set W := fun k ↦ ⋃ p : I, interior (C k p)
    have hVd (k : ℕ) : Dense (Good k) := dense_iUnion_interior_of_closed (hCc k) (hcover k)
    have hVo (k : ℕ) : IsOpen (Good k) := isOpen_iUnion (fun _ ↦ isOpen_interior)
    apply (dense_iInter_of_isOpen hVo hVd).mono
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨p, hp⟩ := mem_iUnion.mp (mem_iInter.mp hv k)
    let O : Set V := Subtype.val '' interior (C k p)
    have hOo : IsOpen O := hW.isOpenMap_subtype_val _ isOpen_interior
    have hvO : v.val ∈ O := ⟨v, hp, rfl⟩
    have hN : O ×ˢ U p ∈ 𝓝 (v.val, y₀) :=
      (hOo.prod (hUo p)).mem_nhds ⟨hvO, hUy p⟩
    filter_upwards [hN] with z hz
    obtain ⟨w, hw, hwz⟩ := hz.1
    have hb₁ := (interior_subset hw) z.2 hz.2
    have hb₂ := (interior_subset hp) y₀ (hUy p)
    have htri := dist_triangle (H z) (p.2 : ℝ) (H (v.val, y₀))
    simp only [dist_eq_norm] at htri
    have hwz' : (w.val, z.2) = z := Prod.ext hwz rfl
    rw [hwz'] at hb₁
    rw [norm_sub_rev (p.2 : ℝ)] at htri
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (htri.trans (add_le_add hb₁ hb₂)) (by linarith)
  · have hg := (IsGδ.setOfPred_continuousAt H).preimage
      (f := fun v : W ↦ (v.val, y₀))
      (continuous_subtype_val.prodMk (continuous_const (y := y₀)))
    convert hg using 1
    ext v
    exact continuousWithinAt_iff_continuousAt
      ((hW.prod Metric.isOpen_ball).mem_nhds ⟨v.property, hy₀⟩)


end HolomorphicAnosov.Analysis.Regularity

