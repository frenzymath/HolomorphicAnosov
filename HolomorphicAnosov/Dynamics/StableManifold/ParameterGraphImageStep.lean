import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- The single-fibre image graph transform from HPS, pp.54–55, in the original
product maximum norms (step 3b–c of `parameter_graph_construction`).

For a centered unit-slope input graph, the horizontal image map differs from `T`
by an `ε`-Lipschitz map. The strict inverse-norm bound makes it a global
homeomorphism. Comparing two horizontal equations gives inverse bound
`a / (1 - a * ε)`. The vertical image difference has bound `k + ε` on the
input graph, so the stated smallness inequality preserves unit slope. This
argument allows zero fibres and a singular vertical linear map. -/
theorem parameter_graph_image_step
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V)
    (G : X × Y → U × V) (hG : G 0 = 0)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) ≤ 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (s : X → Y) (hs0 : s 0 = 0) (hs : LipschitzWith 1 s) :
    ∃ H : X ≃ₜ U, ∃ s' : U → V,
      (∀ x, H x = (G (x, s x)).1) ∧ H 0 = 0 ∧
      (∀ u v, ‖H.symm u - H.symm v‖ ≤
        (a : ℝ) / (1 - (a : ℝ) * ε) * ‖u - v‖) ∧
      s' 0 = 0 ∧ LipschitzWith 1 s' ∧
      G '' Set.range (fun x ↦ (x, s x)) = Set.range (fun u ↦ (u, s' u)) := by
  have hG00 : G (0, 0) = (0, 0) := hG
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  let F : X → U := fun x ↦ (G (x, s x)).1
  have hgraph : LipschitzWith 1 (fun x ↦ (x, s x)) := by
    simpa using LipschitzWith.id.prodMk hs
  have hRgraph : ∀ x y, ‖R (x, s x) - R (y, s y)‖ ≤ (ε : ℝ) * ‖x - y‖ := by
    intro x y
    simpa using (hR.comp hgraph).norm_sub_le x y
  have hRfst : ∀ x y, ‖(R (x, s x)).1 - (R (y, s y)).1‖ ≤
      (ε : ℝ) * ‖x - y‖ := fun x y ↦ (norm_fst_le _).trans (hRgraph x y)
  have hF : ∀ x, F x = T x + (R (x, s x)).1 := by
    intro x
    simp [F, R]
  have happrox : ApproximatesLinearOn F T.toContinuousLinearMap univ ε := by
    intro x hx y hy
    have he : F x - F y - T (x - y) =
        (R (x, s x)).1 - (R (y, s y)).1 := by
      rw [hF, hF, map_sub]
      abel
    change ‖F x - F y - T (x - y)‖ ≤ (ε : ℝ) * ‖x - y‖
    rw [he]
    exact hRfst x y
  have hguard : Subsingleton X ∨ ε < ‖T.symm.toContinuousLinearMap‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · right
      have hpos : 0 < ‖T.symm.toContinuousLinearMap‖ := T.norm_symm_pos
      have hlt : (ε : ℝ) < ‖T.symm.toContinuousLinearMap‖⁻¹ := by
        rw [inv_eq_one_div]
        apply (lt_div_iff₀ hpos).2
        calc
          (ε : ℝ) * ‖T.symm.toContinuousLinearMap‖ ≤ (ε : ℝ) * a :=
            mul_le_mul_of_nonneg_left ha ε.2
          _ < 1 := by simpa [mul_comm] using hsmall
      exact_mod_cast hlt
  let H : X ≃ₜ U := happrox.toHomeomorph F hguard
  have hH : ∀ x, H x = F x := fun x ↦ rfl
  have hH0 : H 0 = 0 := by simp [hH, F, hs0, hG00]
  have hden : 0 < 1 - (a : ℝ) * ε := sub_pos.mpr hsmall
  have hinv : ∀ u v, ‖H.symm u - H.symm v‖ ≤
      (a : ℝ) / (1 - (a : ℝ) * ε) * ‖u - v‖ := by
    intro u v
    let x := H.symm u
    let y := H.symm v
    have heq : T (x - y) = (u - v) - ((R (x, s x)).1 - (R (y, s y)).1) := by
      have hx : F x = u := H.apply_symm_apply u
      have hy : F y = v := H.apply_symm_apply v
      rw [hF] at hx hy
      rw [map_sub]
      rw [← hx, ← hy]
      abel
    have hb : ‖x - y‖ ≤ (a : ℝ) *
        (‖u - v‖ + (ε : ℝ) * ‖x - y‖) := calc
      ‖x - y‖ = ‖T.symm (T (x - y))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (x - y)‖ :=
        T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (a : ℝ) * ‖T (x - y)‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ (a : ℝ) * (‖u - v‖ + (ε : ℝ) * ‖x - y‖) := by
        apply mul_le_mul_of_nonneg_left _ a.2
        rw [heq]
        exact (norm_sub_le _ _).trans (add_le_add_right (hRfst x y) _)
    apply (le_of_mul_le_mul_left ?_ hden : ‖x - y‖ ≤ _)
    field_simp
    nlinarith [hb]
  let s' : U → V := fun u ↦ (G (H.symm u, s (H.symm u))).2
  have hvertical : ∀ x y, ‖(G (x, s x)).2 - (G (y, s y)).2‖ ≤
      ((k : ℝ) + ε) * ‖x - y‖ := by
    intro x y
    have hsy : ‖s x - s y‖ ≤ ‖x - y‖ := by simpa using hs.norm_sub_le x y
    have hv := parameter_graph_vertical_estimate T.toContinuousLinearMap S G k ε hk hR
      x y (s x) (s y)
    rw [max_eq_left hsy] at hv
    exact hv.trans (by nlinarith [mul_le_mul_of_nonneg_left hsy k.2])
  have hs' : LipschitzWith 1 s' := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro u v
    have hc : ((k : ℝ) + ε) * ((a : ℝ) / (1 - (a : ℝ) * ε)) ≤ 1 := by
      rw [← mul_div_assoc]
      apply (div_le_one hden).2
      nlinarith [hslope]
    calc
      ‖s' u - s' v‖ ≤ ((k : ℝ) + ε) * ‖H.symm u - H.symm v‖ :=
        hvertical _ _
      _ ≤ ((k : ℝ) + ε) * ((a : ℝ) / (1 - (a : ℝ) * ε) * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (hinv u v) (add_nonneg k.2 ε.2)
      _ ≤ (1 : NNReal) * ‖u - v‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  refine ⟨H, s', hH, hH0, hinv, ?_, hs', ?_⟩
  · have hi : H.symm 0 = 0 := by rw [← hH0, H.symm_apply_apply]
    simp [s', hi, hs0, hG00]
  · ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨H x, ?_⟩
      apply Prod.ext
      · exact hH x
      · simp only [s', H.symm_apply_apply]
    · rintro ⟨u, rfl⟩
      refine ⟨(H.symm u, s (H.symm u)), ⟨H.symm u, rfl⟩, ?_⟩
      apply Prod.ext
      · exact H.apply_symm_apply u
      · rfl



end HolomorphicAnosov
