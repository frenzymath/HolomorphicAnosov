import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- The full preimage graph transform of HPS, *Invariant Manifolds*, pp.56–57.
For each fixed vertical coordinate, solve the horizontal equation by the global
inverse theorem for a perturbation of `T`. Its error has Lipschitz constant
`2 * ε`, even if `S` is singular. Comparing two solutions in the product maximum
norm shows that a horizontal difference larger than the vertical difference
would contradict `a * (k + 2 * ε) < 1`. Thus the solution graph has unit slope.
The solution for vertical coordinate zero is zero, and uniqueness gives equality
with the entire preimage, rather than just an included graph. -/
theorem parameter_graph_preimage_step
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V)
    (G : X × Y → U × V) (hG : G 0 = 0)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * (2 * ε) < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (t : V → U) (ht0 : t 0 = 0) (ht : LipschitzWith 1 t) :
    ∃ t' : Y → X, t' 0 = 0 ∧ LipschitzWith 1 t' ∧
      G ⁻¹' Set.range (fun v ↦ (t v, v)) = Set.range (fun y ↦ (t' y, y)) := by
  let R : X × Y → U × V := fun z ↦ G z - (T z.1, S z.2)
  let F : Y → X → U := fun y x ↦ (G (x, y)).1 - t (G (x, y)).2
  have hRbound (x x' : X) (y y' : Y) :
      ‖R (x, y) - R (x', y')‖ ≤
        (ε : ℝ) * max ‖x - x'‖ ‖y - y'‖ := by
    simpa only [R, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using hR.norm_sub_le (x,y) (x',y')
  have hvertical (x x' : X) (y y' : Y) :
      ‖(G (x, y)).2 - (G (x', y')).2‖ ≤
        (k : ℝ) * ‖y - y'‖ + (ε : ℝ) * max ‖x - x'‖ ‖y - y'‖ :=
    parameter_graph_vertical_estimate T.toContinuousLinearMap S G k ε hk hR x x' y y'
  have happrox (y : Y) : ApproximatesLinearOn (F y) T.toContinuousLinearMap univ (2 * ε) := by
    intro x hx x' hx'
    have he : F y x - F y x' - T (x - x') =
        ((R (x,y)).1 - (R (x',y)).1) - (t (G (x,y)).2 - t (G (x',y)).2) := by
      simp only [F, R, Prod.fst_sub, map_sub]
      abel
    change ‖F y x - F y x' - T (x - x')‖ ≤ (↑(2 * ε) : ℝ) * ‖x - x'‖
    rw [he]
    have hr := (norm_fst_le _).trans (hRbound x x' y y)
    have hv := (ht.norm_sub_le (G (x,y)).2 (G (x',y)).2).trans
      (by simpa using hvertical x x' y y)
    simp only [sub_self, norm_zero, max_eq_left (norm_nonneg _)] at hr hv
    calc
      _ ≤ ‖(R (x,y)).1 - (R (x',y)).1‖ + ‖t (G (x,y)).2 - t (G (x',y)).2‖ := norm_sub_le _ _
      _ ≤ (ε : ℝ) * ‖x - x'‖ + (ε : ℝ) * ‖x - x'‖ := add_le_add hr hv
      _ = _ := by push_cast; ring
  have hguard : Subsingleton X ∨ 2 * ε < ‖T.symm.toContinuousLinearMap‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · right
      have hpos := T.norm_symm_pos
      have hlt : (2 * (ε : ℝ)) < ‖T.symm.toContinuousLinearMap‖⁻¹ := by
        rw [inv_eq_one_div]
        apply (lt_div_iff₀ hpos).2
        calc
          2 * (ε : ℝ) * ‖T.symm.toContinuousLinearMap‖ ≤ 2 * (ε : ℝ) * a :=
            mul_le_mul_of_nonneg_left ha (by positivity)
          _ < 1 := by nlinarith [hsmall]
      exact_mod_cast hlt
  let H (y : Y) : X ≃ₜ U := (happrox y).toHomeomorph (F y) hguard
  let t' : Y → X := fun y ↦ (H y).symm 0
  have ht'eq (y : Y) : (G (t' y, y)).1 = t (G (t' y, y)).2 := by
    have he : F y (t' y) = 0 := (H y).apply_symm_apply 0
    exact sub_eq_zero.mp he
  have huniq (x : X) (y : Y) (hxy : (G (x,y)).1 = t (G (x,y)).2) : x = t' y := by
    apply (H y).injective
    change F y x = F y (t' y)
    rw [show F y x = 0 from sub_eq_zero.mpr hxy]
    exact ((H y).apply_symm_apply 0).symm
  have hzero : t' 0 = 0 := by
    symm
    apply huniq
    have h00 : G (0,0) = (0,0) := hG
    simp [h00, ht0]
  have hlip : LipschitzWith 1 t' := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro y y'
    simp only [NNReal.coe_one, one_mul]
    by_contra hn
    have hlt : ‖y - y'‖ < ‖t' y - t' y'‖ := lt_of_not_ge hn
    have he : T (t' y - t' y') =
        (t (G (t' y,y)).2 - t (G (t' y',y')).2) -
          ((R (t' y,y)).1 - (R (t' y',y')).1) := by
      simp only [R, Prod.fst_sub, map_sub]
      rw [ht'eq y, ht'eq y']
      abel
    have htn : ‖t (G (t' y,y)).2 - t (G (t' y',y')).2‖ ≤
        (k : ℝ) * ‖y - y'‖ + (ε : ℝ) * ‖t' y - t' y'‖ := by
      have hh : ‖t (G (t' y,y)).2 - t (G (t' y',y')).2‖ ≤
          ‖(G (t' y,y)).2 - (G (t' y',y')).2‖ := by
        simpa using ht.norm_sub_le (G (t' y,y)).2 (G (t' y',y')).2
      exact hh.trans
        (by simpa only [max_eq_left hlt.le] using hvertical (t' y) (t' y') y y')
    have hrn : ‖(R (t' y,y)).1 - (R (t' y',y')).1‖ ≤
        (ε : ℝ) * ‖t' y - t' y'‖ := by
      exact (norm_fst_le _).trans
        (by simpa only [max_eq_left hlt.le] using hRbound (t' y) (t' y') y y')
    have hbound : ‖t' y - t' y'‖ ≤ (a : ℝ) *
        ((k : ℝ) * ‖y - y'‖ + 2 * (ε : ℝ) * ‖t' y - t' y'‖) := calc
      _ = ‖T.symm (T (t' y - t' y'))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (t' y - t' y')‖ := T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (a : ℝ) * ‖T (t' y - t' y')‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ a.2
        rw [he]
        have hh := (norm_sub_le _ _).trans (add_le_add htn hrn)
        linarith [hh]
    have hdy : (a : ℝ) * k * ‖y - y'‖ ≤ (a : ℝ) * k * ‖t' y - t' y'‖ :=
      mul_le_mul_of_nonneg_left hlt.le (mul_nonneg a.2 k.2)
    have hpos : 0 < ‖t' y - t' y'‖ := (norm_nonneg _).trans_lt hlt
    nlinarith [mul_lt_mul_of_pos_right hslope hpos]
  refine ⟨t', hzero, hlip, ?_⟩
  ext z
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨z.2, ?_⟩
    have hx : z.1 = t' z.2 := huniq z.1 z.2 (by
      have hv1 := congrArg Prod.fst hv
      have hv2 := congrArg Prod.snd hv
      simp only at hv1 hv2
      rw [← hv2]
      exact hv1.symm)
    exact Prod.ext hx.symm rfl
  · rintro ⟨y, rfl⟩
    exact ⟨(G (t' y,y)).2, Prod.ext (ht'eq y).symm rfl⟩

end HolomorphicAnosov
