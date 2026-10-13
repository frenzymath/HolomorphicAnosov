import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse

noncomputable section
open scoped ContDiff ENat NNReal Topology _root_.Topology
namespace HolomorphicAnosov

/-- A smooth homeomorphism that is a sufficiently small Lipschitz perturbation of a continuous linear equivalence has a smooth inverse (Wells, pp.285–287). -/
theorem parameter_graph_smooth_inverse
    {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (T : X ≃L[ℝ] U) (H : X ≃ₜ U) (r : ℕ∞) (hr : 1 ≤ r)
    (hH : ContDiff ℝ (r : ℕ∞ω) (H : X → U))
    (a ε : NNReal) (hT : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun x ↦ H x - T x)) :
    ContDiff ℝ (r : ℕ∞ω) (H.symm : U → X) := by
  let Γ : X → X := fun x ↦ -(T.symm (H x - T x))
  have hΓ : ContDiff ℝ (r : ℕ∞ω) Γ :=
    (T.symm.contDiff.comp (hH.sub T.contDiff)).neg
  have hΓlip : ∀ x ∈ (Set.univ : Set X), ∀ y ∈ (Set.univ : Set X),
      ‖Γ x - Γ y‖ ≤ ((a : ℝ) * ε) * ‖x-y‖ := by
    intro x _ y _
    calc
      _ = ‖T.symm ((H x-T x) - (H y-T y))‖ := by
        change ‖-(T.symm (H x-T x)) - -(T.symm (H y-T y))‖ = _
        rw [neg_sub_neg, norm_sub_rev, ← map_sub]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖(H x-T x) - (H y-T y)‖ :=
        T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (a : ℝ) * ((ε : ℝ) * ‖x-y‖) := mul_le_mul hT (hR.norm_sub_le x y)
        (norm_nonneg _) a.2
      _ = _ := (mul_assoc _ _ _).symm
  have hnormal (x : X) : x - Γ x = T.symm (H x) := by
    dsimp [Γ]
    rw [map_sub, T.symm_apply_apply]
    abel
  have hrange : (fun x ↦ x - Γ x) '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨H.symm (T x), Set.mem_univ _, ?_⟩
    dsimp only
    rw [hnormal, H.apply_symm_apply, T.symm_apply_apply]
  obtain ⟨_,_,J,_,hJleft,_,hJ,_,_⟩ :=
    Analysis.wellsLipschitzPerturbationSmoothInverse isOpen_univ hr hΓ.contDiffOn
      (mul_nonneg a.2 ε.2) hsmall hΓlip
  change ContDiffOn ℝ (r : ℕ∞ω) J ((fun x ↦ x - Γ x) '' Set.univ) at hJ
  rw [hrange, contDiffOn_univ] at hJ
  have heq : (H.symm : U → X) = fun u ↦ J (T.symm u) := by
    funext u
    have he := hJleft (H.symm u) (Set.mem_univ _)
    have he2 : (fun x ↦ x - Γ x) (H.symm u) = T.symm u := by
      dsimp only
      rw [hnormal, H.apply_symm_apply]
    rw [he2] at he
    exact he.symm
  rw [heq]
  exact hJ.comp T.symm.contDiff

end HolomorphicAnosov
