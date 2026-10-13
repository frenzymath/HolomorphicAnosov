import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrier

/-!
# Realization of centered unit-Lipschitz parameter graphs

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), Sublemma 5.2,
pp.54–55, and the parameter-dependent section metric on p.62. The normalized
dependent `lp` coordinates are the formal realization of that weighted metric.
No topology on the parameter type, completeness of the fibres, or nontriviality
of any input fibre is needed for this realization.
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS Sublemma 5.2, pp.54–55, with parameter insertion p.62: every centered
unit-Lipschitz family has normalized bounded coordinates. The slope bound at zero
gives `‖s p x‖ ≤ ‖x‖`, so division by the positive norm of a nonzero input bounds
every coordinate by one. Multiplication by that norm recovers the original map;
the zero input is recovered from centeredness. Thus the original slope constraints
hold for the recovered map without any change of fibre norm. -/
theorem parameter_graph_carrier_realization
    {A : Type*} (E F : A → Type*)
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    (s : ∀ p, E p → F p) (hs0 : ∀ p, s p 0 = 0)
    (hs : ∀ p, LipschitzWith 1 (s p)) :
    ∃ q : ParameterGraphCarrier E F, q ∈ parameterGraphUnitSet E F ∧
      ∀ p x, parameterGraphValue E F q p x = s p x := by
  classical
  let v : (i : Sigma (fun p ↦ {x : E p // x ≠ 0})) → F i.1 :=
    fun i ↦ ‖i.2.1‖⁻¹ • s i.1 i.2.1
  have hv : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have hnorm : ‖s i.1 i.2.1‖ ≤ ‖i.2.1‖ := by
      simpa [hs0] using (hs i.1).norm_sub_le i.2.1 0
    dsimp [v]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖i.2.1‖⁻¹ * ‖s i.1 i.2.1‖ ≤ ‖i.2.1‖⁻¹ * ‖i.2.1‖ :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr i.2.2)
  let q : ParameterGraphCarrier E F := ⟨v, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact hv i⟩⟩
  have hvalue : ∀ p x, parameterGraphValue E F q p x = s p x := by
    intro p x
    by_cases hx : x = 0
    · simp [parameterGraphValue, hx, hs0]
    · simp only [parameterGraphValue, dite_eq_right hx]
      change ‖x‖ • (‖x‖⁻¹ • s p x) = s p x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  refine ⟨q, ?_, hvalue⟩
  intro p
  simpa only [funext (hvalue p)] using hs p

end HolomorphicAnosov
