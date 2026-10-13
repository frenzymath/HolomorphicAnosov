import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter
open scoped Topology _root_.Topology ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- The two bounded shifts used in Wells (1976), pp.289–291, Case 1 and Case 2
sequence operators. DAG node: `analysis.wells_c0_sequence_shifts_g18`.
Deleting the first coordinate preserves convergence to zero;
inserting a zero does too. Both operations are linear and their coordinate norms
are bounded by the original supremum norm. Thus both extend directly to continuous
linear maps of the genuine null-sequence space. No completeness is needed. -/
theorem wells_c0_sequence_shifts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ S T : C₀(ℕ, E) →L[ℝ] C₀(ℕ, E),
      (∀ w, S w 0 = 0) ∧ (∀ w n, S w (n + 1) = w n) ∧
      (∀ w n, T w n = w (n + 1)) ∧
      (∀ w, ‖S w‖ ≤ ‖w‖) ∧ (∀ w, ‖T w‖ ≤ ‖w‖) := by
  let prepend (w : C₀(ℕ, E)) : C₀(ℕ, E) :=
    { toFun := fun n ↦ match n with | 0 => 0 | k + 1 => w k
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        rw [cocompact_eq_atTop]
        apply (tendsto_add_atTop_iff_nat 1).mp
        simpa [cocompact_eq_atTop] using zero_at_infty w }
  let tail (w : C₀(ℕ, E)) : C₀(ℕ, E) :=
    { toFun := fun n ↦ w (n + 1)
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        rw [cocompact_eq_atTop]
        apply (tendsto_add_atTop_iff_nat 1).mpr
        simpa [cocompact_eq_atTop] using zero_at_infty w }
  let S₀ : C₀(ℕ, E) →ₗ[ℝ] C₀(ℕ, E) :=
    { toFun := prepend
      map_add' := by intro w z; ext n; cases n <;> simp [prepend]
      map_smul' := by intro c w; ext n; cases n <;> simp [prepend] }
  let T₀ : C₀(ℕ, E) →ₗ[ℝ] C₀(ℕ, E) :=
    { toFun := tail
      map_add' := by intro w z; ext n; rfl
      map_smul' := by intro c w; ext n; rfl }
  have hS (w : C₀(ℕ, E)) : ‖S₀ w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg w)).mpr
    intro n
    cases n with
    | zero => simp [S₀, prepend]
    | succ n => exact BoundedContinuousFunction.norm_coe_le_norm w.toBCF n
  have hT (w : C₀(ℕ, E)) : ‖T₀ w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg w)).mpr
    intro n
    exact BoundedContinuousFunction.norm_coe_le_norm w.toBCF (n + 1)
  refine ⟨S₀.mkContinuous 1 hS, T₀.mkContinuous 1 hT,
    (fun _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), ?_, ?_⟩
  · intro w
    change ‖S₀ w‖ ≤ ‖w‖
    simpa only [one_mul] using hS w
  · intro w
    change ‖T₀ w‖ ≤ ‖w‖
    simpa only [one_mul] using hT w

end HolomorphicAnosov.Analysis

