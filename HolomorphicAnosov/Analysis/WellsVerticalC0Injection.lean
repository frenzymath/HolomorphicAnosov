import Mathlib.Topology.ContinuousMap.ZeroAtInfty

open Filter
open scoped Topology _root_.Topology ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- The vertical zeroth-coordinate injection used by Wells's Case 2, p.291.
It has only `(0,p)` at index zero, and the complementary product maximum estimate
is proved directly on the genuine null-sequence carrier. -/
theorem wells_vertical_c0_injection
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] :
    ∃ I : E₂ →L[ℝ] C₀(ℕ, E₁ × E₂),
      (∀ p, I p 0 = (0, p)) ∧ (∀ p n, I p (n + 1) = 0) ∧
      (∀ p, ‖I p‖ = ‖p‖) ∧
      (∀ p w, (w 0).2 = 0 → ‖I p + w‖ = max ‖p‖ ‖w‖) := by
  let value (p : E₂) : C₀(ℕ, E₁ × E₂) :=
    { toFun := fun n ↦ match n with | 0 => (0, p) | _ + 1 => 0
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        rw [cocompact_eq_atTop]
        apply (tendsto_add_atTop_iff_nat 1).mp
        exact tendsto_const_nhds }
  let L : E₂ →ₗ[ℝ] C₀(ℕ, E₁ × E₂) :=
    { toFun := value
      map_add' := by intro p q; ext n <;> cases n <;> simp [value]
      map_smul' := by intro c p; ext n <;> cases n <;> simp [value] }
  have hnorm (p : E₂) : ‖L p‖ = ‖p‖ := by
    apply le_antisymm
    · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg p)).mpr
      intro n
      cases n <;> simp [L, value, Prod.norm_def]
    · have h := BoundedContinuousFunction.norm_coe_le_norm (L p).toBCF 0
      simpa [L, value, Prod.norm_def] using h
  let I := L.mkContinuous 1 (fun p ↦ by simp [hnorm])
  have hI0 (p : E₂) : I p 0 = (0, p) := rfl
  have hIs (p : E₂) (n : ℕ) : I p (n + 1) = 0 := rfl
  refine ⟨I, hI0, hIs, hnorm, ?_⟩
  intro p w hw
  have hz : (I p + w) 0 = ((w 0).1, p) := by
    ext <;> simp [hI0, hw]
  have hn (n : ℕ) : (I p + w) (n + 1) = w (n + 1) := by
    simp [hIs]
  have hc (z : C₀(ℕ, E₁ × E₂)) (n : ℕ) : ‖z n‖ ≤ ‖z‖ :=
    BoundedContinuousFunction.norm_coe_le_norm z.toBCF n
  apply le_antisymm
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg p))).mpr
    intro n
    change ‖(I p + w) n‖ ≤ _
    cases n with
    | zero =>
      rw [hz, Prod.norm_def]
      calc
        max ‖(w 0).1‖ ‖p‖ ≤ max ‖w‖ ‖p‖ :=
          max_le_max ((norm_fst_le (w 0)).trans (hc w 0)) le_rfl
        _ = max ‖p‖ ‖w‖ := max_comm _ _
    | succ n =>
      rw [hn]
      exact (hc w (n + 1)).trans (le_max_right _ _)
  · apply max_le
    · have h := (norm_snd_le ((I p + w) 0)).trans (hc (I p + w) 0)
      simpa [hz] using h
    · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg (I p + w))).mpr
      intro n
      change ‖w n‖ ≤ _
      cases n with
      | zero =>
        calc
          ‖w 0‖ = max ‖(w 0).1‖ 0 := by rw [Prod.norm_def]; simp [hw]
          _ ≤ max ‖(w 0).1‖ ‖p‖ := max_le_max le_rfl (norm_nonneg _)
          _ = ‖(I p + w) 0‖ := by rw [hz, Prod.norm_def]
          _ ≤ ‖I p + w‖ :=
            BoundedContinuousFunction.norm_coe_le_norm (I p + w).toBCF 0
      | succ n => simpa [hn] using hc (I p + w) (n + 1)

end HolomorphicAnosov.Analysis

