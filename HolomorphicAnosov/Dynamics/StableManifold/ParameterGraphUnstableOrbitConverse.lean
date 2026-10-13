import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableTransverse
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- Every coherent backward orbit satisfying the stated normalized bound lies on a centered invariant unstable graph (HPS, pp.59–60, 62). -/
theorem parameter_graph_unstable_orbit_converse
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A → A) (T₁ : ∀ p, E₁ p →L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (ρ : ℝ) (hρ : 0 < ρ) (k ε : NNReal)
    (hrate : (k : ℝ) + 2 * ε < ρ)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (s : ∀ p, E₁ p → E₂ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p))
    (hgraph : ∀ p x, (G p (x,s p x)).2 = s (h p) (G p (x,s p x)).1)
    (p : A) (z : E₁ p × E₂ p)
    (horbit : ∃ v : ℕ → Sigma (fun p ↦ E₁ p × E₂ p),
      v 0 = ⟨p,z⟩ ∧
      (∀ n, (⟨h (v (n+1)).1, G (v (n+1)).1 (v (n+1)).2⟩ :
        Sigma (fun p ↦ E₁ p × E₂ p)) = v n) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n, ‖(v n).2‖ ≤ C * (ρ⁻¹) ^ n) :
    z ∈ Set.range (fun x ↦ (x,s p x)) := by
  let g : Sigma (fun p ↦ E₁ p × E₂ p) → Sigma (fun p ↦ E₁ p × E₂ p) :=
    fun v ↦ ⟨h v.1, G v.1 v.2⟩
  let D : Sigma (fun p ↦ E₁ p × E₂ p) → ℝ := fun v ↦ ‖v.2.2 - s v.1 v.2.1‖
  let B : ℝ := (k : ℝ) + 2 * ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hstep (v : Sigma (fun p ↦ E₁ p × E₂ p)) : D (g v) ≤ B * D v :=
    parameter_graph_unstable_transverse (T₁ v.1) (T₂ v.1) (G v.1) k ε
      (hT₂ v.1) (hR v.1) (s v.1) (s (h v.1)) (hs _).2 (hgraph v.1) v.2.1 v.2.2
  have hbound (v : Sigma (fun p ↦ E₁ p × E₂ p)) : D v ≤ 2 * ‖v.2‖ := by
    have hsbound : ‖s v.1 v.2.1‖ ≤ ‖v.2.1‖ := by
      simpa only [(hs v.1).1, sub_zero, NNReal.coe_one, one_mul] using
        (hs v.1).2.norm_sub_le v.2.1 0
    exact (norm_sub_le _ _).trans (by
      have hfst := norm_fst_le v.2
      have hsnd := norm_snd_le v.2
      linarith)
  obtain ⟨v,hv0,hv,C,hC,hCv⟩ := horbit
  have hback (n : ℕ) : D (v n) ≤ B * D (v (n+1)) := by
    have hb := hstep (v (n+1))
    change D (⟨h (v (n+1)).1, G (v (n+1)).1 (v (n+1)).2⟩ :
      Sigma (fun p ↦ E₁ p × E₂ p)) ≤ _ at hb
    rwa [hv] at hb
  have hiter : ∀ n : ℕ, D (v 0) ≤ B ^ n * D (v n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ B ^ n * D (v n) := ih
        _ ≤ B ^ n * (B * D (v (n+1))) :=
          mul_le_mul_of_nonneg_left (hback n) (pow_nonneg hB n)
        _ = _ := by rw [pow_succ]; ring
  have hdecay (n : ℕ) : D (v 0) ≤ 2 * C * (B / ρ) ^ n := calc
    _ ≤ B ^ n * D (v n) := hiter n
    _ ≤ B ^ n * (2 * (C * (ρ⁻¹) ^ n)) :=
      mul_le_mul_of_nonneg_left ((hbound _).trans
        (mul_le_mul_of_nonneg_left (hCv n) (by norm_num))) (pow_nonneg hB n)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring
  have hlim : Tendsto (fun n : ℕ ↦ 2 * C * (B / ρ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hB hρ.le) ((div_lt_one hρ).mpr hrate)).const_mul (2 * C)
  have hzero : D (v 0) = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hdecay)) (norm_nonneg _)
  rw [hv0] at hzero
  have hz : z.2 = s p z.1 := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨z.1, Prod.ext rfl hz.symm⟩

end HolomorphicAnosov
