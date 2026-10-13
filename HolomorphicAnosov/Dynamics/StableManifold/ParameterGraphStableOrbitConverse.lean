import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableTransverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Function.Iterate

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- Every orbit satisfying the stated normalized bound lies on a centered invariant stable graph (HPS, pp.59–60, 62). -/
theorem parameter_graph_stable_orbit_converse
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A → A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (m ρ : ℝ) (hm : 0 ≤ m) (hρ : 0 < ρ) (ε : NNReal)
    (hrate : ρ < m - 3 * (ε : ℝ))
    (hT : ∀ p, m * ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (t : ∀ p, E₂ p → E₁ p)
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p))
    (hgraph : ∀ p y, (G p (t p y,y)).1 = t (h p) (G p (t p y,y)).2)
    (p : A) (z : E₁ p × E₂ p)
    (horbit : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(((fun v : Sigma (fun p ↦ E₁ p × E₂ p) ↦
        (⟨h v.1, G v.1 v.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p)))^[n]) ⟨p,z⟩).2‖
        ≤ C * ρ ^ n) :
    z ∈ Set.range (fun y ↦ (t p y,y)) := by
  let g : Sigma (fun p ↦ E₁ p × E₂ p) → Sigma (fun p ↦ E₁ p × E₂ p) :=
    fun v ↦ ⟨h v.1, G v.1 v.2⟩
  let D : Sigma (fun p ↦ E₁ p × E₂ p) → ℝ := fun v ↦ ‖v.2.1 - t v.1 v.2.2‖
  let M : ℝ := m - 3 * (ε : ℝ)
  have hM : 0 < M := hρ.trans hrate
  have hstep (v : Sigma (fun p ↦ E₁ p × E₂ p)) : M * D v ≤ D (g v) :=
    parameter_graph_stable_transverse (T₁ v.1) (T₂ v.1) (G v.1) m hm ε
      (hT v.1) (hR v.1) (t v.1) (t (h v.1)) (ht _).2 (hgraph v.1) v.2.1 v.2.2
  have hbound (v : Sigma (fun p ↦ E₁ p × E₂ p)) : D v ≤ 2 * ‖v.2‖ := by
    have htbound : ‖t v.1 v.2.2‖ ≤ ‖v.2.2‖ := by
      simpa only [(ht v.1).1, sub_zero, NNReal.coe_one, one_mul] using
        (ht v.1).2.norm_sub_le v.2.2 0
    exact (norm_sub_le _ _).trans (by
      have hfst := norm_fst_le v.2
      have hsnd := norm_snd_le v.2
      linarith)
  have hiter : ∀ n : ℕ, M ^ n * D ⟨p,z⟩ ≤ D ((g^[n]) ⟨p,z⟩) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      calc
        _ ≤ M * D ((g^[n]) ⟨p,z⟩) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih hM.le
        _ ≤ _ := hstep _
  obtain ⟨C, hC, horbit⟩ := horbit
  have hdecay (n : ℕ) : D ⟨p,z⟩ ≤ 2 * C * (ρ / M) ^ n := by
    have hb : M ^ n * D ⟨p,z⟩ ≤ 2 * (C * ρ ^ n) :=
      (hiter n).trans ((hbound _).trans (mul_le_mul_of_nonneg_left (horbit n) (by norm_num)))
    apply (le_of_mul_le_mul_left ?_ (pow_pos hM n) : D ⟨p,z⟩ ≤ _)
    calc
      _ ≤ 2 * (C * ρ ^ n) := hb
      _ = M ^ n * (2 * C * (ρ / M) ^ n) := by
        rw [div_pow]
        field_simp
  have hlim : Tendsto (fun n : ℕ ↦ 2 * C * (ρ / M) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hρ.le hM.le) ((div_lt_one hM).mpr hrate)).const_mul (2 * C)
  have hzero : D ⟨p,z⟩ = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hdecay)) (norm_nonneg _)
  have hz : z.1 = t p z.2 := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨z.2, Prod.ext hz.symm rfl⟩

end HolomorphicAnosov
