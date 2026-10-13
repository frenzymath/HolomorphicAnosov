import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import Mathlib.Logic.Function.Iterate

/-! This file proves forward orbit bounds for invariant stable parameter graphs (HPS, pp.59–62). -/

noncomputable section
namespace HolomorphicAnosov

/-- A centered unit-slope invariant stable graph has forward orbits bounded by `(k + ε)^n` in the product norm (HPS, pp.59–62). -/
theorem parameter_graph_stable_orbit
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A → A) (T₁ : ∀ p, E₁ p →L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : ∀ p, G p 0 = 0) (k ε : NNReal)
    (hk : ∀ p, ‖T₂ p‖ ≤ k)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (t : ∀ p, E₂ p → E₁ p)
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p))
    (hpre : ∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
      Set.range (fun y ↦ (t p y, y)))
    (p : A) (z : E₁ p × E₂ p) (hz : z ∈ Set.range (fun y ↦ (t p y, y))) :
    let g : Sigma (fun p ↦ E₁ p × E₂ p) → Sigma (fun p ↦ E₁ p × E₂ p) :=
      fun v ↦ ⟨h v.1, G v.1 v.2⟩
    (∀ n : ℕ,
      ((g^[n]) ⟨p, z⟩).2 ∈
        Set.range (fun y ↦ (t ((g^[n]) ⟨p, z⟩).1 y, y)) ∧
      ‖((g^[n]) ⟨p, z⟩).2‖ ≤ ((k : ℝ) + ε) ^ n * ‖z‖) ∧
    (∀ ρ d : ℝ, (k : ℝ) + ε ≤ ρ → ρ ≤ 1 → ‖z‖ < d →
      (∀ n : ℕ, ‖((g^[n]) ⟨p, z⟩).2‖ < d) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖((g^[n]) ⟨p, z⟩).2‖ ≤ C * ρ ^ n) := by
  dsimp only
  let g : Sigma (fun p ↦ E₁ p × E₂ p) → Sigma (fun p ↦ E₁ p × E₂ p) :=
    fun v ↦ ⟨h v.1, G v.1 v.2⟩
  have hnorm (q : A) (y : E₂ q) : ‖(t q y, y)‖ = ‖y‖ := by
    have hy : ‖t q y‖ ≤ ‖y‖ := by
      simpa only [(ht q).1, sub_zero, NNReal.coe_one, one_mul] using
        (ht q).2.norm_sub_le y 0
    exact max_eq_right hy
  have hstep (v : Sigma (fun p ↦ E₁ p × E₂ p))
      (hv : v.2 ∈ Set.range (fun y ↦ (t v.1 y, y))) :
      (g v).2 ∈ Set.range (fun y ↦ (t (g v).1 y, y)) ∧
      ‖(g v).2‖ ≤ ((k : ℝ) + ε) * ‖v.2‖ := by
    have himage : G v.1 v.2 ∈ Set.range (fun y ↦ (t (h v.1) y, y)) := by
      change v.2 ∈ G v.1 ⁻¹' Set.range (fun y ↦ (t (h v.1) y, y))
      rw [hpre]
      exact hv
    refine ⟨himage, ?_⟩
    obtain ⟨y, hy⟩ := hv
    obtain ⟨y', hy'⟩ := himage
    have hvnorm : ‖v.2‖ = ‖y‖ := by rw [← hy]; exact hnorm _ _
    have hgNorm : ‖G v.1 v.2‖ = ‖(G v.1 v.2).2‖ := by
      rw [← hy']
      exact hnorm _ _
    change ‖G v.1 v.2‖ ≤ _
    rw [hgNorm, hvnorm]
    have hb := parameter_graph_vertical_estimate (T₁ v.1) (T₂ v.1) (G v.1)
      k ε (hk v.1) (hR v.1) (t v.1 y) 0 y 0
    have htNorm : ‖t v.1 y‖ ≤ ‖y‖ := by
      simpa only [(ht v.1).1, sub_zero, NNReal.coe_one, one_mul] using
        (ht v.1).2.norm_sub_le y 0
    simpa only [hy, show (0, 0) = (0 : E₁ v.1 × E₂ v.1) from rfl,
      hG, Prod.snd_zero, sub_zero, max_eq_right htNorm, add_mul] using hb
  have hiter : ∀ n : ℕ,
      ((g^[n]) ⟨p, z⟩).2 ∈
        Set.range (fun y ↦ (t ((g^[n]) ⟨p, z⟩).1 y, y)) ∧
      ‖((g^[n]) ⟨p, z⟩).2‖ ≤ ((k : ℝ) + ε) ^ n * ‖z‖ := by
    intro n
    induction n with
    | zero =>
      refine ⟨hz, ?_⟩
      simp only [Function.iterate_zero_apply, pow_zero, one_mul]
      exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hmem, hbound⟩ := hstep ((g^[n]) ⟨p, z⟩) ih.1
      refine ⟨hmem, hbound.trans ?_⟩
      calc
        _ ≤ ((k : ℝ) + ε) * (((k : ℝ) + ε) ^ n * ‖z‖) :=
          mul_le_mul_of_nonneg_left ih.2 (add_nonneg k.2 ε.2)
        _ = _ := by rw [pow_succ']; exact (mul_assoc _ _ _).symm
  refine ⟨hiter, ?_⟩
  intro ρ d hrate hρ hzd
  have hnonneg : 0 ≤ (k : ℝ) + ε := add_nonneg k.2 ε.2
  constructor
  · intro n
    exact ((hiter n).2.trans ((mul_le_mul_of_nonneg_right
      (pow_le_one₀ hnonneg (hrate.trans hρ)) (norm_nonneg z)).trans_eq
      (one_mul _))).trans_lt hzd
  · refine ⟨‖z‖ + 1, by positivity, ?_⟩
    intro n
    calc
      _ ≤ ((k : ℝ) + ε) ^ n * ‖z‖ := (hiter n).2
      _ ≤ ρ ^ n * (‖z‖ + 1) := mul_le_mul
        (pow_le_pow_left₀ hnonneg hrate n) (by linarith)
        (norm_nonneg z) (pow_nonneg (hnonneg.trans hrate) n)
      _ = _ := mul_comm _ _

end HolomorphicAnosov
