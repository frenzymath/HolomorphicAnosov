import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstablePreimageBound
import Mathlib.Logic.Function.Iterate

noncomputable section
namespace HolomorphicAnosov

/-- Every point on an image-invariant centered unit-slope graph has a coherent backward history bounded by `b^n‖z‖`, where `b=a/(1-aε)` (HPS, pp.54–55, 59–61). -/
theorem parameter_graph_unstable_orbit
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A ≃ A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : ∀ p, G p 0 = 0) (a ε : NNReal)
    (hT : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : (a : ℝ) * ε < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (s : ∀ p, E₁ p → E₂ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p))
    (himage : ∀ p, G p '' Set.range (fun x ↦ (x,s p x)) =
      Set.range (fun x ↦ (x,s (h p) x)))
    (p : A) (z : E₁ p × E₂ p) (hz : z ∈ Set.range (fun x ↦ (x,s p x))) :
    ∃ v : ℕ → Sigma (fun p ↦ E₁ p × E₂ p),
      v 0 = ⟨p,z⟩ ∧
      (∀ n, (⟨h (v (n+1)).1, G (v (n+1)).1 (v (n+1)).2⟩ :
        Sigma (fun p ↦ E₁ p × E₂ p)) = v n) ∧
      (∀ n, (v n).2 ∈ Set.range (fun x ↦ (x,s (v n).1 x))) ∧
      (∀ n, ‖(v n).2‖ ≤ ((a : ℝ) / (1 - (a : ℝ) * ε)) ^ n * ‖z‖) ∧
      (∀ ρ d : ℝ, 0 < ρ → 1 ≤ ρ →
        (a : ℝ) / (1 - (a : ℝ) * ε) ≤ ρ⁻¹ → ‖z‖ < d →
        (∀ n, ‖(v n).2‖ < d) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n, ‖(v n).2‖ ≤ C * (ρ⁻¹) ^ n) := by
  classical
  let P : Sigma (fun p ↦ E₁ p × E₂ p) → Prop :=
    fun v ↦ v.2 ∈ Set.range (fun x ↦ (x,s v.1 x))
  let F : {v // P v} → {v // P v} := fun v ↦
    ⟨⟨h v.1.1, G v.1.1 v.1.2⟩, by
      change G v.1.1 v.1.2 ∈ Set.range (fun x ↦ (x,s (h v.1.1) x))
      rw [← himage]
      exact ⟨v.1.2,v.2,rfl⟩⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨⟨q,w⟩,hw⟩
    obtain ⟨q,rfl⟩ := h.surjective q
    have hw' : w ∈ G q '' Set.range (fun x ↦ (x,s q x)) := by
      rw [himage]
      exact hw
    obtain ⟨u,hu,hu'⟩ := hw'
    refine ⟨⟨⟨q,u⟩,hu⟩, ?_⟩
    apply Subtype.ext
    change (⟨h q,G q u⟩ : Sigma (fun p ↦ E₁ p × E₂ p)) = ⟨h q,w⟩
    rw [hu']
  let B : {v // P v} → {v // P v} := fun v ↦ Classical.choose (hsurj v)
  have hB (v : {v // P v}) : F (B v) = v := Classical.choose_spec (hsurj v)
  let v0 : {v // P v} := ⟨⟨p,z⟩,hz⟩
  let v : ℕ → Sigma (fun p ↦ E₁ p × E₂ p) := fun n ↦ ((B^[n]) v0).1
  let b : ℝ := (a : ℝ) / (1 - (a : ℝ) * ε)
  have hb : 0 ≤ b := div_nonneg a.2 (sub_pos.mpr hsmall).le
  have hstep (w : {v // P v}) : ‖(B w).1.2‖ ≤ b * ‖w.1.2‖ := by
    have hp := (B w).2
    obtain ⟨x,hx⟩ := hp
    have hnorm := parameter_graph_unstable_preimage_bound (T₁ (B w).1.1)
      (T₂ (B w).1.1) (G (B w).1.1) (hG _) a ε (hT _) hsmall (hR _)
      (s (B w).1.1) (hs _).1 (hs _).2 x
    dsimp only at hx
    rw [hx] at hnorm
    have he : ‖G (B w).1.1 (B w).1.2‖ = ‖w.1.2‖ :=
      congrArg (fun u : {v // P v} ↦ ‖u.1.2‖) (hB w)
    exact hnorm.trans_eq (by rw [he])
  have hiter : ∀ n, ‖(v n).2‖ ≤ b ^ n * ‖z‖ := by
    intro n
    induction n with
    | zero =>
      simp only [v,v0,Function.iterate_zero_apply,pow_zero,one_mul]
      rfl
    | succ n ih =>
      change ‖((B^[n+1]) v0).1.2‖ ≤ _
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ b * ‖((B^[n]) v0).1.2‖ := hstep _
        _ ≤ b * (b ^ n * ‖z‖) := mul_le_mul_of_nonneg_left ih hb
        _ = _ := by rw [pow_succ']; ring
  refine ⟨v,rfl,?_,fun n ↦ ((B^[n]) v0).2,hiter,?_⟩
  · intro n
    have he := congrArg Subtype.val (hB ((B^[n]) v0))
    change (⟨h ((B^[n+1]) v0).1.1, G ((B^[n+1]) v0).1.1 ((B^[n+1]) v0).1.2⟩ :
      Sigma (fun p ↦ E₁ p × E₂ p)) = ((B^[n]) v0).1
    rw [Function.iterate_succ_apply']
    exact he
  · intro ρ d hρ hρ₁ hrate hzd
    have hr₁ : ρ⁻¹ ≤ 1 := (inv_le_one₀ hρ).mpr hρ₁
    constructor
    · intro n
      exact ((hiter n).trans ((mul_le_mul_of_nonneg_right
        (pow_le_one₀ hb (hrate.trans hr₁)) (norm_nonneg z)).trans_eq
        (one_mul _))).trans_lt hzd
    · refine ⟨‖z‖ + 1, by positivity, ?_⟩
      intro n
      calc
        _ ≤ b ^ n * ‖z‖ := hiter n
        _ ≤ (ρ⁻¹) ^ n * (‖z‖ + 1) := mul_le_mul
          (pow_le_pow_left₀ hb hrate n) (by linarith)
          (norm_nonneg z) (pow_nonneg (inv_nonneg.mpr hρ.le) n)
        _ = _ := mul_comm _ _

end HolomorphicAnosov
