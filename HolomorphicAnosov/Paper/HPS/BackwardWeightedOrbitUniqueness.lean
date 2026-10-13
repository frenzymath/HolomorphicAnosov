import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HolomorphicAnosov

/-- Two retained backward orbits with the same initial horizontal coordinate and bounded weighted difference coincide. (Wells, pp. 289–290) -/
theorem hps_backward_weighted_orbit_uniqueness
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (g : E₁ × E₂ → E₁ × E₂) (B : Set (E₁ × E₂)) (ε q : ℝ)
    (hε : 0 ≤ ε) (hq : 0 < q)
    (hsmall : max (‖T₁.symm.toContinuousLinearMap‖ * (q + ε))
      (q⁻¹ * (‖T₂‖ + ε)) < 1)
    (hR : ∀ x ∈ B, ∀ y ∈ B,
      ‖(g x - (T₁ x.1, T₂ x.2)) - (g y - (T₁ y.1, T₂ y.2))‖ ≤ ε * ‖x-y‖)
    (w z : ℕ → E₁ × E₂) (hw : ∀ n, w n ∈ B) (hz : ∀ n, z n ∈ B)
    (hwr : ∀ n, g (w (n+1)) = w n) (hzr : ∀ n, g (z (n+1)) = z n)
    (hbase : (w 0).1 = (z 0).1)
    (hbounded : ∃ M : ℝ, ∀ n, q^n * ‖w n-z n‖ ≤ M) : w = z := by
  let a := ‖T₁.symm.toContinuousLinearMap‖
  let Q := max (a * (q+ε)) (q⁻¹ * (‖T₂‖+ε))
  let d : ℕ → ℝ := fun n ↦ q^n * ‖w n-z n‖
  have hb : BddAbove (Set.range d) := by
    obtain ⟨M, hM⟩ := hbounded
    exact ⟨M, by rintro _ ⟨n,rfl⟩; exact hM n⟩
  let D := ⨆ n, d n
  have hd (n : ℕ) : d n ≤ D := le_ciSup hb n
  have hD : 0 ≤ D := (mul_nonneg (pow_nonneg hq.le 0) (norm_nonneg _)).trans (hd 0)
  have hQ : 0 ≤ Q := (mul_nonneg (norm_nonneg _) (add_nonneg hq.le hε)).trans
    (le_max_left _ _)
  have hh (n : ℕ) : ‖(w (n+1)).1-(z (n+1)).1‖ ≤
      a * (‖(w n).1-(z n).1‖ + ε * ‖w (n+1)-z (n+1)‖) := by
    let e := (g (w (n+1)) - (T₁ (w (n+1)).1,T₂ (w (n+1)).2)) -
      (g (z (n+1)) - (T₁ (z (n+1)).1,T₂ (z (n+1)).2))
    have he : ‖e.1‖ ≤ ε * ‖w (n+1)-z (n+1)‖ :=
      (norm_fst_le e).trans (hR _ (hw _) _ (hz _))
    have heq : (w (n+1)).1-(z (n+1)).1 =
        T₁.symm ((w n).1-(z n).1-e.1) := by
      apply T₁.injective
      simp only [map_sub, T₁.apply_symm_apply]
      dsimp [e]
      rw [hwr, hzr]
      abel
    rw [heq]
    exact (T₁.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
        (add_le_add le_rfl he)) (norm_nonneg _))
  have hv (n : ℕ) : ‖(w n).2-(z n).2‖ ≤
      (‖T₂‖+ε) * ‖w (n+1)-z (n+1)‖ := by
    let e := (g (w (n+1)) - (T₁ (w (n+1)).1,T₂ (w (n+1)).2)) -
      (g (z (n+1)) - (T₁ (z (n+1)).1,T₂ (z (n+1)).2))
    have he : ‖e.2‖ ≤ ε * ‖w (n+1)-z (n+1)‖ :=
      (norm_snd_le e).trans (hR _ (hw _) _ (hz _))
    have heq : (w n).2-(z n).2 =
        T₂ ((w (n+1)).2-(z (n+1)).2)+e.2 := by
      dsimp [e]
      rw [map_sub, hwr, hzr]
      abel
    rw [heq]
    calc
      _ ≤ ‖T₂ ((w (n+1)).2-(z (n+1)).2)‖+‖e.2‖ := norm_add_le _ _
      _ ≤ ‖T₂‖ * ‖w (n+1)-z (n+1)‖ + ε * ‖w (n+1)-z (n+1)‖ :=
        add_le_add ((T₂.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le (w (n+1)-z (n+1))) (norm_nonneg _))) he
      _ = _ := by ring
  have hx (n : ℕ) : q^n * ‖(w n).1-(z n).1‖ ≤ Q*D := by
    cases n with
    | zero => simp only [hbase, sub_self, norm_zero, mul_zero]; exact mul_nonneg hQ hD
    | succ n =>
      calc
        _ ≤ q^(n+1) * (a * (‖(w n).1-(z n).1‖ + ε * ‖w (n+1)-z (n+1)‖)) :=
          mul_le_mul_of_nonneg_left (hh n) (pow_nonneg hq.le _)
        _ = a*q * (q^n * ‖(w n).1-(z n).1‖) + a*ε*d (n+1) := by
          dsimp [d]; rw [pow_succ]; ring
        _ ≤ a*q*D + a*ε*D := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              ((mul_le_mul_of_nonneg_left (norm_fst_le _) (pow_nonneg hq.le _)).trans
                (hd n)) (mul_nonneg (norm_nonneg _) hq.le)
          · exact mul_le_mul_of_nonneg_left (hd _) (mul_nonneg (norm_nonneg _) hε)
        _ = (a*(q+ε))*D := by ring
        _ ≤ Q*D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD
  have hy (n : ℕ) : q^n * ‖(w n).2-(z n).2‖ ≤ Q*D := by
    calc
      _ ≤ q^n * ((‖T₂‖+ε) * ‖w (n+1)-z (n+1)‖) :=
        mul_le_mul_of_nonneg_left (hv n) (pow_nonneg hq.le _)
      _ = (q⁻¹*(‖T₂‖+ε))*d (n+1) := by
        dsimp [d]; rw [pow_succ]; field_simp
      _ ≤ (q⁻¹*(‖T₂‖+ε))*D :=
        mul_le_mul_of_nonneg_left (hd _) (mul_nonneg (inv_nonneg.mpr hq.le)
          (add_nonneg (norm_nonneg _) hε))
      _ ≤ Q*D := mul_le_mul_of_nonneg_right (le_max_right _ _) hD
  have hcontract : D ≤ Q*D := by
    apply ciSup_le
    intro n
    change q^n * ‖w n-z n‖ ≤ Q*D
    rw [Prod.norm_def, mul_max_of_nonneg _ _ (pow_nonneg hq.le n)]
    exact max_le (hx n) (hy n)
  have hD0 : D = 0 := by
    have hQ1 : Q < 1 := hsmall
    nlinarith
  funext n
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh' := hd n
  dsimp [d] at hh'
  rw [hD0] at hh'
  have hp := pow_pos hq n
  nlinarith [norm_nonneg (w n-z n)]

end HolomorphicAnosov

