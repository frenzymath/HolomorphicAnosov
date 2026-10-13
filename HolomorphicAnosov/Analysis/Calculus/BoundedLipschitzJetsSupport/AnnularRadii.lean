import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- The decreasing radii in HPS (3.3), p.28 can meet any prescribed positive bounds.
Choose each radius at most half the preceding radius and at most its prescribed bound.
Induction bounds the sequence by its initial radius times 2^(-n), proving convergence. -/
theorem annular_radii (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ StrictAnti r ∧
      (∀ n, r n ≤ δ n) ∧ Tendsto r atTop (𝓝 0) := by
  let r : ℕ → ℝ := Nat.rec (min (δ 0) 1) (fun n a ↦ min (δ (n+1)) (a / 2))
  have hr0 : r 0 = min (δ 0) 1 := rfl
  have hrs (n : ℕ) : r (n+1) = min (δ (n+1)) (r n / 2) := rfl
  have hp (n : ℕ) : 0 < r n := by
    induction n with
    | zero => simpa [hr0] using lt_min (hδ 0) zero_lt_one
    | succ n ih => rw [hrs]; exact lt_min (hδ _) (half_pos ih)
  have hhalf (n : ℕ) : r (n+1) ≤ r n / 2 := by rw [hrs]; exact min_le_right _ _
  have ha : StrictAnti r := strictAnti_nat_of_succ_lt fun n ↦ (hhalf n).trans_lt (by linarith [hp n])
  have hd (n : ℕ) : r n ≤ δ n := by cases n <;> simp only [hr0, hrs]; exact min_le_left _ _; exact min_le_left _ _
  have hg (n : ℕ) : r n ≤ r 0 * (1/2 : ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        r (n+1) ≤ r n / 2 := hhalf n
        _ ≤ (r 0 * (1/2:ℝ)^n) / 2 := by linarith
        _ = r 0 * (1/2:ℝ)^(n+1) := by ring
  refine ⟨r, hp, ha, hd, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ r 0 * (1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (r 0)
  exact squeeze_zero (fun n ↦ (hp n).le) hg ht

end HolomorphicAnosov.BoundedLipschitzJets

