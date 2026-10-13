import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

open Matrix
open scoped BigOperators

namespace HolomorphicAnosov

/-- Gantmacher, Applications of the Theory of Matrices (1959), Chapter III,
pp.66–73: the positive-eigenvector simplicity argument used in the parent
FranksManning Step 11(C4). For a strictly positive real matrix, every real
eigenvector with the same eigenvalue as a strictly positive eigenvector is
a scalar multiple of it.

Choose the greatest coordinate ratio v_i/z_i and subtract v from this multiple
of z. The residual is nonnegative and has a zero coordinate. Its image has that
same zero coordinate by the common eigenvalue equation. Strict positivity of
the matrix then forces every residual coordinate to vanish. Empty dimension
is handled directly. This proves geometric uniqueness, not algebraic simplicity
or existence of a positive eigenvector. -/
theorem franks_manning_positive_eigenvector_unique
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
    (z v : Fin n → ℝ) (hz : ∀ i, 0 < z i) (ρ : ℝ)
    (hAz : A *ᵥ z = ρ • z) (hAv : A *ᵥ v = ρ • v) :
    ∃ c : ℝ, v = c • z := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨0, Subsingleton.elim _ _⟩
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin n ↦ v j / z j) Finset.univ_nonempty
  let c := v i / z i
  let w := c • z - v
  have hw (j : Fin n) : 0 ≤ w j := by
    have h := (div_le_iff₀ (hz j)).mp (hmax j (Finset.mem_univ j))
    change 0 ≤ c * z j - v j
    exact sub_nonneg.mpr h
  have hwi : w i = 0 := by
    change v i / z i * z i - v i = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hz i)), sub_self]
  have hAw : A *ᵥ w = ρ • w := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAz, hAv]
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : ∑ j, A i j * w j = 0 := by
    have h := congrFun hAw i
    simpa [Matrix.mulVec, dotProduct, hwi] using h
  have hwzero (j : Fin n) : w j = 0 := by
    have hterm : A i j * w j ≤ 0 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun k _ ↦ mul_nonneg (hA i k).le (hw k))
        (Finset.mem_univ j)
    exact le_antisymm (nonpos_of_mul_nonpos_right hterm (hA i j)) (hw j)
  refine ⟨c, ?_⟩
  ext j
  exact (sub_eq_zero.mp (hwzero j)).symm

/-- The same real eigendirection uniqueness when a power of the matrix is
strictly positive, as used for primitive matrices in Gantmacher, Chapter III,
Theorem 8, pp.97–98. Iterating the two eigenvector equations gives the same
eigenvalue power for both vectors; apply the preceding positive-matrix result
to this actual power. No new positive eigenvector is chosen. -/
theorem franks_manning_positive_power_eigenvector_unique
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (hA : ∀ i j, 0 < (A ^ k) i j)
    (z v : Fin n → ℝ) (hz : ∀ i, 0 < z i) (ρ : ℝ)
    (hAz : A *ᵥ z = ρ • z) (hAv : A *ᵥ v = ρ • v) :
    ∃ c : ℝ, v = c • z := by
  have hp (x : Fin n → ℝ) (hx : A *ᵥ x = ρ • x) (m : ℕ) :
      A ^ m *ᵥ x = ρ ^ m • x := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, ih, pow_succ]
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  exact franks_manning_positive_eigenvector_unique (A ^ k) hA z v hz (ρ ^ k)
    (hp z hAz k) (hp v hAv k)

end HolomorphicAnosov

