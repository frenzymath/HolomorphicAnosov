import Mathlib.Analysis.SpecificLimits.Basic

namespace HolomorphicAnosov.FranksFibreInjectivity

/-- Franks (1969), §1.8, pp.122–123: equal-image points on one expanding leaf
coincide. The relation is the same-leaf relation and `d` its intrinsic distance.
Semiconjugacy propagates equality of images and invariance propagates the leaf
relation. The uniform fibre bound and inverse expansion estimate give
`d x y ≤ C * rate^k * bound` for every k. Its right side tends to zero, so
strict positivity of intrinsic distance for distinct leaf points proves equality.
This statement keeps the geometric bounds as explicit premises; it does not
infer them from properness or compactness of the ambient space. -/
theorem eq_of_expanding_leaf_of_equal_image {P Q : Type*}
    (F : P → P) (A : Q → Q) (H : P → Q) (hsem : Function.Semiconj H F A)
    (L : P → P → Prop) (d : P → P → ℝ)
    (hinv : ∀ x y, L x y → L (F x) (F y))
    (hpos : ∀ x y, L x y → x ≠ y → 0 < d x y)
    (C rate bound : ℝ) (hC : 0 ≤ C) (hrate : 0 ≤ rate) (hrate1 : rate < 1)
    (hexp : ∀ x y, L x y → ∀ k : ℕ,
      d x y ≤ C * rate ^ k * d (F^[k] x) (F^[k] y))
    (hbound : ∀ x y, L x y → H x = H y → d x y ≤ bound)
    {x y : P} (hL : L x y) (hH : H x = H y) : x = y := by
  have hLi : ∀ k : ℕ, L (F^[k] x) (F^[k] y) := by
    intro k
    induction k with
    | zero => simpa using hL
    | succ k hk => simpa only [Function.iterate_succ_apply'] using hinv _ _ hk
  have hHi : ∀ k : ℕ, H (F^[k] x) = H (F^[k] y) := by
    intro k
    rw [(hsem.iterate_right k) x, (hsem.iterate_right k) y, hH]
  have hle : ∀ k : ℕ, d x y ≤ C * rate ^ k * bound := by
    intro k
    exact (hexp x y hL k).trans
      (mul_le_mul_of_nonneg_left (hbound _ _ (hLi k) (hHi k))
        (mul_nonneg hC (pow_nonneg hrate k)))
  have hlim : Filter.Tendsto (fun k : ℕ ↦ C * rate ^ k * bound)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hrate hrate1).const_mul C).mul_const bound
  have hz : d x y ≤ 0 := ge_of_tendsto' hlim hle
  by_contra hne
  exact (not_le_of_gt (hpos x y hL hne)) hz



end HolomorphicAnosov.FranksFibreInjectivity
