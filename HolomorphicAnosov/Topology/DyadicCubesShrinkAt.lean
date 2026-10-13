import HolomorphicAnosov.Topology.ClosedFamilyShrinksAt
import HolomorphicAnosov.Topology.ClosedComplementDyadicCubeCover
import Mathlib.Data.Fintype.Pi

namespace HolomorphicAnosov
open Set Topology _root_.Topology
/-- Every closed dyadic cube avoiding `c` and meeting a sufficiently small ball
about `c` lies in a prescribed larger ball.

Source: Hatcher, proof of Theorem A.7, pp.525–526. The following finite-grid
argument is an agent expansion of its omitted quantitative shrinking step.
At any fixed lower bound on
side length, there are only finitely many nonnegative dyadic levels. At those
levels, a cube meeting the unit ball at `c` has all its integer coordinates
bounded, so there are only finitely many such cubes. They are closed and avoid
`c`. A small ball avoids their finite union; every remaining cube has Euclidean
diameter below half the prescribed radius. The triangle inequality gives the
conclusion. This argument applies to all dyadic cubes avoiding `c`, without
requiring a maximal selection or positive ambient dimension. -/
theorem dyadic_cubes_shrink_at {N : ℕ} (c : EuclideanSpace ℝ (Fin N)) :
    let Q := fun (k : ℕ) (m : Fin N → ℤ) ↦
      {y : EuclideanSpace ℝ (Fin N) | ∀ j,
        (m j : ℝ) / (2 : ℝ)^k ≤ y j ∧ y j ≤ ((m j : ℝ) + 1) / (2 : ℝ)^k}
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (k : ℕ) (m : Fin N → ℤ), c ∉ Q k m →
        (∃ x ∈ Q k m, dist x c < δ) → ∀ y ∈ Q k m, dist y c < ε := by
  classical
  intro Q
  have hlevels (K : ℕ) :
      {q : ℕ × (Fin N → ℤ) | q.1 ≤ K ∧ ∃ x ∈ Q q.1 q.2, dist x c < 1}.Finite := by
    obtain ⟨B, hB⟩ := exists_int_gt ((2 : ℝ)^K * (‖c‖ + 1) + 1)
    apply ((Set.finite_Iic K).prod
      (Set.Finite.pi' fun _ : Fin N ↦ Set.finite_Icc (-B) B)).subset
    rintro ⟨k, m⟩ ⟨hk, x, hx, hxc⟩
    refine ⟨hk, ?_⟩
    intro j
    constructor
    all_goals
      have hp : 0 < (2 : ℝ)^k := by positivity
      have hpK : (2 : ℝ)^k ≤ (2 : ℝ)^K :=
        pow_le_pow_right₀ (by norm_num) hk
      have hxn : ‖x‖ < ‖c‖ + 1 := norm_lt_of_mem_ball hxc
      have hnorm : |x j| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      have hxj : |x j| < ‖c‖ + 1 := hnorm.trans_lt hxn
      have hlo := (div_le_iff₀ hp).mp (hx j).1
      have hhi := (le_div_iff₀ hp).mp (hx j).2
      have hupper : x j * (2 : ℝ)^k ≤ (‖c‖ + 1) * (2 : ℝ)^K := by
        calc
          x j * (2 : ℝ)^k ≤ (‖c‖ + 1) * (2 : ℝ)^k :=
            mul_le_mul_of_nonneg_right (le_of_lt (abs_lt.mp hxj).2) hp.le
          _ ≤ (‖c‖ + 1) * (2 : ℝ)^K := mul_le_mul_of_nonneg_left hpK (by positivity)
      have hlower : -(‖c‖ + 1) * (2 : ℝ)^K ≤ x j * (2 : ℝ)^k := by
        calc
          -(‖c‖ + 1) * (2 : ℝ)^K ≤ -(‖c‖ + 1) * (2 : ℝ)^k :=
            mul_le_mul_of_nonpos_left hpK (by linarith [norm_nonneg c])
          _ ≤ x j * (2 : ℝ)^k :=
            mul_le_mul_of_nonneg_right (le_of_lt (abs_lt.mp hxj).1) hp.le
    · have hh : (-(B : ℝ)) ≤ (m j : ℝ) := by nlinarith
      exact_mod_cast hh
    · have hh : (m j : ℝ) ≤ (B : ℝ) := by nlinarith
      exact_mod_cast hh
  let I := {q : ℕ × (Fin N → ℤ) // c ∉ Q q.1 q.2}
  let A : I → Set (EuclideanSpace ℝ (Fin N)) := fun q ↦ Q q.val.1 q.val.2
  let size : I → ℝ := fun q ↦ Real.sqrt N * (1 / (2 : ℝ)^q.val.1)
  have hclosed : ∀ i, IsClosed (A i) := by
    intro i
    change IsClosed {y : EuclideanSpace ℝ (Fin N) | ∀ j,
      (i.val.2 j : ℝ) / (2 : ℝ)^i.val.1 ≤ y j ∧
        y j ≤ ((i.val.2 j : ℝ) + 1) / (2 : ℝ)^i.val.1}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    exact (isClosed_le continuous_const (EuclideanSpace.proj j).continuous).inter
      (isClosed_le (EuclideanSpace.proj j).continuous continuous_const)
  have hsize : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ≤ size i := by
    intro i x hx y hy
    apply euclidean_coordinate_box_diameter_le _ (by positivity)
    intro j
    rw [Real.dist_eq, abs_le]
    have heq : ((i.val.2 j : ℝ) + 1) / (2 : ℝ)^i.val.1 -
        (i.val.2 j : ℝ) / (2 : ℝ)^i.val.1 = 1 / (2 : ℝ)^i.val.1 := by ring
    constructor <;> linarith [hx j, hy j]
  have hfinite : ∀ η : ℝ, 0 < η →
      {i : I | (∃ x ∈ A i, dist x c < 1) ∧ η ≤ size i}.Finite := by
    intro η hη
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
      (div_pos hη (show 0 < Real.sqrt N + 1 by positivity)) (by norm_num : (1/2 : ℝ) < 1)
    have hsmall : Real.sqrt N * (1 / (2 : ℝ)^K) < η := by
      have hh : 1 / (2 : ℝ)^K < η / (Real.sqrt N + 1) := by simpa [div_pow] using hK
      have hm := (lt_div_iff₀ (show 0 < Real.sqrt N + 1 by positivity)).mp hh
      nlinarith [show 0 < 1 / (2 : ℝ)^K by positivity]
    apply Set.Finite.of_injOn (f := Subtype.val) ?_
      (fun _ _ _ _ h ↦ Subtype.val_injective h) (hlevels K)
    intro i hi
    refine ⟨?_, hi.1⟩
    by_contra hn
    have hk : K ≤ i.val.1 := (lt_of_not_ge hn).le
    have hpow := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hk
    have hquot : 1 / (2 : ℝ)^i.val.1 ≤ 1 / (2 : ℝ)^K :=
      one_div_le_one_div_of_le (by positivity) hpow
    have hh := mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg (N : ℝ))
    exact (not_lt_of_ge hi.2) (hh.trans_lt hsmall)
  obtain h := closed_family_shrinks_at A size c hclosed (fun i ↦ i.property)
    hsize 1 (by norm_num) hfinite
  intro ε hε
  obtain ⟨δ, hδ, hshrink⟩ := h ε hε
  exact ⟨δ, hδ, fun k m hc hm y hy ↦ hshrink ⟨(k, m), hc⟩ hm y hy⟩




end HolomorphicAnosov
