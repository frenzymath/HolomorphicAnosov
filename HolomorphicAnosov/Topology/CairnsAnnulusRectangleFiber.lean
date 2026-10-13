import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
open Set
namespace HolomorphicAnosov.Topology
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

lemma radial_norm (u : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) :
    ‖cairns_annulus_rectangle_radial_formula u‖ = u.1.2 := by
  have hs := EuclideanSpace.norm_sq_eq (cairns_annulus_rectangle_radial_formula u)
  have hs' : ‖cairns_annulus_rectangle_radial_formula u‖ ^ 2 = u.1.2 ^ 2 := by
    calc
      _ = ∑ i, ‖(cairns_annulus_rectangle_radial_formula u).ofLp i‖ ^ 2 := hs
      _ = u.1.2 ^ 2 * (Real.cos (2 * Real.pi * u.1.1) ^ 2 +
          Real.sin (2 * Real.pi * u.1.1) ^ 2) := by
        simp [cairns_annulus_rectangle_radial_formula, Fin.sum_univ_two, sq]
        ring_nf
      _ = u.1.2 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hu : 0 ≤ u.1.2 := le_trans (by norm_num) u.2.2.1
  nlinarith [norm_nonneg (cairns_annulus_rectangle_radial_formula u)]

private lemma radial_coords (u : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) :
    (cairns_annulus_rectangle_radial_formula u).ofLp 0 =
      u.1.2 * Real.cos (2 * Real.pi * u.1.1) ∧
    (cairns_annulus_rectangle_radial_formula u).ofLp 1 =
      u.1.2 * Real.sin (2 * Real.pi * u.1.1) := by
  simp [cairns_annulus_rectangle_radial_formula]

private lemma angle_classify {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hcos : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b))
    (hsin : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b)) :
    a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  have hang : ((2 * Real.pi * a : ℝ) : Real.Angle) = (2 * Real.pi * b : ℝ) :=
    Real.Angle.cos_sin_inj hcos hsin
  obtain ⟨k, hk⟩ := (Real.Angle.angle_eq_iff_two_pi_dvd_sub).mp hang
  have hsub : a - b = k := by
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hp))
    nlinarith [hk]
  have hkbound : (-1 : ℤ) ≤ k ∧ k ≤ 1 := by
    constructor
    · by_contra h
      have hklt : (k : ℝ) < -1 := by exact_mod_cast (show k < (-1 : ℤ) by omega)
      nlinarith
    · by_contra h
      have hkgt : (1 : ℝ) < k := by exact_mod_cast (show (1 : ℤ) < k by omega)
      nlinarith
  rcases hkbound with ⟨hklo, hkhi⟩
  have hk_cases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · norm_num at hsub
    right; left
    have haeq : a = 0 := by linarith [ha0, hb1]
    have hbeq : b = 1 := by linarith [ha0, hb1]
    exact ⟨haeq, hbeq⟩
  · left
    apply sub_eq_zero.mp
    simpa using hsub
  · norm_num at hsub
    right; right
    have haeq : a = 1 := by linarith [ha1, hb0]
    have hbeq : b = 0 := by linarith [ha1, hb0]
    exact ⟨haeq, hbeq⟩

theorem cairns_annulus_rectangle_radial_formula_fiber (x y : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) :
    cairns_annulus_rectangle_radial_formula x = cairns_annulus_rectangle_radial_formula y ↔
      x.1.2 = y.1.2 ∧
        (x.1.1 = y.1.1 ∨
          (x.1.1 = 0 ∧ y.1.1 = 1) ∨
          (x.1.1 = 1 ∧ y.1.1 = 0)) := by
  constructor
  · intro h
    have hr : x.1.2 = y.1.2 := by
      have hh := congrArg norm h
      rw [radial_norm x, radial_norm y] at hh
      exact hh
    have hcx := congrArg (fun z : Plane => z.ofLp 0) h
    have hcy := congrArg (fun z : Plane => z.ofLp 1) h
    rw [radial_coords x |>.1, radial_coords y |>.1] at hcx
    rw [radial_coords x |>.2, radial_coords y |>.2] at hcy
    rw [hr] at hcx hcy
    have hpos : 0 < x.1.2 := lt_of_lt_of_le (by norm_num) x.2.2.1
    have hypos : 0 < y.1.2 := lt_of_lt_of_le (by norm_num) y.2.2.1
    have hc : Real.cos (2 * Real.pi * x.1.1) = Real.cos (2 * Real.pi * y.1.1) :=
      mul_left_cancel₀ hypos.ne' hcx
    have hs : Real.sin (2 * Real.pi * x.1.1) = Real.sin (2 * Real.pi * y.1.1) :=
      mul_left_cancel₀ hypos.ne' hcy
    have hx := x.property.1
    have hy := y.property.1
    exact ⟨hr, angle_classify (a := x.1.1) (b := y.1.1) hx.1 hx.2 hy.1 hy.2 hc hs⟩
  · rintro ⟨hr, ha⟩
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i
    · simp [cairns_annulus_rectangle_radial_formula, hr]
      rcases ha with h | h | h <;> simp_all
    · simp [cairns_annulus_rectangle_radial_formula, hr]
      rcases ha with h | h | h <;> simp_all
end HolomorphicAnosov.Topology
