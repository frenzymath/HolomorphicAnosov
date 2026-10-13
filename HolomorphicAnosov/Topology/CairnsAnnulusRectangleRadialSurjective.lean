import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialFormula
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
open Set
namespace HolomorphicAnosov.Topology
local notation "Plane" => EuclideanSpace ℝ (Fin 2)
theorem cairns_annulus_rectangle_radial_formula_surjective :
    ∀ z : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      ∃ x : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2,
        cairns_annulus_rectangle_radial_formula x = (z : Plane) := by
  intro z
  let w : ℂ := ⟨(z : Plane).ofLp 0, (z : Plane).ofLp 1⟩
  have hwpos : 0 < ‖w‖ := by
    have hz : 0 < ‖(z : Plane)‖ := lt_of_lt_of_le (by norm_num) z.property.1
    have hsqz := EuclideanSpace.norm_sq_eq (z : Plane)
    have hsqw : ‖w‖ ^ 2 = ‖(z : Plane)‖ ^ 2 := by
      rw [Complex.sq_norm, EuclideanSpace.norm_sq_eq]
      simp [w, Fin.sum_univ_two]
      ring
    nlinarith [norm_nonneg w]
  have hw : ‖w‖ = ‖(z : Plane)‖ := by
    have hsqz := EuclideanSpace.norm_sq_eq (z : Plane)
    have hsqw : ‖w‖ ^ 2 = ‖(z : Plane)‖ ^ 2 := by
      rw [Complex.sq_norm, EuclideanSpace.norm_sq_eq]
      simp [w, Fin.sum_univ_two]
      ring
    nlinarith [norm_nonneg w, norm_nonneg (z : Plane)]
  let θ : ℝ := if 0 ≤ Complex.arg w then Complex.arg w else Complex.arg w + 2 * Real.pi
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]; split_ifs with h <;> nlinarith [Complex.neg_pi_lt_arg w]
  have hθ1 : θ ≤ 2 * Real.pi := by
    dsimp [θ]; split_ifs with h
    · nlinarith [Complex.arg_le_pi w]
    · nlinarith [Complex.arg_le_pi w]
  let t : Icc (0 : ℝ) 1 := ⟨θ / (2 * Real.pi),
    ⟨div_nonneg hθ0 (by positivity), (div_le_iff₀ (by positivity)).2 (by nlinarith)⟩⟩
  let r : Icc (1 : ℝ) 2 := ⟨‖(z : Plane)‖, z.property⟩
  let x : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2 := ⟨(t, r), ⟨t.2, r.2⟩⟩
  refine ⟨x, ?_⟩
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i
  · simp [x, cairns_annulus_rectangle_radial_formula, t, r]
    have hc := Complex.norm_mul_cos_arg w
    have hθc : Real.cos θ = Real.cos (Complex.arg w) := by
      dsimp [θ]
      split_ifs with h <;> simp [Real.cos_add_two_pi]
    have harg : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
      field_simp
    rw [harg, hθc]
    simpa [w, hw] using hc
  · simp [x, cairns_annulus_rectangle_radial_formula, t, r]
    have hs := Complex.norm_mul_sin_arg w
    have hθs : Real.sin θ = Real.sin (Complex.arg w) := by
      dsimp [θ]
      split_ifs with h <;> simp [Real.sin_add_two_pi]
    have harg : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
      field_simp
    rw [harg, hθs]
    simpa [w, hw] using hs
end HolomorphicAnosov.Topology
