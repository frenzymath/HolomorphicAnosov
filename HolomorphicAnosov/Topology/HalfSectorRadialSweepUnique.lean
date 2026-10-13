import Mathlib.Analysis.Complex.Circle

/-!
# Uniqueness of positive radial sweep coordinates

This is the algebraic uniqueness step in Cairns §4(C5).  The parent geometric
proof supplies a front avoiding the apex and injectivity of its normalized
direction map; this helper identifies the front point and positive scalar from
their affine radial combination.
-/

namespace HolomorphicAnosov

open Set

/-- Positive affine radial coordinates are unique when normalized directions
are injective on the front. -/
theorem halfSector_radial_sweep_unique
    (M : ℂ) (L : Set ℂ)
    (hM : ∀ Q ∈ L, Q ≠ M)
    (hinj : Set.InjOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) L)
    {Q R : ℂ} (hQ : Q ∈ L) (hR : R ∈ L)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (heq : (1 - t) • M + t • Q = (1 - u) • M + u • R) :
    Q = R ∧ t = u := by
  have hdiff : t • (Q - M) = u • (R - M) := by
    calc
      t • (Q - M) = ((1 - t) • M + t • Q) - M := by module
      _ = ((1 - u) • M + u • R) - M := congrArg (fun z : ℂ ↦ z - M) heq
      _ = u • (R - M) := by module
  have hscaled : Q - M = (u / t) • (R - M) := by
    calc
      Q - M = (1 / t) • (t • (Q - M)) := by
        rw [one_div, inv_smul_smul₀ (ne_of_gt ht)]
      _ = (1 / t) • (u • (R - M)) := by rw [hdiff]
      _ = (u / t) • (R - M) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hnormQ : ‖Q - M‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hM Q hQ))
  have hnormR : ‖R - M‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hM R hR))
  have hdir : (Q - M) / (‖Q - M‖ : ℂ) =
      (R - M) / (‖R - M‖ : ℂ) := by
    rw [hscaled, norm_smul, norm_div]
    have hpos : 0 < u / t := div_pos hu ht
    norm_num [Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos hu, abs_of_pos ht]
    field_simp [hnormR, ne_of_gt ht, ne_of_gt hu]
  have hQR : Q = R := hinj hQ hR hdir
  subst R
  have hnorm := congrArg norm hdiff
  rw [norm_smul, norm_smul] at hnorm
  norm_num [Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hu] at hnorm
  exact ⟨rfl, hnorm.resolve_right (sub_ne_zero.mpr (hM Q hQ))⟩

end HolomorphicAnosov
