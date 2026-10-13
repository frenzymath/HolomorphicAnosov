import Mathlib.Analysis.Complex.Circle

namespace HolomorphicAnosov
open Set

/-- Positive radial coordinates are unique when the normalized direction map is injective.

This is the uniqueness sublemma in Cairns §4(A), pp.863--864. -/
theorem cairns_radial_point_unique
    {N : ℂ} {L : Set ℂ} (hN : ∀ Q ∈ L, Q ≠ N)
    {D : Type*} [TopologicalSpace D] (d : L ≃ₜ D) (dir : D → Circle) (hdir_inj : Function.Injective dir)
    (hd : ∀ Q : L, ((dir (d Q) : Circle) : ℂ) =
      ((Q : ℂ) - N) / (‖(Q : ℂ) - N‖ : ℂ))
    {Q R : L} {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (heq : (1 - t) • N + t • (Q : ℂ) =
      (1 - u) • N + u • (R : ℂ)) :
    Q = R ∧ t = u := by
  have hdiff : t • ((Q : ℂ) - N) = u • ((R : ℂ) - N) := by
    calc
      t • ((Q : ℂ) - N) = ((1 - t) • N + t • (Q : ℂ)) - N := by module
      _ = ((1 - u) • N + u • (R : ℂ)) - N := congrArg (fun z : ℂ => z - N) heq
      _ = u • ((R : ℂ) - N) := by module
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hscaled : (Q : ℂ) - N = (u / t) • ((R : ℂ) - N) := by
    calc
      (Q : ℂ) - N = (1 / t) • (t • ((Q : ℂ) - N)) := by
        rw [one_div, inv_smul_smul₀ ht0]
      _ = (1 / t) • (u • ((R : ℂ) - N)) := by rw [hdiff]
      _ = (u / t) • ((R : ℂ) - N) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hQnorm : ‖(Q : ℂ) - N‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr (hN Q Q.property)))
  have hRnorm : ‖(R : ℂ) - N‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr (hN R R.property)))
  have hdir_circle : dir (d Q) = dir (d R) := by
    apply Subtype.ext
    rw [hd, hd]
    rw [hscaled, norm_smul, norm_div]
    have hpos : 0 < u / t := div_pos hu ht
    norm_num [Real.norm_eq_abs, abs_of_pos hu, abs_of_pos ht]
    field_simp [hRnorm, ht0, ne_of_gt hu]
  have hdir : d Q = d R := hdir_inj hdir_circle
  have hQR : Q = R := d.injective hdir
  subst R
  have hnorm := congrArg norm hdiff
  rw [norm_smul, norm_smul] at hnorm
  norm_num [Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hu] at hnorm
  have hne : (Q : ℂ) - N ≠ 0 := sub_ne_zero.mpr (hN Q Q.property)
  exact ⟨rfl, hnorm.resolve_right hne⟩

end HolomorphicAnosov
