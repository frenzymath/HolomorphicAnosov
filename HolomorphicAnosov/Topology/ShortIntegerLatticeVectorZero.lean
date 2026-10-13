import Mathlib.Analysis.Normed.Group.AddCircle

namespace HolomorphicAnosov

/-- A lattice representative shorter than one is zero, including the empty
coordinate space. Source: the integer-displacement step of Manning's target
canonical-coordinate argument (Lemma 6, pp.427–428); each coordinate is an integer,
and the original finite-product norm bounds its absolute value strictly below one. -/
theorem short_integer_lattice_vector_zero
    {n : ℕ} (v : Fin n → ℝ) (hz : ∀ i, (v i : UnitAddCircle) = 0)
    (hnorm : ‖v‖ < 1) : v = 0 := by
  funext i
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hz i)
  have hic : ‖v i‖ < 1 := (norm_le_pi_norm v i).trans_lt hnorm
  have hzcast : (z : ℝ) = v i := by simpa only [zsmul_eq_mul, mul_one] using hz
  rw [← hzcast, Real.norm_eq_abs] at hic
  obtain ⟨hzlo, hzhi⟩ := abs_lt.mp hic
  have hzlo' : (-1 : ℤ) < z := by exact_mod_cast hzlo
  have hzhi' : z < (1 : ℤ) := by exact_mod_cast hzhi
  have hzz : z = 0 := by omega
  have hi0 : v i = 0 := by simpa only [hzz, Int.cast_zero] using hzcast.symm
  simpa only [Pi.zero_apply] using hi0

end HolomorphicAnosov
