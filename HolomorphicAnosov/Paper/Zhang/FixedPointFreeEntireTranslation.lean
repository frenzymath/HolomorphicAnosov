import HolomorphicAnosov.Analysis.ComplexPlaneBiholomorphismAffine

/-! This file proves that a fixed-point-free entire biholomorphism of `ℂ` is a translation. (Zhang, Lemma 4.2) -/

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

/-- An entire biholomorphism of `ℂ` with no fixed point is a translation. -/
theorem fixed_point_free_entire_translation (G J : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hJ : Differentiable ℂ J)
    (hJG : ∀ z, J (G z) = z) (hGJ : ∀ z, G (J z) = z)
    (hfree : ∀ z, G z ≠ z) : ∃ c : ℂ, ∀ z, G z = z + c := by
  obtain ⟨ab, hab, _⟩ := complex_plane_biholomorphism_affine.1 G J hG hJ hJG hGJ
  have ha : ab.1 = 1 := by
    by_contra hn
    have hd : 1 - ab.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
    apply hfree (ab.2 / (1 - ab.1))
    rw [hab.2.1]
    field_simp
    ring
  exact ⟨ab.2, fun z ↦ by rw [hab.2.1, ha, one_mul]⟩

end HolomorphicAnosov.Paper.Zhang
