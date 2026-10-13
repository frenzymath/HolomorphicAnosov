import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov
open Set

/-- Every closed ray segment whose front point is strictly on the selected side
belongs to the closure of the strict radial star.

Source: Cairns (1951), §4(A), printed pp.863–864. The affine segment map is
continuous on the real parameter. Its parameters in `(0,1)` lie in the strict
star, since the signed transverse coordinate is the positive parameter times
the front point's coordinate. Density of `(0,1)` in `[0,1]` includes both the
center and the front endpoint in the closure. -/
theorem cairns_interior_ray_subset_closure
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) {Q : ℂ} (hQ : Q ∈ ν)
    (hSideQ : 0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
      (star (E₂ - E₁) * (Q - E₁)).im)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • ((E₁ + E₂) / 2) + t • Q ∈
      closure {z : ℂ | ∃ R ∈ ν, ∃ s ∈ Ioo (0 : ℝ) 1,
        z = (1 - s) • ((E₁ + E₂) / 2) + s • R ∧
        0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
          (star (E₂ - E₁) * (z - E₁)).im} := by
  let f : ℝ → ℂ := fun s ↦ (1 - s) • ((E₁ + E₂) / 2) + s • Q
  have hf : Continuous f := by fun_prop
  apply hf.continuousWithinAt.mem_closure (s := Ioo (0 : ℝ) 1)
  · simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using ht
  · intro s hs
    refine ⟨Q, hQ, s, hs, rfl, ?_⟩
    have hcross : (star (E₂ - E₁) * (f s - E₁)).im =
        s * (star (E₂ - E₁) * (Q - E₁)).im := by
      simp [f, Complex.mul_im, Complex.mul_re, Complex.real_smul]
      ring
    rw [hcross, ← mul_assoc, mul_comm _ s, mul_assoc]
    exact mul_pos hs.1 hSideQ

end HolomorphicAnosov
