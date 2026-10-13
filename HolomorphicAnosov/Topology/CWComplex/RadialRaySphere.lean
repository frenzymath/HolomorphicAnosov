import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace HolomorphicAnosov

/-- Hatcher Theorem 4.8, p.349, punctured-cell radial projection: the ray
from an interior point p through any distinct point z of the closed unit
disk meets the unit sphere at the displayed quadratic-root parameter,
which is at least one.

Proof: put v=z-p, b=inner p v, c=norm v squared and d=1-norm p squared.
Both c and d are positive. The discriminant b squared+d*c exceeds b
squared, so its square root exceeds b and the displayed parameter is
positive. Squaring the defining root identity gives c*l squared+2*b*l=d.
The inner-product norm expansion then places p+l*v on the unit sphere.
If l<1, z=p+v lies beyond this positive root and the same quadratic
expansion would give norm z>1, contradicting disk membership. -/
theorem radial_ray_sphere_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p z : E) (hp : ‖p‖ < 1) (hz : ‖z‖ ≤ 1) (hne : z ≠ p) :
    let v := z - p
    let l := (-inner ℝ p v + Real.sqrt ((inner ℝ p v) ^ 2 +
      (1 - ‖p‖ ^ 2) * ‖v‖ ^ 2)) / ‖v‖ ^ 2
    1 ≤ l ∧ ‖p + l • v‖ = 1 := by
  dsimp only
  let v := z - p
  let b := inner ℝ p v
  let c := ‖v‖ ^ 2
  let d := 1 - ‖p‖ ^ 2
  let s := Real.sqrt (b ^ 2 + d * c)
  let l := (-b + s) / c
  change 1 ≤ l ∧ ‖p + l • v‖ = 1
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  have hc : 0 < c := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hd : 0 < d := by dsimp [d]; nlinarith [norm_nonneg p]
  have hdisc : 0 ≤ b ^ 2 + d * c := le_of_lt (add_pos_of_nonneg_of_pos (sq_nonneg b) (mul_pos hd hc))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = b ^ 2 + d * c := Real.sq_sqrt hdisc
  have hsb : b < s := by nlinarith [mul_pos hd hc]
  have hl : 0 < l := div_pos (by linarith) hc
  have hlc : l * c = -b + s := div_mul_cancel₀ _ hc.ne'
  have hroot : c * l ^ 2 + 2 * b * l = d := by
    have hsq : (l * c + b) ^ 2 = b ^ 2 + d * c := by rw [hlc]; convert hs2 using 1; ring
    have hmul : c * (c * l ^ 2 + 2 * b * l - d) = 0 := by nlinarith [hsq]
    have := (mul_eq_zero.mp hmul).resolve_left hc.ne'
    linarith
  have hnorm : ‖p + l • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hl]
    change ‖p‖ ^ 2 + 2 * (l * b) + (l * ‖v‖) ^ 2 = 1
    dsimp [c, d] at hroot
    nlinarith [hroot]
  have hzsq : c + 2 * b ≤ d := by
    have he : p + v = z := by dsimp [v]; abel
    have hn := norm_add_sq_real p v
    rw [he] at hn
    dsimp [c, b, d]
    nlinarith [norm_nonneg z]
  have hlone : 1 ≤ l := by
    by_contra h
    have hlt : l < 1 := lt_of_not_ge h
    have hbpos : 0 < c * l + 2 * b := by
      have he : l * (c * l + 2 * b) = d := by nlinarith [hroot]
      nlinarith
    have hh : 0 < (1 - l) * (c * (1 + l) + 2 * b) := by
      apply mul_pos (by linarith)
      linarith
    nlinarith [hroot]
  exact ⟨hlone, by nlinarith [norm_nonneg (p + l • v)]⟩

end HolomorphicAnosov
