import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace HolomorphicAnosov

/-- The radial parameter in Hatcher's punctured-cell deformation is one on
the unit sphere. Source: Hatcher Theorem 4.8, p.349, boundary-fixed radial
retraction. Writing c=norm(z-p) squared, b=inner p (z-p), the equation
norm z=1 gives c+2b=1-norm p squared. Thus the discriminant is (b+c)
squared with b+c positive, and the positive square root makes the quotient
exactly one. -/
theorem radial_ray_sphere_parameter_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p z : E) (hp : ‖p‖ < 1) (hz : ‖z‖ = 1) :
    (-inner ℝ p (z-p) + Real.sqrt ((inner ℝ p (z-p)) ^ 2 +
      (1 - ‖p‖ ^ 2) * ‖z-p‖ ^ 2)) / ‖z-p‖ ^ 2 = 1 := by
  let v := z - p
  let b := inner ℝ p v
  let c := ‖v‖ ^ 2
  let d := 1 - ‖p‖ ^ 2
  change (-b + Real.sqrt (b ^ 2 + d * c)) / c = 1
  have hne : z ≠ p := by intro he; rw [he] at hz; linarith
  have hc : 0 < c := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hd : 0 < d := by dsimp [d]; nlinarith [norm_nonneg p]
  have hbc : c + 2 * b = d := by
    have he : p + v = z := by dsimp [v]; abel
    have hn := norm_add_sq_real p v
    rw [he, hz] at hn
    dsimp [c, b, d]
    nlinarith [hn]
  have hpos : 0 < b + c := by linarith
  have hdisc : b ^ 2 + d * c = (b + c) ^ 2 := by nlinarith [hbc]
  rw [hdisc, Real.sqrt_sq (le_of_lt hpos)]
  have he : -b + (b + c) = c := by ring
  rw [he, div_self hc.ne']

end HolomorphicAnosov
