import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Defs

namespace HolomorphicAnosov

open Set Metric

/-- A closed-ball homeomorphism preserving the boundary sphere preserves the open ball.

Source: elementary metric complement argument. Inside the closed unit disk, the open
ball is exactly the complement of the unit sphere. `Homeomorph.image_compl` then
transports this identity under any homeomorphism preserving the sphere. -/
theorem closedBall_homeo_image_ball_of_boundary
    (F : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (hB : F '' {z : Metric.closedBall (0 : ℂ) 1 | (z : ℂ) ∈ sphere (0 : ℂ) 1} =
      {z : Metric.closedBall (0 : ℂ) 1 | (z : ℂ) ∈ sphere (0 : ℂ) 1}) :
    F '' {z : Metric.closedBall (0 : ℂ) 1 | (z : ℂ) ∈ ball (0 : ℂ) 1} =
      {z : Metric.closedBall (0 : ℂ) 1 | (z : ℂ) ∈ ball (0 : ℂ) 1} := by
  let J : Set (Metric.closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ ball (0 : ℂ) 1}
  let B : Set (Metric.closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ sphere (0 : ℂ) 1}
  have hJ : J = Bᶜ := by
    ext z
    rw [mem_compl_iff]
    constructor
    · intro hz hzb
      exact (ne_of_lt hz) hzb
    · intro hzb
      change (z : ℂ) ∈ ball (0 : ℂ) 1
      have hz := z.property
      rw [mem_closedBall, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right]
      apply lt_of_le_of_ne hz
      intro heq
      apply hzb
      change (z : ℂ) ∈ sphere (0 : ℂ) 1
      rw [mem_sphere, dist_zero_right]
      exact heq
  change F '' J = J
  rw [hJ, F.image_compl, hB]

end HolomorphicAnosov
