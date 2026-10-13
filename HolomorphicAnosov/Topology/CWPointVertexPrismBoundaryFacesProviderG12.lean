import Mathlib.Topology.CWComplex.Classical.Basic

open _root_.Topology
universe u
namespace HolomorphicAnosov

/-- Source provider for the maximum-norm prism boundary decomposition.
Fritsch–Piccinini Theorem 2.2.2(ii), p.58: a boundary point of the native
`(d+1)`-disk lies on an endpoint face or on a lateral face over the source
`d`-disk sphere. -/
theorem cw_point_vertex_prism_boundary_faces_provider
    (d : ℕ) (w : Fin (d + 1) → ℝ)
    (hw : w ∈ Metric.sphere (0 : Fin (d + 1) → ℝ) 1) :
    w (Fin.last d) = -1 ∨ w (Fin.last d) = 1 ∨
      ∃ j : Fin d, ‖w j.castSucc‖ = 1 := by
  have hnorm : ‖w‖ = 1 := by
    have hs := (Metric.mem_sphere.mp hw)
    simpa only [dist_zero_right] using hs
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm w).1
  by_cases hlast : i = Fin.last d
  · subst i
    have hi' : ‖w (Fin.last d)‖ = 1 := by simpa [hnorm] using hi
    rw [Real.norm_eq_abs] at hi'
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hi' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · have hle : i.val ≤ d := Nat.le_of_lt_succ i.isLt
    have hil : i.val < d := lt_of_le_of_ne hle (by
      intro h
      apply hlast
      apply Fin.ext
      exact h)
    let j : Fin d := ⟨i.val, hil⟩
    have hji : j.castSucc = i := by ext; rfl
    exact Or.inr (Or.inr ⟨j, by simpa [hji, hnorm] using hi⟩)

end HolomorphicAnosov

