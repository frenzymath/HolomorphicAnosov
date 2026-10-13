import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterCoordinate
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace HolomorphicAnosov.BarycentricGeometry
/-- A positively weighted face in a barycentric chain strictly separates its
inside coordinates from its outside coordinates. Source: Schultz, Math 246A
§I.2, Theorem 4, pp.24–25, positive-drop/equal-level argument. Each nested face
contributes a nonnegative difference, and the chosen face contributes positively. -/
theorem standard_flag_positive_weight_separates {ι : Type*} [DecidableEq ι]
    (C : Finset (Finset ι))
    (hchain : (C : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (w : Finset ι → ℝ) (hw : ∀ G ∈ C, 0 ≤ w G)
    (F : Finset ι) (hF : F ∈ C) (hwF : 0 < w F)
    (i j : ι) (hi : i ∈ F) (hj : j ∉ F) :
    (∑ G ∈ C, w G • ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ))) j <
    (∑ G ∈ C, w G • ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ))) i := by
  classical
  rw [Finset.sum_apply, Finset.sum_apply]
  change (∑ G ∈ C, w G * ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ)) j) <
    (∑ G ∈ C, w G * ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ)) i)
  simp only [standard_barycenter_coordinate]
  apply Finset.sum_lt_sum
  · intro G hG
    have hji : j ∈ G → i ∈ G := by
      intro hjG
      by_cases he : F = G
      · exact he ▸ hi
      · rcases hchain hF hG he with h | h
        · exact h.subset hi
        · exact False.elim (hj (h.subset hjG))
    by_cases hjG : j ∈ G
    · simp [hjG, hji hjG]
    · simp only [ite_eq_right hjG, mul_zero]
      exact mul_nonneg (hw G hG) (by split_ifs <;> positivity)
  · refine ⟨F, hF, ?_⟩
    simp only [ite_eq_right hj, ite_eq_left hi, mul_zero]
    exact mul_pos hwF (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hi⟩)))

end HolomorphicAnosov.BarycentricGeometry
