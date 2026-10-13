import HolomorphicAnosov.Topology.Barycentric.FiniteChainCoordinateSeparator
import HolomorphicAnosov.Topology.Barycentric.StandardFlagPositiveWeightSeparates

namespace HolomorphicAnosov.BarycentricGeometry
/-- Every positively weighted face in one chain expansion occurs in every other
nonnegative chain expansion of the same vector. Source: Schultz, Math 246A §I.2,
Theorem 4, pp.24–25. The separator for an omitted face would force a zero inside
coordinate, or an inside coordinate no larger than an outside coordinate. Both
contradict positivity of that face's coefficient. No normalization is required. -/
theorem standard_flag_positive_weight_common {ι : Type*} [DecidableEq ι]
    (C D : Finset (Finset ι))
    (hC : (C : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (hD : (D : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F))
    (w v : Finset ι → ℝ) (hw : ∀ G ∈ C, 0 ≤ w G) (hv : ∀ G ∈ D, 0 ≤ v G)
    (heq : (∑ G ∈ C, w G • ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ))) =
      ∑ G ∈ D, v G • ((G.card : ℝ)⁻¹ • ∑ k ∈ G, (Pi.single k 1 : ι → ℝ)))
    (F : Finset ι) (hF : F ∈ C) (hne : F.Nonempty) (hwF : 0 < w F) : F ∈ D := by
  classical
  let b : Finset ι → ι → ℝ := fun G ↦ (G.card : ℝ)⁻¹ • ∑ k ∈ G, Pi.single k 1
  have hbc : ∀ G k, b G k = if k ∈ G then (G.card : ℝ)⁻¹ else 0 :=
    standard_barycenter_coordinate
  have hbn : ∀ G k, 0 ≤ b G k := by
    intro G k
    rw [hbc]
    split_ifs <;> positivity
  by_contra hnot
  obtain ⟨i, hi, hz | ⟨j, hj, hji⟩⟩ := finite_chain_coordinate_separator D hD F hne hnot
  · have hpos : 0 < (∑ G ∈ C, w G • b G) i := by
      rw [Finset.sum_apply]
      change 0 < ∑ G ∈ C, w G * b G i
      apply lt_of_lt_of_le (mul_pos hwF ?_) (Finset.single_le_sum (fun G hG ↦
        mul_nonneg (hw G hG) (hbn G i)) hF)
      rw [hbc, ite_eq_left hi]
      exact inv_pos.mpr (Nat.cast_pos.mpr hne.card_pos)
    have hz' : (∑ G ∈ D, v G • b G) i = 0 := by
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro G hG
      change v G * b G i = 0
      simp [hbc, hz G hG]
    change (∑ G ∈ C, w G • b G) = ∑ G ∈ D, v G • b G at heq
    rw [heq, hz'] at hpos
    exact (lt_irrefl 0) hpos
  · have hlt := standard_flag_positive_weight_separates C hC w hw F hF hwF i j hi hj
    rw [heq] at hlt
    have hle : (∑ G ∈ D, v G • b G) i ≤ (∑ G ∈ D, v G • b G) j := by
      rw [Finset.sum_apply, Finset.sum_apply]
      change (∑ G ∈ D, v G * b G i) ≤ ∑ G ∈ D, v G * b G j
      apply Finset.sum_le_sum
      intro G hG
      apply mul_le_mul_of_nonneg_left _ (hv G hG)
      rw [hbc, hbc]
      by_cases hiG : i ∈ G
      · simp [hiG, hji G hG hiG]
      · simp only [ite_eq_right hiG]
        split_ifs <;> positivity
    exact (not_lt_of_ge hle) hlt

end HolomorphicAnosov.BarycentricGeometry
