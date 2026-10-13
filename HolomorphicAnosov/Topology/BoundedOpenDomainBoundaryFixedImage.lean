import HolomorphicAnosov.Topology.BoundedEuclideanFixedPoint

namespace HolomorphicAnosov

open Set Metric
open scoped OnePoint

/-- A bounded open domain cannot be pushed outside itself by a bounded continuous
map which fixes its boundary. Agent-written consequence of the bounded Euclidean
fixed-point theorem (Dold, 1965, homotopy and normalization laws, pp.1–2).

Paste the given map inside the domain and the identity outside. Boundary agreement
makes the pasted map continuous. If it omitted a domain point b, then b+id minus
the pasted map would be bounded: outside the bounded domain it is b, and inside
both the domain and the given map are bounded. A fixed point would force the
pasted map to equal b, a contradiction. -/
theorem bounded_open_domain_image_meets
    (A : Set ℂ) (_hAo : IsOpen A) (hAb : Bornology.IsBounded A)
    (hne : A.Nonempty) (R : C(ℂ, ℂ)) (hRb : Bornology.IsBounded (range R))
    (hfix : ∀ z ∈ frontier A, R z = z) :
    (A ∩ range R).Nonempty := by
  classical
  obtain ⟨b, hb⟩ := hne
  by_contra hdis
  let F : ℂ → ℂ := A.piecewise R id
  have hF : Continuous F :=
    continuous_piecewise (fun z hz ↦ hfix z hz) R.continuous.continuousOn
      continuous_id.continuousOn
  have hav : ∀ z, F z ≠ b := by
    intro z hz
    by_cases hzA : z ∈ A
    · apply hdis
      refine ⟨b, hb, z, ?_⟩
      simpa [F, hzA] using hz
    · have heq : z = b := by simpa [F, hzA] using hz
      exact hzA (heq.symm ▸ hb)
  obtain ⟨M, hM⟩ := hAb.exists_norm_le
  obtain ⟨N, hN⟩ := hRb.exists_norm_le
  let K := ‖b‖ + max M 0 + max N 0
  have hK : 0 ≤ K := by positivity
  have hbound (z : ℂ) : ‖b + z - F z‖ ≤ K := by
    by_cases hz : z ∈ A
    · calc
        ‖b + z - F z‖ ≤ ‖b + z‖ + ‖F z‖ := norm_sub_le _ _
        _ ≤ (‖b‖ + ‖z‖) + ‖R z‖ := by
          rw [show F z = R z by simp [F, hz]]
          gcongr
          exact norm_add_le _ _
        _ ≤ K := by
          have hm := hM z hz
          have hn := hN (R z) (mem_range_self z)
          dsimp [K]
          linarith [le_max_left M 0, le_max_left N 0]
    · simp only [F, Set.piecewise_eq_of_notMem A _ _ hz, id_eq, add_sub_cancel_right]
      dsimp [K]
      linarith [le_max_right M 0, le_max_right N 0]
  let e := Complex.orthonormalBasisOneI.repr
  let G : C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)) :=
    ⟨fun z ↦ e (b + e.symm z - F (e.symm z)), by fun_prop⟩
  obtain ⟨z, hz⟩ := Topology.bounded_euclidean_fixed_point 2 G K hK (fun z ↦ by
    change ‖e (b + e.symm z - F (e.symm z))‖ ≤ K
    rw [e.norm_map]
    exact hbound (e.symm z))
  have heq := congrArg e.symm hz
  change e.symm (e (b + e.symm z - F (e.symm z))) = e.symm z at heq
  rw [e.symm_apply_apply] at heq
  apply hav (e.symm z)
  linear_combination -heq

end HolomorphicAnosov
