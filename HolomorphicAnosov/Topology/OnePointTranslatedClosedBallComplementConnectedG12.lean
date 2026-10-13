import HolomorphicAnosov.Topology.OnePointClosedBallComplementConnected

open Set Metric
open scoped OnePoint

namespace HolomorphicAnosov

/-- The complement of any translated closed complex ball in the one-point compactification is connected. (Ahlfors–Sario, III §4, 12D) -/
theorem onePoint_translated_closedBall_complement_connected (a : ℂ) (R : ℝ)
    (hR : 0 ≤ R) :
    IsConnected ((OnePoint.some '' closedBall a R)ᶜ) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-a)
  let E := e.onePointCongr
  have hball : (⇑e) '' closedBall a R = closedBall (0 : ℂ) R := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_closedBall] at hw ⊢
      change dist (w + -a) 0 ≤ R
      simpa [dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hw
    · intro hz
      rw [mem_closedBall] at hz
      refine ⟨z + a, ?_, ?_⟩
      · rw [mem_closedBall]
        have heq : dist (z + a) a = dist z 0 := by
          simpa only [zero_add] using (dist_add_right z 0 a)
        rw [heq]
        exact hz
      · dsimp [e]
        ring
  have himage : (⇑E) '' (OnePoint.some '' (closedBall a R)) =
      OnePoint.some '' (closedBall (0 : ℂ) R) := by
    ext z
    cases z using OnePoint.rec with
    | infty => simp [E, e]
    | coe u =>
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, hEq⟩
        change OnePoint.some (e v) = OnePoint.some u at hEq
        have hEq' : e v = u := OnePoint.coe_injective hEq
        subst u
        exact ⟨e v, hball ▸ ⟨v, hv, rfl⟩, rfl⟩
      · rintro ⟨v, hv, hvu⟩
        have hvu' : v = u := OnePoint.coe_injective hvu
        subst u
        refine ⟨OnePoint.some (e.symm v), ⟨e.symm v, ?_, rfl⟩, ?_⟩
        · have him : v ∈ (⇑e) '' closedBall a R := by
            rw [hball]
            exact hv
          rcases him with ⟨w, hw, hwe⟩
          have heq : w = e.symm v := by
            apply e.injective
            rw [hwe]
            simp
          simpa [heq] using hw
        · change OnePoint.some (e (e.symm v)) = OnePoint.some v
          congr 1
          exact e.apply_symm_apply v
  have hconn : IsConnected ((⇑E) '' ((OnePoint.some '' closedBall a R)ᶜ)) := by
    rw [E.image_compl, himage]
    exact onePoint_closedBall_complement_connected hR
  exact (E.isConnected_image).mp hconn

end HolomorphicAnosov

