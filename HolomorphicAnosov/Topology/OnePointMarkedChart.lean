import HolomorphicAnosov.Topology.OnePointSphereChartG9
import Mathlib.Topology.Algebra.Group.Basic

open Set

namespace HolomorphicAnosov

/-- For distinct points `x` and `y` in the one-point compactification of `ℂ`, there is a homeomorphism sending them to `0` and infinity. (Conway II, Lemma 5.4) -/
theorem onePoint_homeomorph_send_two_points_to_zero_infty
    (x y : OnePoint ℂ) (hxy : x ≠ y) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      e x = OnePoint.some 0 ∧ e y = OnePoint.infty := by
  obtain ⟨e, hey⟩ := onePoint_homeomorph_send_to_infty y
  have hex : e x ≠ OnePoint.infty := fun h ↦ hxy (e.injective (h.trans hey.symm))
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hex
  let t : ℂ ≃ₜ ℂ := Homeomorph.addRight (-w)
  refine ⟨e.trans t.onePointCongr, ?_, ?_⟩
  · change OnePoint.map t (e x) = OnePoint.some 0
    rw [← hw]
    simp [t]
  · change OnePoint.map t (e y) = OnePoint.infty
    rw [hey]
    rfl

end HolomorphicAnosov

