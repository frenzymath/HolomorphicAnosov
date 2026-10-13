import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

namespace HolomorphicAnosov

open Set

/-- The intersection of two distinct stereographic punctures is path connected
in sphere dimension at least two. Source: Hatcher Proposition 1.14, p.35.
In the chart omitting the first pole it is Euclidean space minus the image of
the second pole. The complement of a point is path connected in dimension at
least two; the continuous inverse chart carries its paths back to the sphere. -/
theorem sphere_two_punctures_path_connected (n : ℕ) (hn : 2 ≤ n)
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hpq : p ≠ q) :
    IsPathConnected (({p}ᶜ ∩ {q}ᶜ) : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let e := stereographic' n p
  have hq : q ∈ e.source := by simpa [e] using hpq.symm
  have htarget : e.target = univ := stereographic'_target p
  have himage : e.symm '' {e q}ᶜ = {p}ᶜ ∩ {q}ᶜ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwtarget : w ∈ e.target := htarget ▸ mem_univ w
      refine ⟨?_, ?_⟩
      · simpa only [e, stereographic'_source] using e.map_target hwtarget
      · intro heq
        apply hw
        change e.symm w = q at heq
        exact (e.right_inv hwtarget).symm.trans (congrArg e heq)
    · rintro ⟨hzp, hzq⟩
      have hz : z ∈ e.source := by simpa only [e, stereographic'_source] using hzp
      refine ⟨e z, ?_, e.left_inv hz⟩
      intro heq
      exact hzq (e.injOn hz hq heq)
  rw [← himage]
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n by omega)
  apply (isPathConnected_compl_singleton_of_one_lt_rank hrank (e q)).image'
  exact e.continuousOn_symm.mono (by rw [htarget]; exact subset_univ _)

end HolomorphicAnosov

