import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Between

open Set

namespace HolomorphicAnosov

/-- Every component of the interior of a cone hull, after removing a convex set
containing its base, approaches the apex.

Source: the radial shadow construction in Cairns (1951), §3 Case II, p.863.
This elementary convex form is an agent expansion of that construction.
Write a point `x` of the hull on a segment from the apex `M` to a base-hull
point `y`. Every point `z` between `M` and `x` is outside `K`: otherwise
convexity and `y ∈ K` put `x` in `K`. The half-open segment `(M,x]` is also
in the hull interior by convexity. It is connected, contains `x`, and
approaches `M`, so its containing component approaches `M` as well. -/
theorem convexHull_apex_mem_closure_component
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : E) (S K : Set E) (hS : S.Nonempty) (hK : Convex ℝ K) (hSK : S ⊆ K)
    {x : E} (hx : x ∈ interior (convexHull ℝ (insert M S)) \ K) :
    M ∈ closure (connectedComponentIn (interior (convexHull ℝ (insert M S)) \ K) x) := by
  have hxHull := interior_subset hx.1
  rw [convexHull_insert hS, mem_convexJoin] at hxHull
  obtain ⟨a, ha, y, hy, hxy⟩ := hxHull
  have haM : a = M := mem_singleton_iff.mp ha
  subst a
  have hyK : y ∈ K := convexHull_min hSK hK hy
  let f : ℝ → E := fun t ↦ M + t • (x - M)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hsub : f '' Ioc (0 : ℝ) 1 ⊆ interior (convexHull ℝ (insert M S)) \ K := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨(convex_convexHull ℝ _).add_smul_sub_mem_interior
      (subset_convexHull ℝ _ (mem_insert M S)) hx.1 ht, ?_⟩
    intro hzK
    have hMzx : Wbtw ℝ M (f t) x := by
      apply mem_segment_iff_wbtw.mp
      simpa [f, AffineMap.lineMap_apply, add_comm] using
        lineMap_mem_segment (𝕜 := ℝ) M x ⟨ht.1.le, ht.2⟩
    exact hx.2 (hK.mem_of_wbtw ((mem_segment_iff_wbtw.mp hxy).trans_left_right hMzx)
      hzK hyK)
  have hxImage : x ∈ f '' Ioc (0 : ℝ) 1 := by
    exact ⟨1, ⟨zero_lt_one, le_rfl⟩, by simp [f]⟩
  have hcomponent := (isPreconnected_Ioc.image f hf.continuousOn).subset_connectedComponentIn
    hxImage hsub
  apply closure_mono hcomponent
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  simpa [f] using hf.continuousWithinAt.mem_closure_image hzero

end HolomorphicAnosov
