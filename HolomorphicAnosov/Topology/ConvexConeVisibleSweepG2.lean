import HolomorphicAnosov.Topology.HalfSectorOpenSweepClosure
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Visible

open Set
namespace HolomorphicAnosov

/-- Every nonapex point of a cone hull outside a closed convex set containing
its base lies strictly before a visible point of that set on the same ray.
Source: Cairns (1951), §3 Case II, p.863, radial shadow construction. Write the
point on an apex-to-base segment, and take the first intersection with the
closed set. If this first intersection came before the point, convexity with
the base endpoint would put the point in the removed set. Thus the point lies
strictly between the apex and that visible first intersection. -/
theorem convexCone_complement_visible_sweep_g2
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : E) (S K : Set E) (hS : S.Nonempty) (hK : Convex ℝ K)
    (hKclosed : IsClosed K) (hSK : S ⊆ K)
    {x : E} (hx : x ∈ convexHull ℝ (insert M S) \ K) (hxM : x ≠ M) :
    ∃ Q ∈ K, IsVisible ℝ K M Q ∧ x ∈ openSegment ℝ M Q := by
  have hxh := hx.1
  rw [convexHull_insert hS,mem_convexJoin] at hxh
  obtain ⟨a,ha,y,hy,hxy⟩ := hxh
  have haM : a=M := mem_singleton_iff.mp ha
  subst a
  have hyK : y ∈ K := convexHull_min hSK hK hy
  obtain ⟨Q,hQ,hMQy,hvis⟩ := hKclosed.exists_wbtw_isVisible hyK M
  rw [segment_eq_image_lineMap] at hxy
  obtain ⟨t,ht,hxt⟩ := hxy
  obtain ⟨s,hs,hsQ⟩ := hMQy
  have hts : t < s := by
    by_contra hn
    have hst : s ≤ t := not_lt.mp hn
    have hmid : Wbtw ℝ Q x y := by
      have hh := (Wbtw.of_le_of_le hst ht.2).map (AffineMap.lineMap M y)
      simpa only [hsQ,hxt,AffineMap.lineMap_apply_one] using hh
    exact hx.2 (hK.mem_of_wbtw hmid hQ hyK)
  have hmid : Wbtw ℝ M x Q := by
    have hh := (Wbtw.of_le_of_le ht.1 hts.le).map (AffineMap.lineMap M y)
    simpa only [hsQ,hxt,AffineMap.lineMap_apply_zero] using hh
  exact ⟨Q,hQ,hvis,mem_openSegment_of_ne_left_right hxM.symm
    (ne_of_mem_of_not_mem hQ hx.2) hmid.mem_segment⟩

end HolomorphicAnosov
