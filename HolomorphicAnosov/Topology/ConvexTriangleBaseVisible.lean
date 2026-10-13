import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Visible

open Set
namespace HolomorphicAnosov

/-- A visible point on the base of a convex body contained in an apex triangle
is a base endpoint, provided the body has nonempty interior and contains both
base endpoints. Source: Cairns (1951), §3 Case II, p.863, with the following
separation expansion. Separate the open body interior from the open ray ending
at a hypothetical visible base-interior point. Extend the inequalities to the
body and ray endpoints. The strict convex combination of the base endpoints
forces their two functional values to equal the separation level. The apex
has value at least that level, so the entire triangle does too, contradicting
the strict inequality on the nonempty body interior. -/
theorem convex_triangle_visible_base_endpoint
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    {M A B q : E} (hsub : K ⊆ convexHull ℝ {M, A, B})
    (hA : A ∈ K) (hB : B ∈ K) (hM : M ∉ K)
    (hq : q ∈ segment ℝ A B) (hvis : IsVisible ℝ K M q) :
    q = A ∨ q = B := by
  by_contra hn
  push Not at hn
  have hqK := hK.segment_subset hA hB hq
  have hMq : M ≠ q := (ne_of_mem_of_not_mem hqK hM).symm
  have hdis : Disjoint (interior K) (openSegment ℝ M q) := by
    apply disjoint_left.mpr
    intro z hz hzray
    exact hvis (interior_subset hz) ⟨mem_segment_iff_wbtw.mp
      (openSegment_subset_segment ℝ M q hzray),
      fun he ↦ hM (he ▸ interior_subset hz),
      fun he ↦ hMq (right_mem_openSegment_iff.mp (he ▸ hzray))⟩
  obtain ⟨f, c, hfi, hfray⟩ := geometric_hahn_banach_open hK.interior
    isOpen_interior (convex_openSegment M q) hdis
  have hfK : ∀ z ∈ K, f z ≤ c := by
    intro z hz
    apply closure_minimal (fun z hz ↦ (hfi z hz).le)
      (isClosed_Iic.preimage f.continuous)
    rw [hK.closure_interior_eq_closure_of_nonempty_interior hKi]
    exact subset_closure hz
  have hfseg : ∀ z ∈ segment ℝ M q, c ≤ f z := by
    intro z hz
    exact closure_minimal hfray (isClosed_Ici.preimage f.continuous)
      (segment_subset_closure_openSegment hz)
  have hfq : f q = c := le_antisymm (hfK q hqK) (hfseg q (right_mem_segment ..))
  have hfM := hfseg M (left_mem_segment ℝ M q)
  obtain ⟨a, b, ha, hb, hab, heq⟩ := mem_openSegment_of_ne_left_right hn.1.symm hn.2.symm hq
  have heqf : a * f A + b * f B = c := by
    simpa only [map_add, map_smul, smul_eq_mul, hfq] using congrArg f heq
  have hfA := hfK A hA
  have hfB := hfK B hB
  have habc : a * c + b * c = c := by nlinarith [congrArg (fun t : ℝ ↦ t * c) hab]
  have hAe : f A = c := by
    have := mul_nonneg hb.le (sub_nonneg.mpr hfB)
    have he : a * (c - f A) = 0 := by nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha.ne')).symm
  have hBe : f B = c := by
    have he : b * (c - f B) = 0 := by rw [hAe] at heqf; nlinarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hb.ne')).symm
  have htri : convexHull ℝ {M, A, B} ⊆ {z | c ≤ f z} := by
    apply convexHull_min _ ((convex_Ici c).linear_preimage f.toLinearMap)
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hfM, hAe.ge, hBe.ge⟩
  obtain ⟨z, hz⟩ := hKi
  exact (hfi z hz).not_ge (htri (hsub (interior_subset hz)))

end HolomorphicAnosov
