import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.Convex.Join

open Set
namespace HolomorphicAnosov

/-- A boundary point off the base of a convex triangular body has a supporting
functional that strictly separates the apex. Source: Cairns (1951), §3 Case II,
p.863; agent-written supporting-functional expansion. Separate the body interior
from q, obtaining f≤f(q) on the body. Write q as a strict convex combination of
the apex and an interior base point; endpoint visibility excludes the two base
endpoints. This gives f(M)≥f(q). Equality would force the base point, hence both
base endpoints, to have value f(q). Then f is constant on the containing triangle,
contradicting strict separation at an interior point of the body. -/
theorem convex_triangle_visible_supporting_functional_g2
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hKint : (interior K).Nonempty)
    {M A B q : E} (hsub : K ⊆ convexHull ℝ {M, A, B})
    (hA : A ∈ K) (hB : B ∈ K) (hM : M ∉ K)
    (hvisA : IsVisible ℝ K M A) (hvisB : IsVisible ℝ K M B)
    (hq : q ∈ K) (hqint : q ∉ interior K) (hqbase : q ∉ segment ℝ A B) :
    ∃ f : E →L[ℝ] ℝ, (∀ x ∈ K, f x ≤ f q) ∧ f q < f M := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hqint
  have hbound : ∀ x ∈ K, f x ≤ f q := by
    intro x hx
    apply closure_minimal (fun z hz ↦ (hf z hz).le) (isClosed_Iic.preimage f.continuous)
    rw [hK.closure_interior_eq_closure_of_nonempty_interior hKint]
    exact subset_closure hx
  have hqhull := hsub hq
  rw [convexHull_insert (insert_nonempty A {B}), mem_convexJoin] at hqhull
  obtain ⟨m, hm, y, hy, hqy⟩ := hqhull
  have hmM : m = M := mem_singleton_iff.mp hm
  subst m
  rw [convexHull_pair] at hy
  have hyK : y ∈ K := hK.segment_subset hA hB hy
  have hqM : q ≠ M := ne_of_mem_of_not_mem hq hM
  have hqA : q ≠ A := fun h ↦ hqbase (h ▸ left_mem_segment ℝ A B)
  have hqB : q ≠ B := fun h ↦ hqbase (h ▸ right_mem_segment ℝ A B)
  have hyA : y ≠ A := by
    intro h
    subst y
    exact hvisA hq ⟨mem_segment_iff_wbtw.mp hqy, hqM, hqA⟩
  have hyB : y ≠ B := by
    intro h
    subst y
    exact hvisB hq ⟨mem_segment_iff_wbtw.mp hqy, hqM, hqB⟩
  obtain ⟨a, b, ha, hb, hab, hqyEq⟩ := hqy
  have haPos : 0 < a := by
    by_contra hn
    have haz : a = 0 := le_antisymm (not_lt.mp hn) ha
    have hb1 : b = 1 := by linarith
    have hqy : q = y := by simpa [haz, hb1] using hqyEq.symm
    exact hqbase (hqy ▸ hy)
  have hbPos : 0 < b := by
    by_contra hn
    have hbz : b = 0 := le_antisymm (not_lt.mp hn) hb
    have ha1 : a = 1 := by linarith
    exact hqM (by simpa [hbz, ha1] using hqyEq.symm)
  have hfqy : a * f M + b * f y = f q := by
    simpa using congrArg f hqyEq
  have hfy := hbound y hyK
  have hfMge : f q ≤ f M := by
    have hprod := mul_nonneg hb (sub_nonneg.mpr hfy)
    have hsum := congrArg (fun r : ℝ ↦ r * f q) hab
    by_contra hn
    have hpos := mul_pos haPos (sub_pos.mpr (not_le.mp hn))
    nlinarith
  refine ⟨f,hbound,lt_of_le_of_ne hfMge ?_⟩
  intro hEq
  have hfM : f M=f q := hEq.symm
  have hfyEq : f y = f q := by
    have hsum := congrArg (fun r : ℝ ↦ r * f q) hab
    have hzero : b * (f y - f q) = 0 := by rw [hfM] at hfqy; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hbPos.ne')
  have hyOpen := mem_openSegment_of_ne_left_right hyA.symm hyB.symm hy
  obtain ⟨u, v, hu, hv, huv, huvEq⟩ := hyOpen
  have hfuv : u * f A + v * f B = f y := by simpa using congrArg f huvEq
  have hfA := hbound A hA
  have hfB := hbound B hB
  have hfAEq : f A = f q := by
    have hsum := congrArg (fun r : ℝ ↦ r * f q) huv
    have hprod := mul_nonneg hv.le (sub_nonneg.mpr hfB)
    apply le_antisymm hfA
    by_contra hn
    have hpos := mul_pos hu (sub_pos.mpr (not_le.mp hn))
    nlinarith
  have hfBEq : f B = f q := by
    have hsum := congrArg (fun r : ℝ ↦ r * f q) huv
    have hzero : v * (f B - f q) = 0 := by rw [hfAEq] at hfuv; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hv.ne')
  have hflat : convexHull ℝ {M, A, B} ⊆ f ⁻¹' {f q} := by
    apply convexHull_min _ ((convex_singleton (f q)).linear_preimage f.toLinearMap)
    simp only [insert_subset_iff, singleton_subset_iff, mem_preimage, mem_singleton_iff]
    exact ⟨hfM, hfAEq, hfBEq⟩
  obtain ⟨p, hp⟩ := hKint
  have heq : f p = f q := hflat (hsub (interior_subset hp))
  exact (hf p hp).ne heq

end HolomorphicAnosov

