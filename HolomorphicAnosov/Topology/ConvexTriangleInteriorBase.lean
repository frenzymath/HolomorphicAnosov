import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Set
namespace HolomorphicAnosov

/-- A convex set containing the base of a triangle and a point of its ambient
interior has nonempty ambient interior. This is the affine-span step implicit
in Cairns (1951), §3 Case II, p.863. Extend the interior point slightly away
from the apex, express the extension as an apex/base convex combination, and
solve for the apex in the affine span of the convex set. That span contains
the whole triangle and thus a nonempty open set, so it is the ambient space.
The finite-dimensional convex interior criterion finishes the proof. -/
theorem convex_triangle_interior_nonempty_of_base
    {K : Set ℂ} (hK : Convex ℝ K) {M A B x : ℂ}
    (hA : A ∈ K) (hB : B ∈ K) (hx : x ∈ K)
    (hxi : x ∈ interior (convexHull ℝ {M, A, B})) :
    (interior K).Nonempty := by
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _
    (AffineMap.lineMap_apply_one (k := ℝ) M x) |>.eventually_mem
      (mem_interior_iff_mem_nhds.1 hxi) |>.exists_gt
  rw [convexHull_insert (insert_nonempty A {B}), mem_convexJoin] at ht
  obtain ⟨m, hm, y, hy, a, b, ha, hb, hab, heq⟩ := ht
  have hmM : m = M := mem_singleton_iff.mp hm
  subst m
  rw [convexHull_pair] at hy
  have hyK := hK.segment_subset hA hB hy
  have hc : 0 < t + a - 1 := by linarith
  have heqM : AffineMap.lineMap y x (t / (t + a - 1)) = M := by
    simp only [AffineMap.lineMap_apply_module, Algebra.smul_def] at heq ⊢
    push_cast at heq ⊢
    change (a : ℂ) * M + (b : ℂ) * y = (1 - (t : ℂ)) * M + (t : ℂ) * x at heq
    have hcC : (↑t + ↑a - 1 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have habC : (↑a + ↑b : ℂ) = 1 := by exact_mod_cast hab
    apply (mul_right_cancel₀ hcC)
    field_simp [hcC]
    linear_combination -heq + y * habC
  have hMspan : M ∈ affineSpan ℝ K := heqM ▸
    AffineMap.lineMap_mem _ (subset_affineSpan ℝ K hyK) (subset_affineSpan ℝ K hx)
  have hsub : convexHull ℝ {M, A, B} ⊆ affineSpan ℝ K := by
    apply convexHull_min _ (affineSpan ℝ K).convex
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hMspan, subset_affineSpan ℝ K hA, subset_affineSpan ℝ K hB⟩
  apply hK.interior_nonempty_iff_affineSpan_eq_top.mpr
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top ⟨x, hxi⟩]
  exact affineSpan_le.mpr (interior_subset.trans hsub)

end HolomorphicAnosov
