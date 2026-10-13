import Mathlib.Analysis.Convex.StdSimplex

namespace HolomorphicAnosov.BarycentricGeometry
/-- A convex combination in an injectively indexed finite set can use its original
indices. This is Mathlib's finite convex hull criterion with `Finset.sum_image`.
Extend vertex weights by composition in one direction; use center of mass in the other. -/
theorem mem_convexHull_finset_image_iff {ι E : Type*}
    [AddCommGroup E] [Module ℝ E] (C : Finset ι) (b : ι → E)
    (hb : Set.InjOn b (C : Set ι)) (x : E) :
    x ∈ convexHull ℝ (b '' (C : Set ι)) ↔
      ∃ w : ι → ℝ, (∀ F ∈ C, 0 ≤ w F) ∧
        ∑ F ∈ C, w F = 1 ∧ ∑ F ∈ C, w F • b F = x := by
  classical
  constructor
  · intro hx
    rw [← Finset.coe_image] at hx
    obtain ⟨w, hw, hsum, heq⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun F ↦ w (b F), fun F hF ↦ hw _ (Finset.mem_image_of_mem _ hF), ?_, ?_⟩
    · rwa [Finset.sum_image (fun F hF G hG he ↦ hb hF hG he)] at hsum
    · rwa [Finset.sum_image (fun F hF G hG he ↦ hb hF hG he)] at heq
  · rintro ⟨w, hw, hsum, rfl⟩
    have h := C.centerMass_mem_convexHull hw (by rw [hsum]; norm_num)
      (fun F hF ↦ Set.mem_image_of_mem b hF)
    simpa [Finset.centerMass_eq_of_sum_1 _ _ hsum] using h

end HolomorphicAnosov.BarycentricGeometry
