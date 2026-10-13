import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Segment

namespace HolomorphicAnosov

open Set

/-- A chord avoiding an embedded circle meets that circle only at its endpoints.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3(E), pp.863--864. The Lean statement isolates the elementary endpoint step
used in the countable attached-chord construction.
-/
theorem affine_lineMap_mem_circle_endpoint
    (σ : Circle → ℂ) (u v : Circle)
    (hAvoid : Disjoint (openSegment ℝ (σ u) (σ v)) (Set.range σ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hx : AffineMap.lineMap (σ u) (σ v) t ∈ Set.range σ) :
    t = 0 ∨ t = 1 := by
  by_contra hn
  have htn : ¬ t = 0 := fun ht0 ↦ hn (Or.inl ht0)
  have htn' : ¬ t = 1 := fun ht1 ↦ hn (Or.inr ht1)
  have hto : t ∈ Set.Ioo 0 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm htn), lt_of_le_of_ne ht.2 htn'⟩
  exact Set.disjoint_left.mp hAvoid
    (lineMap_mem_openSegment ℝ _ _ hto) hx

end HolomorphicAnosov
