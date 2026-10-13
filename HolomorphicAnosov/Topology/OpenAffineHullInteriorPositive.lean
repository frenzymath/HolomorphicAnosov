import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions

open Set
namespace HolomorphicAnosov

/-- An open affine coordinate that is nonnegative on a generating set is positive on the interior of its convex hull. (Cairns, §3) -/
theorem open_affine_positive_on_convexHull_interior
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f : E → ℝ) (hf : IsOpenMap f)
    (haff : ∀ x y : E, ∀ a b : ℝ, a + b = 1 →
      f (a • x + b • y) = a * f x + b * f y)
    {S : Set E} (hS : ∀ z ∈ S, 0 ≤ f z)
    {z : E} (hz : z ∈ interior (convexHull ℝ S)) : 0 < f z := by
  have hc : Convex ℝ {z | 0 ≤ f z} := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ f (a • x + b • y)
    rw [haff x y a b hab]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hsub := interior_mono (convexHull_min hS hc)
  have hz' : z ∈ interior (f ⁻¹' Ici 0) := hsub hz
  have := hf.interior_preimage_subset_preimage_interior hz'
  simpa only [interior_Ici, mem_preimage, mem_Ioi] using this

end HolomorphicAnosov
