import Mathlib.Analysis.Convex.StdSimplex

namespace HolomorphicAnosov.BarycentricGeometry
/-- Coordinates outside an original coordinate face vanish throughout its hull.
Source: Schultz, Math 246A §I.2, p.21 (restriction to subcomplexes). Each generating
vertex has zero outside coordinate, and the zero-coordinate set is convex. -/
theorem standard_face_coordinate_zero {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (i : ι) (hi : i ∉ A) (x : ι → ℝ)
    (hx : x ∈ convexHull ℝ ((fun j ↦ (Pi.single j 1 : ι → ℝ)) '' (A : Set ι))) :
    x i = 0 := by
  apply convexHull_min (t := {y : ι → ℝ | y i = 0}) ?_ ?_ hx
  · rintro y ⟨j, hj, rfl⟩
    change (Pi.single j 1 : ι → ℝ) i = 0
    have hji : j ≠ i := by intro he; exact hi (he ▸ hj)
    simp [Ne.symm hji]
  · intro y hy z hz a c _ _ _
    change a * y i + c * z i = 0
    rw [show y i = 0 from hy, show z i = 0 from hz]
    simp

end HolomorphicAnosov.BarycentricGeometry
