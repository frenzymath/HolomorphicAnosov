import HolomorphicAnosov.Topology.Barycentric.StandardFaceCoordinateZero
import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterCoordinate

namespace HolomorphicAnosov.BarycentricGeometry
/-- A nonempty coordinate face's barycenter belongs to an original face exactly
when its index set is contained there. Source: Schultz, Math 246A §I.2, p.21.
The forward direction uses its positive coordinates; the reverse uses its uniform
convex combination of the indexed standard vertices. -/
theorem standard_barycenter_mem_face_iff {ι : Type*} [DecidableEq ι]
    (F A : Finset ι) (hne : F.Nonempty) :
    (F.card : ℝ)⁻¹ • ∑ i ∈ F, (Pi.single i 1 : ι → ℝ) ∈
      convexHull ℝ ((fun i ↦ (Pi.single i 1 : ι → ℝ)) '' (A : Set ι)) ↔ F ⊆ A := by
  classical
  constructor
  · intro hx i hi
    by_contra hn
    have hz := standard_face_coordinate_zero A i hn _ hx
    rw [standard_barycenter_coordinate, ite_eq_left hi] at hz
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr hne.card_ne_zero)) hz
  · intro hFA
    have hsum : ∑ i ∈ F, (F.card : ℝ)⁻¹ = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hne.card_ne_zero)
    have h : F.centerMass (fun _ ↦ (F.card : ℝ)⁻¹) (fun i ↦ (Pi.single i 1 : ι → ℝ)) ∈
        convexHull ℝ ((fun i ↦ (Pi.single i 1 : ι → ℝ)) '' (A : Set ι)) :=
      F.centerMass_mem_convexHull (fun _ _ ↦ by positivity) (by rw [hsum]; norm_num)
        (fun i hi ↦ Set.mem_image_of_mem _ (hFA hi))
    simpa [Finset.centerMass_eq_of_sum_1 _ _ hsum, Finset.smul_sum] using h

end HolomorphicAnosov.BarycentricGeometry
