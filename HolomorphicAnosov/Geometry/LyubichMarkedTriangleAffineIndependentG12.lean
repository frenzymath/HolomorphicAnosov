import HolomorphicAnosov.Geometry.IdealDiskTriangle
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace HolomorphicAnosov

/-- The three distinct marked unit-circle vertices are affinely independent. -/
theorem markedIdealDiskTriangle_vertices_affineIndependent
    (T : MarkedIdealDiskTriangle) : AffineIndependent ℝ T.vertex := by
  apply (affineIndependent_iff_not_collinear).2
  intro hcol
  let s : EuclideanGeometry.Sphere ℂ := ⟨0, 1⟩
  have hmem (i : Fin 3) : T.vertex i ∈ s := by
    rw [EuclideanGeometry.mem_sphere]
    simpa [s, dist_zero_right] using T.norm_vertex i
  have h01 : T.vertex 0 ≠ T.vertex 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (T.distinct h)
  have hline (i : Fin 3) : T.vertex i ∈ line[ℝ, T.vertex 0, T.vertex 1] := by
    exact hcol.mem_affineSpan_of_mem_of_ne (Set.mem_range_self 0)
      (Set.mem_range_self 1) (Set.mem_range_self i) h01
  have h2 := (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (s := s) (p := T.vertex 0) (q := T.vertex 1) (hmem 0) (hline 2)).mpr (hmem 2)
  have h1 := (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (s := s) (p := T.vertex 0) (q := T.vertex 1) (hmem 0) (hline 1)).mpr (hmem 1)
  rcases h1 with h10 | h1s
  · exact h01 h10.symm
  rcases h2 with h20 | h2s
  · exact (by decide : (2 : Fin 3) ≠ 0) (T.distinct h20)
  · exact (by decide : (2 : Fin 3) ≠ 1) (T.distinct (h2s.trans h1s.symm))

