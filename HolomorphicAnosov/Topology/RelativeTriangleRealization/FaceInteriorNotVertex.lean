import HolomorphicAnosov.Topology.RelativeTriangleRealization.FaceBoundaryVertex

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

open Convexity

/-- An interior point of an ordered triangle face is not a triangle vertex.

This is the cross-stratum disjointness fact needed when packaging the open edge
cells and zero-cells with `finiteClassicalCWOfDisks`. -/
theorem face_interior_ne_vertex {j : Fin 3} {t : Simplex 1}
    (ht : t ∈ interior 1) (v : Fin 3) : face j t ≠ Convexity.StdSimplex.single v := by
  intro hface
  have hz : (face j t).weights j = 0 := by
    change t.weights.mapDomain j.succAbove j = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact j.succAbove_ne a ha
  have hvne : v ≠ j := by
    intro hvj
    have hh := congrArg (fun z : Simplex 2 => z.weights j) hface
    rw [hz] at hh
    simp [hvj] at hh
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hvne
  fin_cases k
  · have hh := congrArg (fun z : Simplex 2 => z.weights (j.succAbove 1)) hface
    have hp := ht 1
    rw [← hk] at hh
    change t.weights.mapDomain j.succAbove _ = _ at hh
    rw [Finsupp.mapDomain_apply_of_injective j.succAbove_right_injective] at hh
    simp at hh
    linarith
  · have hh := congrArg (fun z : Simplex 2 => z.weights (j.succAbove 0)) hface
    have hp := ht 0
    rw [← hk] at hh
    change t.weights.mapDomain j.succAbove _ = _ at hh
    rw [Finsupp.mapDomain_apply_of_injective j.succAbove_right_injective] at hh
    simp at hh
    linarith


end HolomorphicAnosov.RelativeTriangleRealization
