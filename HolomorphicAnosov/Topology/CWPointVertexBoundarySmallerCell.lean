import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Strict dimension descent for a CW attaching point

Source: Fritsch–Piccinini, Cellular Structures in Topology, Lemma 2.3.7, p.67.
-/
open _root_.Topology
universe u
namespace HolomorphicAnosov

/-- Source: FP Lemma 2.3.7 p.67, the strict dimension decrease in the preliminary
boundary refinement. The finite open-cell frontier cover puts the boundary image
in a cell of strictly smaller dimension, with its actual interior representative. -/
theorem cw_point_vertex_refinement_boundary_smaller_cell
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X))
    {n : ℕ} (i : @CWComplex.cell X _ Set.univ old n)
    (v : Fin n → ℝ) (hv : v ∈ Metric.sphere 0 1) :
    ∃ m < n, ∃ j : @CWComplex.cell X _ Set.univ old m,
      ∃ b : Fin m → ℝ, ‖b‖ < 1 ∧
        (@CWComplex.map X _ Set.univ old m j) b =
          (@CWComplex.map X _ Set.univ old n i) v := by
  let : CWComplex (Set.univ : Set X) := old
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  have hmem : (@CWComplex.map X _ Set.univ old n i) v ∈
      CWComplex.cellFrontier (C := (Set.univ : Set X)) n i := by
    change (@CWComplex.map X _ Set.univ old n i) v ∈
      (@CWComplex.map X _ Set.univ old n i) '' Metric.sphere 0 1
    exact ⟨v, hv, rfl⟩
  have hboundary := hI hmem
  simp only [Set.mem_iUnion] at hboundary
  obtain ⟨m, hm, j, _, b, hb, hbj⟩ := hboundary
  exact ⟨m, hm, j, b, by simpa only [Metric.mem_ball, dist_zero_right] using hb, hbj⟩


end HolomorphicAnosov
