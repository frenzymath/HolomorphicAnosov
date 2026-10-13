import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# Cancellation of shared square-grid sides

Source: Conway, Functions of One Complex Variable, second edition (1978),
VIII Proposition 1.1, p.196, equation (1.2). Oppositely oriented shared sides
cancel, leaving precisely the sides incident to one selected rectangle.
DAG node: `analysis.finite_grid_boundary_cancellation_g19`.
-/

open scoped BigOperators
namespace HolomorphicAnosov.Analysis.Complex

/-- Sum the counterclockwise boundaries of finitely many grid cells. Horizontal
weights point right, vertical weights point up. Every shared weight cancels;
the four remaining sums are the bottom, top, right and left exposed sides.

Source: Conway VIII.1.1, p.196, equation (1.2). For a lattice direction d,
partition cells into those with and without the neighbor in that direction.
Translation by d bijects the two lists of occurrences of a shared edge, with
equal weights and opposite signs. Cancel those sums. Apply this to the vertical
neighbor for horizontal weights and the horizontal neighbor for vertical weights.
The argument is purely additive and therefore works in any abelian group,
including complex contour integrals. Empty cell sets need no special case. -/
theorem finite_grid_boundary_cancellation {A : Type*} [AddCommGroup A]
    (S : Finset (ℤ × ℤ)) (H V : (ℤ × ℤ) → A) :
    (∑ q ∈ S, (H q + V (q + (1, 0)) - H (q + (0, 1)) - V q)) =
      (∑ q ∈ S.filter (fun q ↦ q - (0, 1) ∉ S), H q) -
      (∑ q ∈ S.filter (fun q ↦ q + (0, 1) ∉ S), H (q + (0, 1))) +
      (∑ q ∈ S.filter (fun q ↦ q + (1, 0) ∉ S), V (q + (1, 0))) -
      (∑ q ∈ S.filter (fun q ↦ q - (1, 0) ∉ S), V q) := by
  have hshift (d : ℤ × ℤ) (F : (ℤ × ℤ) → A) :
      (∑ q ∈ S, F q) - (∑ q ∈ S, F (q + d)) =
      (∑ q ∈ S.filter (fun q ↦ q - d ∉ S), F q) -
      (∑ q ∈ S.filter (fun q ↦ q + d ∉ S), F (q + d)) := by
    have hcommon : (∑ q ∈ S.filter (fun q ↦ q - d ∈ S), F q) =
        ∑ q ∈ S.filter (fun q ↦ q + d ∈ S), F (q + d) := by
      apply Finset.sum_bij (fun q _ ↦ q - d)
      · intro q hq
        obtain ⟨hq, hprev⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hprev, by simpa using hq⟩
      · intro q hq r hr heq
        simpa using congrArg (fun x ↦ x + d) heq
      · intro q hq
        obtain ⟨hq, hnext⟩ := Finset.mem_filter.mp hq
        exact ⟨q + d, Finset.mem_filter.mpr ⟨hnext, by simpa using hq⟩, by simp⟩
      · intro q hq
        simp
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q ↦ q - d ∈ S) F,
      ← Finset.sum_filter_add_sum_filter_not S (fun q ↦ q + d ∈ S) (fun q ↦ F (q + d)),
      hcommon]
    abel
  calc
    _ = ((∑ q ∈ S, H q) - (∑ q ∈ S, H (q + (0, 1)))) -
        ((∑ q ∈ S, V q) - (∑ q ∈ S, V (q + (1, 0)))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      abel
    _ = _ := by rw [hshift, hshift]; abel

end HolomorphicAnosov.Analysis.Complex
