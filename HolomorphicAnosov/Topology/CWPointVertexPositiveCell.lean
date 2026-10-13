import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Initial cases for marked-point CW refinement

Source: Fritsch–Piccinini, Cellular Structures in Topology, Lemma 2.3.7, p.67.
-/

open _root_.Topology
universe u
namespace HolomorphicAnosov

/-- If the marked point is not already a zero-cell, the old open-cell cover
places it in a positive-dimensional original cell. This is the first reduction
in Fritsch–Piccinini Lemma 2.3.7, p.67.
Proof: choose its carrier from the open-cell cover. A zero-dimensional carrier
is a singleton, contradicting the hypothesis; its dimension is therefore positive. -/
theorem cw_point_vertex_refinement_positive_cell
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X)) (x : X)
    (hx : ¬ ∃ i : @CWComplex.cell X _ Set.univ old 0,
      (@CWComplex.map X _ Set.univ old 0 i).target = {x}) :
    ∃ n : ℕ, 0 < n ∧ ∃ i : @CWComplex.cell X _ Set.univ old n,
      x ∈ (@CWComplex.map X _ Set.univ old n i) '' Metric.ball 0 1 := by
  let : CWComplex (Set.univ : Set X) := old
  have hcover : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n),
      CWComplex.openCell n i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    exact Set.mem_univ x
  obtain ⟨n, hni⟩ := Set.mem_iUnion.mp hcover
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hni
  by_cases hn : 0 < n
  · exact ⟨n, hn, i, hxi⟩
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hx0 : x = (RelCWComplex.map 0 i) ![] := by
      simpa only [CWComplex.openCell_zero_eq_singleton, Set.mem_singleton_iff] using hxi
    apply False.elim
    apply hx
    refine ⟨i, ?_⟩
    change (RelCWComplex.map 0 i).target = {x}
    rw [← PartialEquiv.image_source_eq_target, RelCWComplex.source_eq]
    change CWComplex.openCell 0 i = {x}
    rw [CWComplex.openCell_zero_eq_singleton, hx0]


end HolomorphicAnosov
