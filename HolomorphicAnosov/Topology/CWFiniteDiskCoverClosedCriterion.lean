import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Preserving the CW closed-set criterion through finite characteristic covers

Source: Fritsch–Piccinini, Cellular Structures in Topology, Proposition 1.2.2,
pp.23–24, and the cellular adjunction topology argument in Theorem 2.3.1,
pp.62–63. The theorem below is an agent-written realization of the closed-image argument
for finite cell replacements in
Lemma 2.3.7, p.67, on the original ambient topology.
-/

open Set _root_.Topology

namespace HolomorphicAnosov

/-- Suppose each original closed cell of a Hausdorff CW complex is a finite
union of images of continuous characteristic disks. Closed inverse images under
those disks imply that a set is closed in the original ambient topology.

Source context: the characteristic closed-set criterion of Fritsch–Piccinini
Proposition 1.2.2, pp.23–24, and its finite replacement application in the
cellular adjunction construction, Theorem 2.3.1, pp.62–63.

This exact finite-family coordinate formulation is agent-written.
Proof: intersect a disk with the inverse image of the set. It is a closed
subset of a compact disk, so its continuous image is compact and hence closed
in the Hausdorff ambient space. This image is exactly the intersection of the
set with the characteristic image. Each old closed-cell intersection is then
a finite union of these closed intersections. The original CW closed-set test
makes the set closed. The characteristic family can be infinite; only its
cover of each individual old closed cell must be finite. -/
theorem cw_closed_of_finite_characteristic_cover
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)]
    {J : Type*} (dim : J → ℕ)
    (newMap : (j : J) → (Fin (dim j) → ℝ) → X)
    (hcont : ∀ j, ContinuousOn (newMap j)
      (Metric.closedBall (0 : Fin (dim j) → ℝ) 1))
    (hcover : ∀ (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m),
      ∃ F : Finset J, CWComplex.closedCell m i =
        ⋃ j ∈ F, newMap j '' Metric.closedBall (0 : Fin (dim j) → ℝ) 1)
    (B : Set X)
    (hpre : ∀ j, IsClosed
      (Metric.closedBall (0 : Fin (dim j) → ℝ) 1 ∩ newMap j ⁻¹' B)) :
    IsClosed B := by
  apply (CWComplex.closed (univ : Set X) B (subset_univ B)).2
  intro m i
  obtain ⟨F, hF⟩ := hcover m i
  rw [hF]
  simp_rw [inter_iUnion]
  change IsClosed (⋃ j ∈ (↑F : Set J),
    B ∩ newMap j '' Metric.closedBall (0 : Fin (dim j) → ℝ) 1)
  rw [Set.biUnion_eq_iUnion]
  apply isClosed_iUnion_of_finite
  intro j
  have hcompact : IsCompact
      (Metric.closedBall (0 : Fin (dim j) → ℝ) 1 ∩ newMap j ⁻¹' B) :=
    (isCompact_closedBall _ _).of_isClosed_subset (hpre j) inter_subset_left
  have himage : newMap j ''
      (Metric.closedBall (0 : Fin (dim j) → ℝ) 1 ∩ newMap j ⁻¹' B) =
      B ∩ newMap j '' Metric.closedBall (0 : Fin (dim j) → ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨v, ⟨hv, hvB⟩, rfl⟩
      exact ⟨hvB, ⟨v, hv, rfl⟩⟩
    · rintro ⟨hyB, v, hv, rfl⟩
      exact ⟨v, ⟨hv, hyB⟩, rfl⟩
  rw [← himage]
  exact (hcompact.image_of_continuousOn
    ((hcont j).mono inter_subset_left)).isClosed

end HolomorphicAnosov
