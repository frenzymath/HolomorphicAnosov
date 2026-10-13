import HolomorphicAnosov.Topology.CWComplex.EndpointSubcomplexPackaging
import Mathlib.Topology.UnitInterval

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- Endpoint characteristic-map equations give an original-indexed slice subcomplex.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.2.2,
p.58, specialized to endpoint cells. This is the range-indexed implementation
of that subcomplex step. The product CW structure is explicit supplied data;
this lemma does not construct it.

Proof: the map equation on the closed ball identifies the closed endpoint
image with the original closed-cell image times the endpoint singleton. The
same equation applies to the open ball, which is contained in the closed ball.
The original open cells cover X, so these endpoint open cells cover exactly
X times the singleton. The closed images stay in that slice. Apply
`endpoint_range_subcomplex` with these two verified hypotheses. Empty X,
arbitrary cell cardinalities, and nonregular characteristic boundaries are
allowed; no injectivity of the cell-index map is needed. -/
theorem endpoint_slice_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] [CWComplex (univ : Set (X × unitInterval))]
    (t : unitInterval)
    (endpoint : ∀ n, RelCWComplex.cell (univ : Set X) n →
      RelCWComplex.cell (univ : Set (X × unitInterval)) n)
    (hmap : ∀ n i z, z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 →
      RelCWComplex.map (C := (univ : Set (X × unitInterval))) n (endpoint n i) z =
        (RelCWComplex.map (C := (univ : Set X)) n i z, t)) :
    ∃ A : CWComplex.Subcomplex (univ : Set (X × unitInterval)),
      (A : Set (X × unitInterval)) = univ.prod {t} ∧
      ∀ n, A.I n = range (endpoint n) := by
  apply endpoint_range_subcomplex
    (fun n ↦ RelCWComplex.cell (univ : Set X) n) endpoint (univ.prod {t})
  · intro n i y hy
    rcases hy with ⟨z, hz, rfl⟩
    rw [hmap n i z hz]
    exact ⟨mem_univ _, mem_singleton _⟩
  · ext y
    constructor
    · intro hy
      rcases mem_iUnion.mp hy with ⟨n, hy⟩
      rcases mem_iUnion.mp hy with ⟨i, z, hz, rfl⟩
      rw [hmap n i z (Metric.ball_subset_closedBall hz)]
      exact ⟨mem_univ _, mem_singleton _⟩
    · intro hy
      have hx : y.1 ∈ ⋃ n, ⋃ i : RelCWComplex.cell (univ : Set X) n,
          CWComplex.openCell (C := (univ : Set X)) n i := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        exact mem_univ _
      rcases mem_iUnion.mp hx with ⟨n, hx⟩
      rcases mem_iUnion.mp hx with ⟨i, z, hz, heq⟩
      refine mem_iUnion_of_mem n (mem_iUnion_of_mem i ⟨z, hz, ?_⟩)
      rw [hmap n i z (Metric.ball_subset_closedBall hz)]
      exact Prod.ext heq (mem_singleton_iff.mp hy.2).symm

end HolomorphicAnosov.Topology

