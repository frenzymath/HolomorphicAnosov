import Mathlib.Topology.MetricSpace.Bounded

/-!
# Exhaustion from uniformly shrinking boundary sectors

Source: Cairns (1951), §4, corollary to Lemma 4.1, printed p.865.
-/

namespace HolomorphicAnosov.Topology.Plane

open Set

/-- Uniformly shrinking bounded residual pieces attached to a closed excluded boundary
force exhaustion, provided every old frontier point away from that boundary is filled at
the next stage.

Source: Cairns (1951), corollary to Lemma 4.1, p.865. If a point in the region never
enters a stage, it cannot lie on an old frontier: it is outside the excluded boundary and
would then enter the next stage. Thus at every stage it lies in a residual piece. A small
ball about the point misses the closed boundary. At a sufficiently late stage the closure
of its residual piece has diameter less than the radius of this ball, yet contains both
the point and a boundary point, a contradiction. Boundedness is explicit because the real
diameter of an unbounded set is totalized to zero. No nesting assumption is needed. -/
theorem cairns_shrinking_residual_exhaustion
    {E : Type*} [PseudoMetricSpace E] {ι : ℕ → Type*}
    (a B : Set E) (A : ℕ → Set E) (β : ∀ j, ι j → Set E)
    (hA : ∀ j, A j ⊆ a) (hsep : Disjoint a B) (hB : IsClosed B)
    (hcover : ∀ j, a \ closure (A j) ⊆ ⋃ i, β j i)
    (hfrontier : ∀ j, frontier (A j) ⊆ B ∪ A (j + 1))
    (hboundary : ∀ j i, (closure (β j i) ∩ B).Nonempty)
    (hbounded : ∀ j i, Bornology.IsBounded (β j i))
    (hsmall : ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ i : ι j,
      Metric.diam (closure (β j i)) < ε) :
    (⋃ j, A j) = a := by
  apply Subset.antisymm (iUnion_subset hA)
  intro x hx
  by_contra hnot
  have hxA : ∀ j, x ∉ A j := fun j hj ↦ hnot (mem_iUnion.mpr ⟨j, hj⟩)
  have hxB : x ∉ B := fun hxb ↦ Set.disjoint_left.mp hsep hx hxb
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB.isOpen_compl x hxB
  obtain ⟨J, hJ⟩ := hsmall ε hε
  have hxcl : x ∉ closure (A J) := by
    intro hxc
    have hxf : x ∈ frontier (A J) := ⟨hxc, fun hi ↦ hxA J (interior_subset hi)⟩
    exact (hfrontier J hxf).elim hxB (hxA (J + 1))
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover J ⟨hx, hxcl⟩)
  obtain ⟨y, hy, hyB⟩ := hboundary J i
  have hdist : dist y x < ε :=
    lt_of_le_of_lt (Metric.dist_le_diam_of_mem (hbounded J i).closure hy
      (subset_closure hxi)) (hJ J le_rfl i)
  exact hball hdist hyB

end HolomorphicAnosov.Topology.Plane
