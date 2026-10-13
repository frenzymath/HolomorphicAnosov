import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- Banach fixed-point interface for the graph-transform carrier.

This packages the existence and uniqueness step in HPS, pp.54–56.  The
carrier can be the centered unit-Lipschitz graph family constructed in the
preceding step.  Completeness and nonemptiness are explicit assumptions, while
`hΦ` is the strict contraction estimate; no compactness or finite-dimensionality
of the carrier is used. -/
theorem parameter_graph_fixedPoint
    {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
    (Φ : S → S) (q : NNReal) (hΦ : ContractingWith q Φ) :
    ∃! s, Φ s = s := by
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  obtain ⟨s, hs, _, _⟩ := hΦ.exists_fixedPoint s₀ (edist_ne_top _ _)
  refine ⟨s, hs.eq, ?_⟩
  intro t ht
  exact hΦ.fixedPoint_unique' ht hs



end HolomorphicAnosov
