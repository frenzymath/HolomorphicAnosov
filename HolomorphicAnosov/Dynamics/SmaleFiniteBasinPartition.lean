import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleDisjointBasins

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The stable basins of finitely many disjoint nonempty closed sets partition a compact metric
space whenever every forward orbit approaches one of those sets (Shub, Lemma 2.2). -/
theorem smale_finite_stable_basin_partition
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {b : ℕ} (L : Fin b → Set X) (g : X → X)
    (hLclosed : ∀ i, IsClosed (L i))
    (hLnonempty : ∀ i, (L i).Nonempty)
    (hLdisj : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hcover : ∀ x : X, ∃ i : Fin b,
      Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) (L i)) atTop (𝓝 0)) :
    (⋃ i, {x | Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) (L i))
      atTop (𝓝 0)} = Set.univ) ∧
      Pairwise (fun i j => Disjoint
        {x | Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) (L i)) atTop (𝓝 0)}
        {x | Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) (L j)) atTop (𝓝 0)}) := by
  constructor
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro i j hij
    exact smale_disjoint_infDist_basins g (hLclosed i) (hLclosed j)
      (hLnonempty i) (hLnonempty j) (hLdisj hij)

end HolomorphicAnosov
