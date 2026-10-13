import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleOrbitEventuallyNearNonwandering
import HolomorphicAnosov.Dynamics.SmaleFiniteBasinPartition
import HolomorphicAnosov.Dynamics.SmaleOrbitComponentCapture
import HolomorphicAnosov.Dynamics.SmaleBasinFromNeighborhood

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- Separated neighborhoods covering the nonwandering set, with the stated mapping and closure
conditions, give a stable basin partition for finitely many disjoint nonempty closed components
(Shub, Lemma 2.2). -/
theorem smale_stable_basin_partition_of_neighborhoods
    {X : Type*} [MetricSpace X] [CompactSpace X] {b : ℕ}
    (g : X → X) (L U V : Fin b → Set X)
    (hLclosed : ∀ i, IsClosed (L i))
    (hLnonempty : ∀ i, (L i).Nonempty)
    (hLdisj : Pairwise (fun i j ↦ Disjoint (L i) (L j)))
    (hUopen : IsOpen (⋃ i, U i))
    (hΩU : {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' W ∩ W).Nonempty} ⊆ ⋃ i, U i)
    (hUV : ∀ i, U i ⊆ V i)
    (hmap : ∀ i, MapsTo g (U i) (V i))
    (hVdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hguard : ∀ i, {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' W ∩ W).Nonempty} ∩ closure (U i) ⊆ L i) :
    (⋃ i, {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L i))
      atTop (𝓝 0)} = univ) ∧
      Pairwise (fun i j ↦ Disjoint
        {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L i)) atTop (𝓝 0)}
        {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L j)) atTop (𝓝 0)}) := by
  apply smale_finite_stable_basin_partition L g hLclosed hLnonempty hLdisj
  intro x
  have htail := smale_eventually_mem_of_nonwandering_subset g x hUopen hΩU
  obtain ⟨i, hi⟩ := smale_eventually_one_component g x U V hUV hmap hVdisj htail
  exact ⟨i, smale_basin_of_eventually_mem_neighborhood g x (L i) (U i)
    (hguard i) hi⟩

end HolomorphicAnosov
