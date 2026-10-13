import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- If an orbit eventually lies in smaller neighborhoods mapped into pairwise disjoint larger
neighborhoods, it eventually stays in one smaller neighborhood (Shub, Lemma 2.2). -/
theorem smale_eventually_one_component
    {X ι : Type*} (g : X → X) (x : X) (U V : ι → Set X)
    (hUV : ∀ i, U i ⊆ V i)
    (hmap : ∀ i, MapsTo g (U i) (V i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (htail : ∀ᶠ n : ℕ in atTop, g^[n] x ∈ ⋃ i, U i) :
    ∃ i, ∀ᶠ n : ℕ in atTop, g^[n] x ∈ U i := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hN N le_rfl)
  have hstay : ∀ n, N ≤ n → g^[n] x ∈ U i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hi
    | succ n hn ih =>
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hN (n + 1) (by omega))
        have hnext : g^[n + 1] x ∈ V i := by
          simpa only [Function.iterate_succ_apply'] using hmap i ih
        have hji : j = i := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne) (hUV j hj) hnext
        simpa only [hji] using hj
  exact ⟨i, eventually_atTop.mpr ⟨N, hstay⟩⟩

end HolomorphicAnosov
