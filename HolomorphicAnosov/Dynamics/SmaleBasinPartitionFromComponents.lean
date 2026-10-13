import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs
import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromNeighborhoods

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The stable basins of a finite disjoint nonempty closed invariant decomposition of the
nonwandering set partition a compact metric space (Shub, Lemma 2.2). -/
theorem smale_stable_basin_partition_of_spectral_components
    {X : Type*} [MetricSpace X] [CompactSpace X] {b : ℕ}
    (g : X → X) (hg : Continuous g) (L : Fin b → Set X)
    (hLclosed : ∀ i, IsClosed (L i))
    (hLnonempty : ∀ i, (L i).Nonempty)
    (hLdisj : Pairwise (fun i j ↦ Disjoint (L i) (L j)))
    (hLmap : ∀ i, MapsTo g (L i) (L i))
    (hΩ : {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ (g^[k] '' W ∩ W).Nonempty} = ⋃ i, L i) :
    (⋃ i, {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L i))
      atTop (𝓝 0)} = univ) ∧
      Pairwise (fun i j ↦ Disjoint
        {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L i)) atTop (𝓝 0)}
        {x | Tendsto (fun k : ℕ ↦ Metric.infDist (g^[k] x) (L j)) atTop (𝓝 0)}) := by
  let V : Fin b → Set X := fun i ↦
    {x | ∀ j, j ≠ i → Metric.infDist x (L i) < Metric.infDist x (L j)}
  have hVopen : ∀ i, IsOpen (V i) := by
    intro i
    dsimp only [V]
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt (Metric.continuous_infDist_pt _) (Metric.continuous_infDist_pt _)
  have hLV : ∀ i, L i ⊆ V i := by
    intro i x hx j hji
    rw [Metric.infDist_zero_of_mem hx]
    apply (hLclosed j).notMem_iff_infDist_pos (hLnonempty j) |>.mp
    intro hxj
    exact Set.disjoint_left.mp (hLdisj hji) hxj hx
  have hVdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact (hxi j hij.symm).asymm (hxj i hij)
  let U : Fin b → Set X := fun i ↦ V i ∩ g ⁻¹' V i
  have hLU : ∀ i, L i ⊆ U i := by
    intro i x hx
    exact ⟨hLV i hx, hLV i (hLmap i hx)⟩
  apply smale_stable_basin_partition_of_neighborhoods g L U V
    hLclosed hLnonempty hLdisj
  · exact isOpen_iUnion fun i ↦ (hVopen i).inter ((hVopen i).preimage hg)
  · rw [hΩ]
    exact iUnion_mono hLU
  · intro i
    exact inter_subset_left
  · intro i x hx
    exact hx.2
  · exact hVdisj
  · intro i x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hΩ ▸ hx.1)
    by_cases hji : j = i
    · simpa only [hji] using hxj
    · have hcl : closure (U i) ⊆
          {z | Metric.infDist z (L i) ≤ Metric.infDist z (L j)} := by
        apply closure_minimal
        · intro z hz
          exact (hz.1 j hji).le
        · exact isClosed_le (Metric.continuous_infDist_pt _)
            (Metric.continuous_infDist_pt _)
      have hzero : Metric.infDist x (L i) = 0 := by
        apply le_antisymm _ Metric.infDist_nonneg
        simpa only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hxj] using hcl hx.2
      exact (hLclosed i).mem_iff_infDist_zero (hLnonempty i) |>.mpr hzero

end HolomorphicAnosov
