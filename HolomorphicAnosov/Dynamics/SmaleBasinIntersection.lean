import HolomorphicAnosov.Dynamics.SmaleDisjointBasins
import Mathlib.Topology.Homeomorph.Defs

/-! Stable and unstable basin intersections for finite invariant decompositions of the nonwandering
set (Shub, Prop. 9.8). -/

namespace HolomorphicAnosov

open Set Filter
open scoped Topology _root_.Topology

/-- For a finite disjoint closed invariant decomposition of the nonwandering set, each component
equals the intersection of its stable and unstable basins if that intersection consists of
nonwandering points (Shub, Prop. 9.8). -/
theorem smale_basin_intersection_of_nonwandering
    {X : Type*} [MetricSpace X] [CompactSpace X] {b : ℕ}
    (f : X ≃ₜ X) (L : Fin b → Set X)
    (hLclosed : ∀ i, IsClosed (L i))
    (hLnonempty : ∀ i, (L i).Nonempty)
    (hLdisj : Pairwise (fun i j ↦ Disjoint (L i) (L j)))
    (hLmap : ∀ i, f '' L i = L i)
    (hΩ : {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ ((f : X → X)^[k] '' W ∩ W).Nonempty} = ⋃ i, L i) :
    let Ws : Fin b → Set X := fun i ↦
      {x | Tendsto (fun k : ℕ ↦ Metric.infDist ((f : X → X)^[k] x) (L i))
        atTop (𝓝 0)}
    let Wu : Fin b → Set X := fun i ↦
      {x | Tendsto (fun k : ℕ ↦ Metric.infDist ((f.symm : X → X)^[k] x) (L i))
        atTop (𝓝 0)}
    (∀ i, Ws i ∩ Wu i ⊆ {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ ((f : X → X)^[k] '' W ∩ W).Nonempty}) →
    ∀ i, Ws i ∩ Wu i = L i := by
  intro Ws Wu hreturn
  have hforward : ∀ i, MapsTo f (L i) (L i) := by
    intro i x hx
    rw [← hLmap i]
    exact mem_image_of_mem f hx
  have hbackward : ∀ i, MapsTo f.symm (L i) (L i) := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := (hLmap i).symm ▸ hx
    simpa only [f.symm_apply_apply] using hy
  intro i
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hΩ ▸ hreturn i hx)
    by_cases hji : j = i
    · simpa only [hji] using hxj
    · have hxWs : x ∈ Ws j := by
        have hz : (fun k : ℕ ↦ Metric.infDist ((f : X → X)^[k] x) (L j)) =
            fun _ ↦ 0 := funext fun k ↦ Metric.infDist_zero_of_mem
              ((hforward j).iterate k hxj)
        change Tendsto _ atTop (𝓝 0)
        rw [hz]
        exact tendsto_const_nhds
      exact (Set.disjoint_left.mp (smale_disjoint_infDist_basins f
        (hLclosed j) (hLclosed i) (hLnonempty j) (hLnonempty i)
        (hLdisj hji)) hxWs hx.1).elim
  · intro x hx
    constructor
    · have hz : (fun k : ℕ ↦ Metric.infDist ((f : X → X)^[k] x) (L i)) =
          fun _ ↦ 0 := funext fun k ↦ Metric.infDist_zero_of_mem
            ((hforward i).iterate k hx)
      change Tendsto _ atTop (𝓝 0)
      rw [hz]
      exact tendsto_const_nhds
    · have hz : (fun k : ℕ ↦ Metric.infDist ((f.symm : X → X)^[k] x) (L i)) =
          fun _ ↦ 0 := funext fun k ↦ Metric.infDist_zero_of_mem
            ((hbackward i).iterate k hx)
      change Tendsto _ atTop (𝓝 0)
      rw [hz]
      exact tendsto_const_nhds

end HolomorphicAnosov

