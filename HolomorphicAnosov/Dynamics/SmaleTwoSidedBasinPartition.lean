import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromComponents
import HolomorphicAnosov.Dynamics.SmaleNonwanderingInverse
import Mathlib.Topology.Homeomorph.Defs

namespace HolomorphicAnosov

open Set Filter
open scoped Topology _root_.Topology

/-- A finite disjoint nonempty closed invariant decomposition of the nonwandering set gives both
stable and unstable basin partitions of a compact metric space (Shub, Lemma 2.2; Prop. 1.1). -/
theorem smale_two_sided_basin_partition_of_spectral_components
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
    Pairwise (fun i j ↦ Disjoint (Ws i) (Ws j)) ∧ (⋃ i, Ws i) = univ ∧
      Pairwise (fun i j ↦ Disjoint (Wu i) (Wu j)) ∧ (⋃ i, Wu i) = univ := by
  have hforward : ∀ i, MapsTo f (L i) (L i) := by
    intro i x hx
    rw [← hLmap i]
    exact mem_image_of_mem f hx
  have hbackward : ∀ i, MapsTo f.symm (L i) (L i) := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := (hLmap i).symm ▸ hx
    simpa only [f.symm_apply_apply] using hy
  obtain ⟨hscover, hsdisj⟩ := smale_stable_basin_partition_of_spectral_components
    f f.continuous L hLclosed hLnonempty hLdisj hforward hΩ
  have hΩinverse : {z | ∀ W : Set X, IsOpen W → z ∈ W →
      ∃ k : ℕ, 0 < k ∧ ((f.symm : X → X)^[k] '' W ∩ W).Nonempty} = ⋃ i, L i :=
    (smale_nonwandering_inverse f.toEquiv).trans hΩ
  obtain ⟨hucover, hudisj⟩ := smale_stable_basin_partition_of_spectral_components
    f.symm f.symm.continuous L hLclosed hLnonempty hLdisj hbackward hΩinverse
  exact ⟨hsdisj, hscover, hudisj, hucover⟩

end HolomorphicAnosov
