import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- An orbit approaching one member of a finite disjoint family of nonempty closed sets in a compact
metric space eventually stays a positive distance from every other member (Shub, Lemma 2.2). -/
theorem smale_capture_other_component_astra
    {X : Type*} [MetricSpace X] [CompactSpace X] {b : ℕ}
    (L : Fin b → Set X) (g : X → X)
    (hLclosed : ∀ i, IsClosed (L i))
    (hLnonempty : ∀ i, (L i).Nonempty)
    (hLdisj : Pairwise (fun i j => Disjoint (L i) (L j)))
    (x : X) (i : Fin b)
    (hi : Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) (L i)) atTop (𝓝 0)) :
    ∀ j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k : ℕ in atTop, δ < Metric.infDist (g^[k] x) (L j) := by
  intro j hij
  have hcompact : IsCompact (L i) := (hLclosed i).isCompact
  obtain ⟨a, ha, hamin⟩ := hcompact.exists_isMinOn (hLnonempty i)
    (Metric.continuous_infDist_pt (L j)).continuousOn
  have ha_not_mem : a ∉ L j := by
    intro haj
    exact Set.disjoint_left.mp (hLdisj hij) ha haj
  have ha_not_closure : a ∉ closure (L j) := by
    rw [(hLclosed j).closure_eq]
    exact ha_not_mem
  have hgap : 0 < Metric.infDist a (L j) :=
    (Metric.infDist_pos_iff_notMem_closure (x := a) (hLnonempty j)).1
      ha_not_closure
  refine ⟨Metric.infDist a (L j) / 2, half_pos hgap, ?_⟩
  have hsmall : ∀ᶠ k : ℕ in atTop,
      Metric.infDist (g^[k] x) (L i) < Metric.infDist a (L j) / 2 :=
    hi.eventually (Iio_mem_nhds (half_pos hgap))
  filter_upwards [hsmall] with k hk
  obtain ⟨y, hy, hymin⟩ := hcompact.exists_infDist_eq_dist (hLnonempty i)
    (g^[k] x)
  have hya : dist y (g^[k] x) < Metric.infDist a (L j) / 2 := by
    calc
      dist y (g^[k] x) = dist (g^[k] x) y := dist_comm _ _
      _ = Metric.infDist (g^[k] x) (L i) := hymin.symm
      _ < Metric.infDist a (L j) / 2 := hk
  have hle := Metric.infDist_le_infDist_add_dist (x := y) (y := g^[k] x)
    (s := L j)
  have hbase : Metric.infDist a (L j) ≤ Metric.infDist y (L j) := hamin hy
  have htri : Metric.infDist y (L j) ≤
      Metric.infDist (g^[k] x) (L j) + dist y (g^[k] x) := hle
  linarith

end HolomorphicAnosov
