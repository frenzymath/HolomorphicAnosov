import Mathlib.Topology.MetricSpace.Lipschitz

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Proposition29Length

/-- A connected compact nontrivial extended metric space admits no surjective Lipschitz self-map
with Lipschitz constant less than one. (Zhang, Prop. 2.9) -/
theorem no_surjective_strict_contraction
    {X : Type*} [EMetricSpace X] [CompactSpace X] [ConnectedSpace X] [Nontrivial X]
    (g : X → X) (hg : Function.Surjective g) (q : NNReal) (hq : q < 1)
    (hlip : LipschitzWith q g) : False := by
  have hfinite : ∀ x y : X, edist x y ≠ ⊤ := by
    intro x y
    have hc : IsClopen (Metric.eball x ⊤) :=
      ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
    have hx : x ∈ Metric.eball x ⊤ := by simp
    have hy : y ∈ connectedComponent x := by
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      trivial
    have hyball := hc.connectedComponent_subset hx hy
    exact (show edist y x < ⊤ from hyball).ne |> fun h ↦ by
      simpa only [edist_comm] using h
  let : MetricSpace X := EMetricSpace.toMetricSpace hfinite
  have hbounded : Bornology.IsBounded (Set.univ : Set X) := isCompact_univ.isBounded
  have hpositive : 0 < Metric.diam (Set.univ : Set X) :=
    Metric.diam_pos Set.nontrivial_univ hbounded
  have hdiam := hlip.diam_image_le Set.univ hbounded
  rw [Set.image_univ, hg.range_eq] at hdiam
  have hq' : (q : ℝ) < 1 := hq
  nlinarith


end HolomorphicAnosov.Proposition29Length
