import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Dynamics.PeriodicPts.Defs

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The basins defined by convergence of orbit infimum distance to two disjoint nonempty closed sets
in a compact metric space are disjoint (Shub, Lemma 2.2). -/
theorem smale_disjoint_infDist_basins {X : Type*} [MetricSpace X] [CompactSpace X]
    (g : X → X) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hAB : Disjoint A B) :
    Disjoint
      {x | Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) A) atTop (𝓝 0)}
      {x | Tendsto (fun k : ℕ => Metric.infDist (g^[k] x) B) atTop (𝓝 0)} := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨z, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq (fun k : ℕ => g^[k] x)
  have hAz : Metric.infDist z A = 0 :=
    tendsto_nhds_unique ((Metric.continuous_infDist_pt (s := A)).continuousAt.tendsto.comp hz)
      (hxA.comp hφ.tendsto_atTop)
  have hBz : Metric.infDist z B = 0 :=
    tendsto_nhds_unique ((Metric.continuous_infDist_pt (s := B)).continuousAt.tendsto.comp hz)
      (hxB.comp hφ.tendsto_atTop)
  exact Set.disjoint_left.mp hAB ((hA.mem_iff_infDist_zero hAn).mpr hAz)
    ((hB.mem_iff_infDist_zero hBn).mpr hBz)

end HolomorphicAnosov
