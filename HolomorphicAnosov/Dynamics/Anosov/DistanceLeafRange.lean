import HolomorphicAnosov.Dynamics.Anosov.SourceBoundTransportedPlaqueStages
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped ContDiff Manifold Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov.HPS

universe u

/-- Every leaf of a distance-identified partition is the asymptotic set through
any of its points, with the original ambient metric.

DAG node: `dynamics.distance_leaf_range_g18`.

Source: HPS (1977), §§6B--7 pp.111--116 and the GL8--GL9 distance identification
recorded in `SourceBoundTransportedPlaqueStages`. The marked point is asymptotic
to itself, so the identifying leaf contains it. Disjointness of the partition
identifies this leaf with the given leaf. Substitute the stored range equality,
then convert convergence of extended distance to convergence of finite distance.
This uses no new lamination existence theorem or ambient/intrinsic topology
identification and applies to varying ranks, including rank zero.
-/
theorem DistanceLeafIdentification.range_eq_forwardAsymptotic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    {F : LeafPartition D ι L r}
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞}
    (identification : DistanceLeafIdentification F f edist)
    (i : ι) (a : L i) :
    Set.range (F.leaf i).inclusion =
      {y | ForwardAsymptotic f ((F.leaf i).inclusion a) y} := by
  have ha : (F.leaf i).inclusion a ∈
      Set.range (F.leaf (identification.label ((F.leaf i).inclusion a))).inclusion := by
    rw [identification.equality]
    simp only [Set.mem_ofPred_eq, edist_self]
    exact tendsto_const_nhds
  obtain ⟨b, hb⟩ := ha
  have hi := F.disjoint _ i b a hb
  have hrange := identification.equality ((F.leaf i).inclusion a)
  rw [hi] at hrange
  rw [hrange]
  ext y
  have heq := ENNReal.tendsto_toReal_zero_iff (fi := atTop)
    (f := fun n : ℕ ↦ edist (realIterate 𝓘(ℝ, E) f n y)
      (realIterate 𝓘(ℝ, E) f n ((F.leaf i).inclusion a)))
  change Tendsto (fun n : ℕ ↦ edist (realIterate 𝓘(ℝ, E) f n y)
      (realIterate 𝓘(ℝ, E) f n ((F.leaf i).inclusion a))) atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ ↦ dist (realIterate 𝓘(ℝ, E) f n y)
      (realIterate 𝓘(ℝ, E) f n ((F.leaf i).inclusion a))) atTop (𝓝 0)
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using heq.symm

end HolomorphicAnosov.HPS

