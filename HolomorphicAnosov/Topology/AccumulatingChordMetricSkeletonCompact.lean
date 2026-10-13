import HolomorphicAnosov.Topology.AccumulatingChordEndpointDistance
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Cofinite

namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- A continuous image of a circle together with the chords associated to a
pairwise disjoint family of open parameter arcs is compact in a proper real
normed space.

Source: Cairns (1951), §3(E)--§4(A), pp.863--864, and de Carvalho,
Definition 4.3/Lemma 4.4, pp.29--30, attached-skeleton null-family argument.
The proof works in any proper real normed space, including the product plane
needed for the graph of the affine boundary map. The base image is compact and
all chords lie in one ball. For closedness, a sequence limiting off the base
eventually lies on chords. Finitely many selected indices give a closed finite
union. Infinitely many indices give a subsequence on distinct chords, whose
distances to their endpoints tend to zero by the null-family estimate. Its
limit lies in the closed base, a contradiction. -/
theorem accumulatingChord_metric_skeleton_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι : Type*} (σ : Circle → E) (hσ : Continuous σ)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j)) :
    IsCompact (range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  classical
  have hbase : IsCompact (range σ) := isCompact_range hσ
  have hbounded : Bornology.IsBounded
      (range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
    obtain ⟨r, hr⟩ := hbase.isBounded.subset_closedBall (0 : E)
    apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
    refine ⟨r, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact hr hz
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact (convex_closedBall (0 : E) r).segment_subset
        (hr ⟨u j, rfl⟩) (hr ⟨v j, rfl⟩) hj
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, hbounded⟩
  have hseg (j : ι) : IsClosed (segment ℝ (σ (u j)) (σ (v j))) := by
    rw [segment_eq_image_lineMap]
    apply (isCompact_Icc.image ?_).isClosed
    change Continuous (fun t : ℝ ↦ t • (σ (v j) - σ (u j)) + σ (u j))
    exact (continuous_id.smul continuous_const).add continuous_const
  apply IsSeqClosed.isClosed
  intro x z hx hz
  by_cases hzb : z ∈ range σ
  · exact Or.inl hzb
  have htail : ∀ᶠ n in atTop, x n ∉ range σ :=
    hz.eventually (hbase.isClosed.isOpen_compl.mem_nhds hzb)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hchord (n : ℕ) : ∃ j, x (n + N) ∈ segment ℝ (σ (u j)) (σ (v j)) :=
    mem_iUnion.mp ((hx (n + N)).resolve_left (hN _ (Nat.le_add_left _ _)))
  choose j hj using hchord
  have hlim : Tendsto (fun n ↦ x (n + N)) atTop (𝓝 z) :=
    hz.comp (tendsto_add_atTop_nat N)
  by_cases hf : (range j).Finite
  · have hc := hf.isClosed_biUnion (fun i _ ↦ hseg i)
    have hm : z ∈ ⋃ i ∈ range j, segment ℝ (σ (u i)) (σ (v i)) :=
      hc.mem_of_tendsto hlim (Eventually.of_forall (fun n ↦
        mem_iUnion.mpr ⟨j n, mem_iUnion.mpr ⟨mem_range_self n, hj n⟩⟩))
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    obtain ⟨_, hzi⟩ := mem_iUnion.mp hi
    exact Or.inr (mem_iUnion.mpr ⟨i, hzi⟩)
  · let e := Set.Infinite.natEmbedding (range j) hf
    have he (n : ℕ) : ∃ k, j k = (e n).val := (e n).property
    choose k hk using he
    have hki : Function.Injective k := by
      intro n m hnm
      apply e.injective
      apply Subtype.ext
      rw [← hk n, ← hk m, hnm]
    have hji : Pairwise fun n m ↦ j (k n) ≠ j (k m) := by
      intro n m hnm heq
      apply hnm
      apply e.injective
      apply Subtype.ext
      simpa only [hk] using heq
    have hend := accumulatingChord_endpoint_distance_tendsto_zero σ hσ arcs u v
      hOpen hConnected hEndpoints hDistinct hArcsDisjoint (fun n ↦ j (k n)) hji
    have hclose : Tendsto (fun n ↦ dist (x (k n + N)) (σ (u (j (k n)))))
        atTop (𝓝 0) := by
      refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hend
      exact Metric.mem_closedBall.mp (segment_subset_closedBall_left _ _ (hj (k n)))
    have hpz := (hlim.comp hki.nat_tendsto_atTop).congr_dist hclose
    exact (hzb (hbase.isClosed.mem_of_tendsto hpz
      (Eventually.of_forall (fun n ↦ ⟨u (j (k n)), rfl⟩)))).elim


end HolomorphicAnosov
