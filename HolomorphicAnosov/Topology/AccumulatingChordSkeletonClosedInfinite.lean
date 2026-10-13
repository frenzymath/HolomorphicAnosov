import HolomorphicAnosov.Topology.AccumulatingChordDistinctIndexLimit
import HolomorphicAnosov.Topology.AccumulatingChordRecurringLimit
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Cofinite

namespace HolomorphicAnosov
open Set
open Filter
open scoped Topology _root_.Topology

/--
The genuinely countable branch of the attached-chord closedness argument.
Cairns §3(E)-§4(A) and de Carvalho Definition 4.3/Lemma 4.4 reduce this
branch to the null-family endpoint estimate: pairwise disjoint proper source
arcs have only finitely many members above every positive normalized length,
so a sequence on distinct chords has endpoint distance tending to zero and
its limit lies on the embedded base circle. The recurring-index case is the
closedness of one affine segment. This theorem isolates that countable null
family from the finite compact-image branch.
-/
theorem accumulatingChordSkeleton_closed_of_infinite
    {ι : Type*} [Countable ι] [Infinite ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (hProper : ∀ i, arcs i ≠ Set.univ)
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j)))) :
    IsClosed (Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))) := by
  classical
  have hbase : IsClosed (Set.range σ) := (isCompact_range hσ.continuous).isClosed
  have hseg (i : ι) : IsClosed (segment ℝ (σ (u i)) (σ (v i))) := by
    apply IsSeqClosed.isClosed
    intro x z hx hz
    exact accumulatingChordSkeleton_recurring_index_limit _ _ x z hx hz
  apply IsSeqClosed.isClosed
  intro x z hx hz
  by_cases hzb : z ∈ Set.range σ
  · exact Or.inl hzb
  have htail : ∀ᶠ n in atTop, x n ∉ Set.range σ :=
    hz.eventually (hbase.isOpen_compl.mem_nhds hzb)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hchord (n : ℕ) : ∃ i, x (n + N) ∈ segment ℝ (σ (u i)) (σ (v i)) :=
    mem_iUnion.mp ((hx (n + N)).resolve_left (hN _ (Nat.le_add_left _ _)))
  choose j hj using hchord
  have hlim : Tendsto (fun n ↦ x (n + N)) atTop (𝓝 z) :=
    hz.comp (tendsto_add_atTop_nat N)
  by_cases hf : (Set.range j).Finite
  · have hc := hf.isClosed_biUnion (fun i _ ↦ hseg i)
    have hm : z ∈ ⋃ i ∈ Set.range j, segment ℝ (σ (u i)) (σ (v i)) :=
      hc.mem_of_tendsto hlim (Eventually.of_forall (fun n ↦
        mem_iUnion.mpr ⟨j n, mem_iUnion.mpr ⟨mem_range_self n, hj n⟩⟩))
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    obtain ⟨_, hzi⟩ := mem_iUnion.mp hi
    exact Or.inr (mem_iUnion.mpr ⟨i, hzi⟩)
  · let e := Set.Infinite.natEmbedding (Set.range j) hf
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
    have hzb' := accumulatingChordSkeleton_distinct_index_limit σ hσ h arcs u v
      hOpen hConnected hProper hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint
      (fun n ↦ j (k n)) (fun n ↦ x (k n + N)) z hji (fun n ↦ hj (k n))
      (hlim.comp hki.nat_tendsto_atTop)
    exact (hzb hzb').elim


end HolomorphicAnosov
