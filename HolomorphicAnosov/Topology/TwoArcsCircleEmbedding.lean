import HolomorphicAnosov.Topology.IntervalLoopCircleEmbedding
import Mathlib.Topology.Path

/-! # Two arcs meeting only at their endpoints form an embedded circle

Source: Whyburn, *Topological Analysis*, II §5, printed p.28 (exercise).
The proof explicitly concatenates the first arc with the reverse of the second,
then uses the endpoint quotient of the unit interval.
-/
namespace HolomorphicAnosov
open Set

/-- Two injective continuous arcs with common endpoints and no other intersections
parametrize an embedded circle whose range is their union.

Source: Whyburn, *Topological Analysis*, II §5, p.28 (exercise); this is an
agent-written solution. Concatenate the first arc with the reversed second arc.
On each half-interval injectivity follows from that of the corresponding arc.
Across the two halves the intersection condition forces a common endpoint;
the excluded terminal parameter removes the duplicated initial endpoint.
The interval-loop quotient theorem therefore supplies the circle embedding. -/
theorem twoArcs_circle_embedding {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : unitInterval → X) (hA : Continuous A) (hB : Continuous B)
    (hiA : Function.Injective A) (hiB : Function.Injective B)
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hcross : ∀ s t, A s = B t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ j : Circle → X, _root_.Topology.IsEmbedding j ∧ range j = range A ∪ range B := by
  let a : Path (A 0) (A 1) := ⟨⟨A, hA⟩, rfl, rfl⟩
  let b : Path (A 0) (A 1) := ⟨⟨B, hB⟩, h0.symm, h1.symm⟩
  let p := a.trans b.symm
  have hinj : InjOn p.extend (Ico 0 1) := by
    intro s hs t ht heq
    have left (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) (hh : r ≤ 1 / 2) :
        p.extend r = A ⟨2 * r, by constructor <;> linarith [hr.1]⟩ := by
      rw [Path.extend_trans_of_le_half a b.symm hh, Path.extend_apply]
      rfl
    have right (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) (hh : ¬r ≤ 1 / 2) :
        p.extend r = B ⟨2 - 2 * r, by constructor <;> linarith [hr.1, hr.2]⟩ := by
      rw [Path.extend_trans_of_half_le a b.symm (by linarith), Path.extend_symm_apply]
      have he : 1 - (2 * r - 1) = 2 - 2 * r := by ring
      rw [he, Path.extend_apply]
      rfl
    by_cases hs' : s ≤ 1 / 2 <;> by_cases ht' : t ≤ 1 / 2
    · rw [left s hs hs', left t ht ht'] at heq
      have := congrArg Subtype.val (hiA heq)
      dsimp at this
      linarith
    · rw [left s hs hs', right t ht ht'] at heq
      rcases hcross _ _ heq with h | h
      · have := congrArg Subtype.val h.2
        dsimp at this
        linarith [ht.2]
      · have := congrArg Subtype.val h.2
        dsimp at this
        linarith
    · rw [right s hs hs', left t ht ht'] at heq
      rcases hcross _ _ heq.symm with h | h
      · have := congrArg Subtype.val h.2
        dsimp at this
        linarith [hs.2]
      · have := congrArg Subtype.val h.2
        dsimp at this
        linarith
    · rw [right s hs hs', right t ht ht'] at heq
      have := congrArg Subtype.val (hiB heq)
      dsimp at this
      linarith
  obtain ⟨j, hj, hr⟩ := Topology.intervalLoop_circle_embedding p.extend
    p.continuous_extend.continuousOn (by simp) hinj
  refine ⟨j, hj, hr.trans ?_⟩
  rw [Path.image_extend_of_subset p Subset.rfl, Path.trans_range, Path.symm_range]
  rfl

end HolomorphicAnosov
